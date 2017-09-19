(ns com.meansemerge.cryptography.probabilistic
  (:import (java.util Random)
           (java.security SecureRandom)))

(def big biginteger)

(def two (big 2))

(defn pow-mod [base exp m]
  (.modPow (big base) (big exp) (big m)))

(defn x2%m [m x]
  (pow-mod x two m))

(def qr x2%m)

(defn qrs [m x]
  (let [qr (partial qr m)]
    (iterate qr (qr x))))

(defn =3mod4? [x]
  (= 3 (mod x 4)))

(defn blum-primes [length random]
  (->> #(BigInteger/probablePrime length random)
       repeatedly
       (filter =3mod4?)))

(defn bit-count [x]
  (.bitLength (big x)))

(defn blum-int
  ([length] (blum-int length (SecureRandom.)))
  ([length random]
   (when (or (odd? length)
             (< length 10))
     (throw (ex-info "modulus length should be an even number, at least 10"
                     {::modulus-length length})))
   (let [candidates
         (->> (blum-primes (quot length 2) random)
              dedupe
              (partition 2 1)
              (map (fn [pair]
                     {::modulus (apply * pair)
                      ::primes  (vec (sort pair))}))
              (filter #(= length (bit-count (::modulus %)))))]
     (first candidates))))

(defn secure-bit-count [m]
  (bit-count (bit-count m)))

(defn low-bit-seq [x low-bit-count]
  (let [bx (big x)]
    (for [i (range (dec low-bit-count) -1 -1)]
      (.testBit bx i))))

(defn bit-seq->byte [bit-seq]
  (->> bit-seq
       (map vector (range 7 -1 -1))
       (filter second)
       (map first)
       (reduce #(bit-set %1 %2) 0)))

(defn simple-bytes-from-low-bits [low-bit-count]
  (comp (mapcat #(low-bit-seq % low-bit-count))
        (partition-all 8)
        (map bit-seq->byte)))

(defn mask-from [low-bit-count]
  (reduce #(bit-set %1 %2) 0 (range low-bit-count)))

(defn bytes-from-low-bits [low-bit-count]
  (fn [rf]
    (let [pending-bits (volatile! {::bits 0 ::bit-count 0})
          low-bit-mask (mask-from low-bit-count)]
      (fn
        ([] (rf))
        ([result] (rf result))
        ([result x]
         (let [{:keys [::bits ::bit-count]} @pending-bits
               bits (bit-or (bit-shift-left bits low-bit-count)
                            (bit-and (unchecked-int x)
                                     low-bit-mask))
               bit-count (+ bit-count low-bit-count)
               out-bytes (for [shift (range (- bit-count 8)
                                            -1 -8)]
                           (unchecked-byte (bit-shift-right bits shift)))]
           (vreset! pending-bits {::bits      bits
                                  ::bit-count (mod bit-count 8)})
           (transduce (map (fn [b] {::source x ::byte b}))
                      rf result out-bytes)))))))

(defn bbs [m seed]
  (->> (qrs m seed)
       (sequence (bytes-from-low-bits (secure-bit-count m)))))

(def map-byte (map ::byte))

(defn byte-seq->Random [byte-seq]
  (let [next-bytes (atom byte-seq)]
    (proxy [Random] []
      (next [number-of-bits]
        (let [byte-count (long (Math/ceil (/ number-of-bits 8)))
              [bytes-out rest-bytes] (split-at byte-count @next-bytes)]
          (reset! next-bytes rest-bytes)
          (int (BigInteger. (byte-array bytes-out))))))))

(defn bbs-seq->Random [bbs-seq]
  (->> bbs-seq
       (sequence map-byte)
       byte-seq->Random))

(defn phi [{m     ::modulus
            [p q] ::primes}]
  (* (dec p) (dec q)))

(defn inverting-exponent [m+factors]
  (/ (+ 4 (phi m+factors))
     8))

(defn qr-offset [m+factors r offset]
  (let [exponent
        (-> (if (not (neg? offset))
              two
              (inverting-exponent m+factors))
            (pow-mod (.abs (big offset))
                     (phi m+factors)))]
    (pow-mod r exponent (::modulus m+factors))))

(defn factor-via-congruent-squares [m roots-of-r & [check-roots?]]
  (let [[x y] roots-of-r]
    (when check-roots?
      (let [qr (partial qr m)]
        (when (not= (qr x) (qr y))
          (throw (ex-info "Not roots of the same residue!" {x (qr x) y (qr y)})))))
    (if (distinct? x y (- m y))
      (let [factor-multiples [(mod (+ x y) m)
                              (mod (- x y) m)]
            factors (-> (map #(.gcd (big m) (big %))
                             factor-multiples)
                        distinct sort vec)]
        (let [factor? #(zero? (mod m %))]
          (when (not-every? factor? factors)
            #_"Sanity check failed. Indicates flaw in my understanding."
            (throw (ex-info "Found non-factors?" {:factors factors}))))
        (if (= 1 (first factors))
          ::factors-are-trivial
          factors))
      ::roots-are-twins)))

(defn factor-by-quadratic-roots [m quadratic-root-fn]
  (let [random (Random. 0)
        root-pairs (->> (repeatedly #(new BigInteger (bit-count m) random))
                        (map (fn [x] [x (quadratic-root-fn (qr m x))])))]
    (->> root-pairs
         (map #(factor-via-congruent-squares m % true))
         (remove #{::roots-are-twins ::factors-are-trivial})
         first)))

(defn chunks-of-50 [n]
  (map (partial apply str)
       (partition-all 50 (str n))))
