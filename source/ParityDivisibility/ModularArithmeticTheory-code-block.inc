.. code-block::

   import Mathlib.Tactic.Ring
   import Mathlib.Tactic.Use
   import LeanSource.Division

.. _theory_modular:

Modular arithmetic: theory
--------------------------

.. admonition:: Definition

  The integers :math:`a` and :math:`b` are *congruent modulo* :math:`n`, if :math:`n\mid (a - b)`.

We use the notation :math:`a\equiv b \mod n` to denote that :math:`a` and :math:`b` are congruent
modulo :math:`n`.

.. code-block::

   def int.modeq (n a b : ℤ) := n ∣ (a - b)

   notation:50 a " ≡ " b " [ZMOD " n "]" => int.modeq n a b

Example
^^^^^^^

.. admonition:: Problem

  Show that :math:`11\equiv 3 \mod 4`.

.. admonition:: Solution

  :math:`11-3=4\cdot 2`, so :math:`4\mid(11-3)`.

.. code-block::

    example : 11 ≡ 3 [ZMOD 4] := by
      use 2

Example
^^^^^^^

.. admonition:: Problem

  Show that :math:`-5\equiv 1 \mod 3`.

.. admonition:: Solution

  :math:`-5-1=3\cdot -2`, so :math:`3\mid(-5-1)`.

.. code-block::

    example : -5 ≡ 1 [ZMOD 3] :=
      sorry

Example
^^^^^^^

.. admonition:: Lemma (addition rule for modular arithmetic)

  Let :math:`a`, :math:`b`, :math:`c`, :math:`d` and :math:`n` be integers, and suppose that
  :math:`a\equiv b \mod n` and :math:`c\equiv d \mod n`.  Then :math:`a+c\equiv b+d \mod n`.

.. admonition:: Proof

  Since :math:`a\equiv b \mod n`, there exists an integer :math:`x` such that :math:`a-b=nx`.
  Since :math:`c\equiv d \mod n`, there exists an integer :math:`y` such that :math:`c-d=ny`.
  Then

  .. math::

    a + c - (b + d) &= (a - b) + (c - d) \\
    &= n x + n y \\
    &= n (x + y),

  so :math:`a+c\equiv b+d \mod n`.

.. code-block::

    lemma int.modeq.add {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n])
      (h2 : c ≡ d [ZMOD n]) :
        a + c ≡ b + d [ZMOD n] := by
      dsimp [int.modeq] at *
      cases' h1 with x hx
      cases' h2 with y hy
      use x + y
      calc a + c - (b + d) = (a - b) + (c - d) := by ring
        _ = n * x + n * y := by rw [hx, hy]
        _ = n * (x + y) := by ring

Exercise
^^^^^^^^

.. admonition:: Lemma (subtraction rule for modular arithmetic)

  Let :math:`a`, :math:`b`, :math:`c`, :math:`d` and :math:`n` be integers, and suppose that
  :math:`a\equiv b \mod n` and :math:`c\equiv d \mod n`.  Then :math:`a-c\equiv b-d \mod n`.

.. code-block::

    lemma int.modeq.sub (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
        a - c ≡ b - d [ZMOD n] := by
      sorry

Exercise
^^^^^^^^

.. admonition:: Lemma (negation rule for modular arithmetic)

  Let :math:`a`, :math:`b` and :math:`n` be integers, and suppose that
  :math:`a\equiv b \mod n`.  Then :math:`-a\equiv -b \mod n`.

.. code-block::

    lemma int.modeq.neg (h1 : a ≡ b [ZMOD n]) :
        - a ≡ - b [ZMOD n] := by
      sorry

Example
^^^^^^^

.. admonition:: Lemma (multiplication rule for modular arithmetic)

  Let :math:`a`, :math:`b`, :math:`c`, :math:`d` and :math:`n` be integers, and suppose that
  :math:`a\equiv b \mod n` and :math:`c\equiv d \mod n`.  Then :math:`ac\equiv bd \mod n`.

.. admonition:: Proof

  Since :math:`a\equiv b \mod n`, there exists an integer :math:`x` such that :math:`a-b=nx`.
  Since :math:`c\equiv d \mod n`, there exists an integer :math:`y` such that :math:`c-d=ny`.
  Then

  .. math::

    a c - b d &= (a - b) c + b (c - d) \\
    &= (n x)  c + b  (n y) \\
    & = n (x c + b y),

  so :math:`ac\equiv bd \mod n`.

.. code-block::

    lemma int.modeq.mul (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
        a * c ≡ b * d [ZMOD n] := by
      cases' h1 with x hx
      cases' h2 with y hy
      use x * c + b * y
      calc
        a * c - b * d 
          = (a - b) * c + b * (c - d) := by ring
        _ = (n * x) * c + b * (n * y) := by rw [hx, hy]
        _ = n * (x * c + b * y) := by ring

.. _no_mod_division:

Example
^^^^^^^

Warning:  There is no "division rule" for modular arithmetic!

.. admonition:: Problem

  It is possible to have integers :math:`a`, :math:`b`, :math:`c`, :math:`d` and :math:`n` with
  :math:`a\equiv b \mod n` and :math:`c\equiv d \mod n`, but :math:`\frac{a}{c}\not\equiv \frac{b}{d} \mod n`.

.. admonition:: Solution

  We can take :math:`a=10`, :math:`b=18`, :math:`c=2`, :math:`d=6`.  Indeed,

  * :math:`10-18=4\cdot -2`, so :math:`10\equiv 18 \mod 4`;

  * :math:`2-6=4\cdot -1`, so :math:`2\equiv 6 \mod 4`;

  * :math:`\frac{10}{2}-\frac{18}{6}=2` lies between the consecutive multiples :math:`4 \cdot 0` and
    :math:`4 \cdot (0 + 1)` of 4, so :math:`\frac{10}{2}\not\equiv \frac{18}{6} \mod 4`,

Notice that here we're using the test for non-divisibility from
:numref:`Example %s <not_divisible>`, which was written up in Lean as the lemma
``int.not_dvd_of_exists_lt_and_lt``.

.. code-block::

   example :
       ∃ a b c d, a ≡ b [ZMOD 4] ∧ c ≡ d [ZMOD 4]
       ∧ ¬ a / c ≡ b / d [ZMOD 4] := by
     use 10, 18, 2, 6
     constructor
     . use -2
     constructor
     . use -1
     apply int.not_dvd_of_exists_lt_and_lt
     . norm_num
     use 0

Example
^^^^^^^^

.. admonition:: Lemma (squaring rule for modular arithmetic)

  Let :math:`a`, :math:`b` and :math:`n` be integers, and suppose that
  :math:`a\equiv b \mod n`.  Then :math:`a^2\equiv b^2 \mod n`.

.. admonition:: Proof

  Since :math:`a\equiv b \mod n`, there exists an integer :math:`x` such that :math:`a-b=nx`.
  Then

  .. math::

    a ^ 2 - b ^ 2 &= (a - b)  (a + b) \\
    &= (n x) (a + b) \\
    &= n  (x  (a + b)).

.. code-block::

    lemma int.modeq.pow_two (h : a ≡ b [ZMOD n]) :
        a ^ 2 ≡ b ^ 2 [ZMOD n] := by
      cases' h with x hx
      use x * (a + b)
      calc a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
        _ = (n * x) * (a + b) := by rw [hx]
        _ = n * (x * (a + b)) := by ring

Exercise
^^^^^^^^

.. admonition:: Lemma (cubing rule for modular arithmetic)

  Let :math:`a`, :math:`b` and :math:`n` be integers, and suppose that
  :math:`a\equiv b \mod n`.  Then :math:`a^3\equiv b^3 \mod n`.

.. code-block::

    lemma int.modeq.pow_three (h : a ≡ b [ZMOD n]) :
        a ^ 3 ≡ b ^ 3 [ZMOD n] := by
      sorry

In fact the same is true for any power, although we don't yet have the tools to prove it.  We'll
come back to this later in the course.

.. admonition:: Lemma (power rule for modular arithmetic)

  Let :math:`k` be a natural number and let :math:`a`, :math:`b` and :math:`n` be integers, and
  suppose that :math:`a\equiv b \mod n`.  Then :math:`a^k\equiv b^k \mod n`.

.. code-block::

    lemma int.modeq.pow (k : ℕ) (h : a ≡ b [ZMOD n]) :
        a ^ k ≡ b ^ k [ZMOD n] := by
      sorry -- we'll prove this later in the course

Example
^^^^^^^^

.. admonition:: Lemma (reflexivity rule for modular arithmetic)

  Let :math:`a` and :math:`n` be integers. Then :math:`a\equiv a \mod n`.

.. admonition:: Proof

  :math:`a-a=n\cdot 0`, so :math:`n\mid a - a`.

.. code-block::

    lemma int.modeq.refl (a : ℤ) : a ≡ a [ZMOD n] := by
      use 0
      ring

.. _apply_mod_lemmas_example:

Example
^^^^^^^^

Whew! That was a lot of lemmas.  But they pay off, as you will now see.  Suppose we now encounter
some very specific modular arithmetic problem of the same general type as we've seen before: the
congruence modulo :math:`n` of two expressions which differ in a kind of spot-the-difference way,
like a "rewriting" by one congruence.  For example,

.. admonition:: Problem

  Let :math:`a`, :math:`b` and :math:`n` be integers, and suppose that :math:`a\equiv 2 \mod 4`.
  Show that :math:`a b ^ 2 + a ^ 2 b + 3 a \equiv 2 b ^ 2 + 2 ^ 2 \cdot b + 3 \cdot 2 \mod 4`.

We could solve this by working directly from the definition, which is rather painful:

.. code-block::

   example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
       a * b ^ 2 + a ^ 2 * b + 3 * a 
       ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 * 2 [ZMOD 4] := by
     cases' ha with x hx
     use x * (b ^ 2 + a * b + 2 * b + 3)
     calc
       (a * b ^ 2 + a ^ 2 * b + 3 * a) - (2 * b ^ 2 + 2 ^ 2 * b + 3 * 2)
         = (a - 2) * (b ^ 2 + a * b + 2 * b + 3) := by ring
       _ = 4 * x * (b ^ 2 + a * b + 2 * b + 3) := by rw [hx]
       _ = 4 * (x * (b ^ 2 + a * b + 2 * b + 3)) := by ring

Or, better, we can solve this by applying the right combination of the lemmas we already proved,
in the right order.  This requires much less thinking:

.. code-block::

   example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
       a * b ^ 2 + a ^ 2 * b + 3
       ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 [ZMOD 4] := by
     apply int.modeq.add
     . apply int.modeq.add
       . apply int.modeq.mul
         . apply ha
         . apply int.modeq.refl
       . apply int.modeq.mul
         . apply int.modeq.pow
           apply ha
         . apply int.modeq.refl
     . apply int.modeq.refl

Exercises
^^^^^^^^^

1. Show that :math:`34\equiv 104 \mod 5`.

   .. code-block::

      example : 34 ≡ 104 [ZMOD 5] := by
        sorry

2. (symmetry rule for modular arithmetic) Let :math:`a`, :math:`b` and :math:`n` be integers, and
   suppose that :math:`a\equiv b \mod n`.  Show that :math:`b\equiv a \mod n`.

   .. code-block::

      lemma int.modeq.symm (h : a ≡ b [ZMOD n]) : b ≡ a [ZMOD n] := by
        sorry

3. (transitivity rule for modular arithmetic) Let :math:`a`, :math:`b`, :math:`c` and :math:`n` be
   integers, and suppose that :math:`a\equiv b \mod n` and :math:`b\equiv c \mod n`.  Show that
   :math:`a\equiv c \mod n`.

   .. code-block::

      lemma int.modeq.trans (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) :
          a ≡ c [ZMOD n] := by
        sorry

4. Let :math:`a`, :math:`c` and :math:`n` be integers.  Show that :math:`a+nc\equiv a \mod n`.

   .. code-block::

      lemma int.modeq_add_fac' : a + n * c ≡ a [ZMOD n] := by
        sorry

5. Give an alternative solution (i.e., with different numbers) to
   :numref:`Example %s <no_mod_division>`.

   .. code-block::

      example :
          ∃ a b c d, a ≡ b [ZMOD 4] ∧ c ≡ d [ZMOD 4] 
          ∧ ¬ a / c ≡ b / d [ZMOD 4] := by
        sorry

6. Let :math:`k` be an integer, and suppose that :math:`k\equiv 3 \mod 5`.  Then
   :math:`4 k + k ^ 3 + 3\equiv 4 \cdot 3 + 3 ^ 3 + 3 \mod 5`.

   Give two solutions, following the style of the two solutions in
   :numref:`Example %s <apply_mod_lemmas_example>`.

   .. code-block::

      example {k : ℤ} (hb : k ≡ 3 [ZMOD 5]) :
          4 * k + k ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] :=
        sorry
