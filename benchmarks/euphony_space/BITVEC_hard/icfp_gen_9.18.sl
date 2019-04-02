(set-logic BV)
(synth-fun f ((x (_ BitVec 64))) (_ BitVec 64)
  ((Start (_ BitVec 64)) (StartBool Bool))
  ((Start (_ BitVec 64)
            (
              (bvnot Start)
              (bvxor Start Start)
              (bvand Start Start)
              (bvor Start Start)
              (bvneg Start)
              (bvadd Start Start)
              (bvmul Start Start)
              (bvudiv Start Start)
              (bvurem Start Start)
              (bvlshr Start Start)
              (bvashr Start Start)
              (bvshl Start Start)
              (bvsdiv Start Start)
              (bvsrem Start Start)
              (bvsub Start Start)
              x
              #x0000000000000000
              #x0000000000000001
              #x0000000000000002
              #x0000000000000003
              #x0000000000000004
              #x0000000000000005
              #x0000000000000006
              #x0000000000000007
              #x0000000000000008
              #x0000000000000009
              #x0000000000000009
              #x0000000000000009
              #x000000000000000A
              #x000000000000000B
              #x000000000000000C
              #x000000000000000D
              #x000000000000000E
              #x000000000000000F
              #x0000000000000010
              #x0000000000000011
              #x0000000000000012
              #x0000000000000013
              #x0000000000000014
              #x0000000000000015
              #x0000000000000016
              #x0000000000000017
              #x0000000000000018
              #x0000000000000019
              #x000000000000001A
              #x000000000000001B
              #x000000000000001C
              #x000000000000001D
              #x000000000000001E
              #x000000000000001F
              (ite StartBool Start Start)
            ))
  (StartBool Bool
            (
              (= Start Start)
              (not StartBool)
              (and StartBool StartBool)
              (or StartBool StartBool)
              (xor StartBool StartBool)
            ))
            ))
(constraint (= (f #xCEC82F2E96E668B2) #x0000000000000001))
(constraint (= (f #xBCC0BC6852185AE6) #x0000000000000001))
(constraint (= (f #x30B43615AA983D54) #x0000000000000001))
(constraint (= (f #x40E2B4CB5A9E54F6) #x0000000000000001))
(constraint (= (f #x52555BEDD494A3EE) #x0000000000000001))
(constraint (= (f #xFFFFFFFF80000002) #x0000000000000000))
(constraint (= (f #x0000000000000001) #x0000000000000000))
(constraint (= (f #x7475A26A39213808) #x0001D1D689A8E484))
(constraint (= (f #x8057EB804CF5E077) #x0002015FAE0133D4))
(constraint (= (f #xBFF0F265EAF4FFFF) #x0002FFC3C997ABD0))
(constraint (= (f #x2F0600431013128D) #x0000BC18010C404C))
(constraint (= (f #x1CD164D410AEFFFF) #x00007345935042B8))
(constraint (= (f #x00000000001026E1) #x0000000000000000))
(constraint (= (f #x00000000001CC6B2) #x0000000000000001))
(constraint (= (f #x0000000000124A1E) #x0000000000000001))
(constraint (= (f #x0000000000186AB0) #x0000000000000001))
(constraint (= (f #x00000000001E43E5) #x0000000000000000))
(constraint (= (f #x0000000000150EE4) #x0000000000000001))
(constraint (= (f #x00000000001AFFFF) #x0000000000000000))
(constraint (= (f #x00000000001181FB) #x0000000000000000))
(constraint (= (f #x00000000001777FA) #x0000000000000001))
(constraint (= (f #x000000000018FFFF) #x0000000000000000))
(check-synth)
