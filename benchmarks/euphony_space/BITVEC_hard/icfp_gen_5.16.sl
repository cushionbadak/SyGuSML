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
(constraint (= (f #x44BDEA77706EF696) #x44BDEA77706EF696))
(constraint (= (f #x378FE2296B844650) #x378FE2296B844650))
(constraint (= (f #x48A7DB48F96DF2C6) #x48A7DB48F96DF2C6))
(constraint (= (f #x9D4E550A2D0B80A0) #x9D4E550A2D0B80A0))
(constraint (= (f #x619584AFE2CEF05E) #x619584AFE2CEF05E))
(constraint (= (f #x000000000000987D) #x000000000000987D))
(constraint (= (f #x000000000000D48A) #x000000000000D48A))
(constraint (= (f #x0000000000017BF1) #x0000000000017BF1))
(constraint (= (f #x000000000001FE42) #x000000000001FE42))
(constraint (= (f #x0000000000014A4D) #x0000000000014A4D))
(constraint (= (f #x6986047E857AFF17) #x06986047E857AFF1))
(constraint (= (f #x355AB728FF7EFBBB) #x0355AB728FF7EFBB))
(constraint (= (f #x7CBB16A4867B4B1C) #x07CBB16A4867B4B1))
(constraint (= (f #xDD80A894275C97F0) #x0DD80A894275C97F))
(constraint (= (f #x8358AF3AC699C18C) #x08358AF3AC699C18))
(constraint (= (f #x0000000000000000) #x0000000000000000))
(check-synth)
