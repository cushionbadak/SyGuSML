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
(constraint (= (f #x558E1F97FA769C24) #x558E1F97FA769C25))
(constraint (= (f #x6ADF8D5EACB70D0C) #x6ADF8D5EACB70D0D))
(constraint (= (f #x0FFF1B516BB93D22) #x0FFF1B516BB93D23))
(constraint (= (f #x8BD40772F32B0C5A) #x8BD40772F32B0C5B))
(constraint (= (f #x9627CA4733129DB0) #x9627CA4733129DB1))
(constraint (= (f #x0000000000000002) #x0000000000000003))
(constraint (= (f #x0000000000000003) #x0000000000000002))
(constraint (= (f #x908B0C77F372527F) #x00000908B0C77F37))
(constraint (= (f #xCA914643AFAE8431) #x00000CA914643AFA))
(constraint (= (f #x5F3A7357C8FF9DBD) #x000005F3A7357C8F))
(constraint (= (f #xC4382639D690E97D) #x00000C4382639D69))
(constraint (= (f #x042174AE2E92B4B5) #x00000042174AE2E9))
(constraint (= (f #x0000000000000000) #x0000000000000001))
(constraint (= (f #xF7BDEF7BDEF7BDF1) #xF7BDEF7BDEF7BDF0))
(check-synth)
