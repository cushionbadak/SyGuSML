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
(constraint (= (f #x6475B86FF1FDE997) #x6475B86FF1FDE997))
(constraint (= (f #xEED1C0B3B3581CA3) #xEED1C0B3B3581CA3))
(constraint (= (f #x4C800FC54ADB1617) #x4C800FC54ADB1617))
(constraint (= (f #xF9A0D02337F1B63F) #xF9A0D02337F1B63F))
(constraint (= (f #x5D26B2E120DA03EB) #x5D26B2E120DA03EB))
(constraint (= (f #x72AFA75EFD0F0DB0) #x0000000000000001))
(constraint (= (f #xD634A5E83EC227C5) #x0000000000000000))
(constraint (= (f #x8EE61B76E0CA7D12) #x0000000000000001))
(constraint (= (f #x4BA7C6E4E72B513A) #x0000000000000001))
(constraint (= (f #x73273715D6877BC9) #x0000000000000000))
(constraint (= (f #x0000000000000016) #x0000000000000000))
(constraint (= (f #x000000000000000E) #x0000000000000000))
(constraint (= (f #x000000000000000F) #x0000000000000000))
(constraint (= (f #xAAAAAAAAAAAAAAAB) #x0000000000000000))
(constraint (= (f #x1222BBB0F0F8E533) #x1222BBB0F0F8E533))
(constraint (= (f #x4C53D402A4F49841) #x4C53D402A4F49843))
(constraint (= (f #x9A6A595464CEAC2C) #x0000000000000001))
(constraint (= (f #x608711D849043DE4) #x0000000000000001))
(constraint (= (f #xE5B10E64F26529A9) #x0000000000000000))
(constraint (= (f #xA39EF8DE677E8600) #xA39EF8DE677E8600))
(constraint (= (f #x726D45BF79FF61BB) #x726D45BF79FF61BB))
(constraint (= (f #x870605C40083AA24) #x0000000000000001))
(constraint (= (f #xC58E599FE5BA0297) #xC58E599FE5BA0297))
(constraint (= (f #x78FC39C0B092BA4A) #x78FC39C0B092BA4A))
(constraint (= (f #x000000000000000E) #x0000000000000000))
(constraint (= (f #xAAAAAAAAAAAAAAAB) #x0000000000000000))
(constraint (= (f #x0000000000000016) #x0000000000000000))
(constraint (= (f #x800000000000000A) #x0000000000000001))
(constraint (= (f #x000000000000001E) #x0000000000000001))
(constraint (= (f #x000000000000000C) #x0000000000000001))
(constraint (= (f #x2AA224A508284406) #x0000000000000001))
(constraint (= (f #x000000000000001A) #x0000000000000000))
(constraint (= (f #x8568B3765006F937) #x0000000000000000))
(constraint (= (f #x7B4C9BECDDE26270) #x0000000000000001))
(constraint (= (f #x9069805E1679FCAA) #x9069805E1679FCAA))
(constraint (= (f #x6DC627C8652482CD) #x0000000000000000))
(constraint (= (f #x2EB8C4C9AACCBE48) #x0000000000000001))
(constraint (= (f #xAA052549091014AB) #xAA052549091014AB))
(constraint (= (f #xB089071947567D3B) #xB089071947567D3B))
(constraint (= (f #xD263691191C45373) #x0000000000000000))
(check-synth)
