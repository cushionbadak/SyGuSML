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
(constraint (= (f #x653CAF4FBE9AB184) #x653CAF4FBE9AB184))
(constraint (= (f #x968B0895A19018A6) #x968B0895A19018A6))
(constraint (= (f #xC367F61A60462DAA) #xC367F61A60462DAA))
(constraint (= (f #xDE651E8601FD99E4) #xDE651E8601FD99E4))
(constraint (= (f #x76DF7DBFEBB87F68) #x76DF7DBFEBB87F68))
(constraint (= (f #x00000000001CEC12) #x00000000001CEC12))
(constraint (= (f #x00000000001BEBFA) #x00000000001BEBFA))
(constraint (= (f #x0000000000151C54) #x0000000000151C54))
(constraint (= (f #x000000000010BF2A) #x000000000010BF2A))
(constraint (= (f #x00000000001C8E04) #x00000000001C8E04))
(constraint (= (f #x7AB85B06C7BD3AA5) #x7AB85B06C7BD3AA7))
(constraint (= (f #x8C1D721D9321AF69) #x8C1D721D9321AF6B))
(constraint (= (f #x114F9AC0C328E4E9) #x114F9AC0C328E4EB))
(constraint (= (f #xAE3DE96A4C91C78F) #xAE3DE96A4C91C78D))
(constraint (= (f #xE8A484294BA1D9AB) #xE8A484294BA1D9A9))
(constraint (= (f #x1CCC0227CB486F1B) #x1CCC0227CB486F19))
(constraint (= (f #xB85FC23ED3E938B7) #xB85FC23ED3E938B5))
(constraint (= (f #xC09F8E8BA034D79D) #xC09F8E8BA034D79F))
(constraint (= (f #xFC70CA6C745FF855) #xFC70CA6C745FF857))
(constraint (= (f #xD9F9DB62C4592E97) #xD9F9DB62C4592E95))
(constraint (= (f #x00000000001EA4C7) #x00000000001EA4C5))
(constraint (= (f #x00000000001E926D) #x00000000001E926F))
(constraint (= (f #x000000000013E205) #x000000000013E207))
(constraint (= (f #x00000000001C8605) #x00000000001C8607))
(constraint (= (f #x00000000001EB301) #x00000000001EB303))
(constraint (= (f #x000000000017B819) #x000000000017B81B))
(constraint (= (f #x00000000001A919B) #x00000000001A9199))
(constraint (= (f #x00000000001D6599) #x00000000001D659B))
(constraint (= (f #x000000000010FF5D) #x000000000010FF5F))
(constraint (= (f #x0000000000153F11) #x0000000000153F13))
(constraint (= (f #x78F7BD9ECD03F41A) #x78F7BD9ECD03F41A))
(constraint (= (f #x46B98ACDD53AE204) #x46B98ACDD53AE204))
(constraint (= (f #x6FF994A9B66DFAB6) #x6FF994A9B66DFAB6))
(constraint (= (f #x57C3338F50626BE5) #x57C3338F50626BE7))
(constraint (= (f #x86AFB941EAADB3C1) #x86AFB941EAADB3C3))
(constraint (= (f #x178083756CD9BAD9) #x178083756CD9BADB))
(constraint (= (f #xBBD9D4CB0F7BF04A) #xBBD9D4CB0F7BF04A))
(constraint (= (f #x392170A0D475602E) #x392170A0D475602E))
(constraint (= (f #x87E6B5C18419AFDB) #x87E6B5C18419AFD9))
(constraint (= (f #x966F7D29A510F709) #x966F7D29A510F70B))
(constraint (= (f #x00000000001C025B) #x00000000001C0259))
(constraint (= (f #x00000000001A35CC) #x00000000001A35CC))
(constraint (= (f #x00000000001A4F47) #x00000000001A4F45))
(check-synth)