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
(constraint (= (f #x86399F9585550B9D) #x000218E67E561554))
(constraint (= (f #x37CA819863A4A2F5) #x0000DF2A06618E90))
(constraint (= (f #x7B33A32DA933AF79) #x0001ECCE8CB6A4CC))
(constraint (= (f #x3C3F63C3D44EBE71) #x0000F0FD8F0F5138))
(constraint (= (f #x4CADB82281527E75) #x000132B6E08A0548))
(constraint (= (f #xEE23A6C3E6D6C10F) #x0003B88E9B0F9B58))
(constraint (= (f #xFE0A17CF4A0013DB) #x0003F8285F3D2800))
(constraint (= (f #xDC39CAB6D4DFAF23) #x000370E72ADB537C))
(constraint (= (f #x9CFDD3F8CACE9D9F) #x000273F74FE32B38))
(constraint (= (f #x58D5542DEF455DE3) #x0001635550B7BD14))
(constraint (= (f #x935265DDBEC8D1A8) #x0000000000000001))
(constraint (= (f #x59EFDB8363289620) #x0000000000000001))
(constraint (= (f #xCDD7857A25736B7C) #x0000000000000001))
(constraint (= (f #xC041939BC5BD511C) #x0000000000000001))
(constraint (= (f #xD587D6774F7323B8) #x0000000000000001))
(constraint (= (f #x0000000000000001) #x0000000000000000))
(constraint (= (f #xE3F17D81FE0A50E6) #x0000000000000001))
(constraint (= (f #x491F263CF960920E) #x0000000000000001))
(constraint (= (f #x3E429F438D11ECEA) #x0000000000000001))
(constraint (= (f #xE2A8B2AC51C3B522) #x0000000000000001))
(constraint (= (f #xEA9B0243AACD5F6E) #x0000000000000001))
(constraint (= (f #x4F152549AA1C0CAD) #x00013C549526A870))
(constraint (= (f #x6577152A9444CD1E) #x0000000000000001))
(constraint (= (f #xE8F22FB9AECBCD0F) #x0003A3C8BEE6BB2C))
(constraint (= (f #x588824016D301410) #x0000000000000001))
(constraint (= (f #xB31DE052362C5B03) #x0002CC778148D8B0))
(constraint (= (f #xBE8E8B57A3153D99) #x0002FA3A2D5E8C54))
(constraint (= (f #xB2C2C2FDF2D68C43) #x0002CB0B0BF7CB58))
(constraint (= (f #xB0EA8022F50224CD) #x0002C3AA008BD408))
(constraint (= (f #x14902B98CE395B96) #x0000000000000001))
(constraint (= (f #xFB526CD839B873C8) #x0000000000000001))
(check-synth)