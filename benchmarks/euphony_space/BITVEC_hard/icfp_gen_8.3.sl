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
(constraint (= (f #xCFBAE81390AFA698) #xFFFFFFFFCFBAE813))
(constraint (= (f #xD084207D0E11E641) #xFFFFFFFFD084207D))
(constraint (= (f #x2695FD2BFA0973DD) #xFFFFFFFF2695FD2B))
(constraint (= (f #x1DB98E96C36AC14C) #xFFFFFFFF1DB98E96))
(constraint (= (f #x93D97B67C0134561) #xFFFFFFFF93D97B67))
(constraint (= (f #x319631563C9378AF) #x19CD39D5386D90EA))
(constraint (= (f #xB0CA4AB4CFF52177) #x09E6B6A966015BD1))
(constraint (= (f #x8849FE48422D5F4F) #x0EF6C036F7BA5416))
(constraint (= (f #x90B3A3A8146F2B73) #x0DE98B8AFD721A91))
(constraint (= (f #x95EFE7D3997EAAA3) #x0D4203058CD02AAB))
(constraint (= (f #x000000000001B238) #xFFFFFFFF00000000))
(constraint (= (f #x000000000001AF24) #xFFFFFFFF00000000))
(constraint (= (f #x00000000000107D1) #xFFFFFFFF00000000))
(constraint (= (f #x000000000001C2E1) #xFFFFFFFF00000000))
(constraint (= (f #x0000000000015DD0) #xFFFFFFFF00000000))
(constraint (= (f #xA424100229285149) #xFFFFFFFF00000000))
(constraint (= (f #x4A84894A88240885) #xFFFFFFFF00000000))
(constraint (= (f #x85524490902A9155) #xFFFFFFFF00000000))
(constraint (= (f #x24A544A4A4485121) #xFFFFFFFF00000000))
(constraint (= (f #x14A490A45044A529) #xFFFFFFFF00000000))
(constraint (= (f #x00000000000152C3) #xFFFFFFFF00000000))
(constraint (= (f #x0000000000012D93) #xFFFFFFFF00000000))
(constraint (= (f #x000000000001BB0B) #xFFFFFFFF00000000))
(constraint (= (f #x00000000000183AF) #xFFFFFFFF00000000))
(constraint (= (f #x0000000000014F8B) #xFFFFFFFF00000000))
(constraint (= (f #x922CAA595A0F05DA) #x0DBA6AB4D4BE1F44))
(constraint (= (f #x888F3A18A2AC2B5E) #x0EEE18BCEBAA7A94))
(constraint (= (f #xCDEF76ACA8776616) #x0642112A6AF1133D))
(constraint (= (f #x5A67867F8134B38E) #x14B30F300FD9698E))
(constraint (= (f #x328BFE6D823E8EB6) #x19AE80324FB82E29))
(constraint (= (f #x0000000000015021) #xFFFFFFFF00000000))
(constraint (= (f #x0000000000010A85) #xFFFFFFFF00000000))
(constraint (= (f #x0000000000014495) #xFFFFFFFF00000000))
(constraint (= (f #x0000000000015451) #xFFFFFFFF00000000))
(constraint (= (f #x0000000000012495) #xFFFFFFFF00000000))
(constraint (= (f #x0000000000000001) #xFFFFFFFF00000000))
(constraint (= (f #x0000000000016F96) #x1FFFFFFFFFFFD20D))
(constraint (= (f #x0000000000017C06) #x1FFFFFFFFFFFD07F))
(constraint (= (f #x0000000000014BDE) #x1FFFFFFFFFFFD684))
(constraint (= (f #x000000000001B426) #x1FFFFFFFFFFFC97B))
(constraint (= (f #x0000000000015A0E) #x1FFFFFFFFFFFD4BE))
(constraint (= (f #xFFFF0000FFFF0002) #x1FFFFFFFFFFFFFFF))
(check-synth)