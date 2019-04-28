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
(constraint (= (f #xFB36C73D3A0609E9) #x0000FB36C73D3A06))
(constraint (= (f #x631B26380087EA6D) #x0000631B26380087))
(constraint (= (f #xBB761C3280189305) #x0000BB761C328018))
(constraint (= (f #xB05D2B75F1C05E01) #x0000B05D2B75F1C0))
(constraint (= (f #xC5C56446FC72332C) #x0000C5C56446FC72))
(constraint (= (f #xFECA5FD3ADC09B3A) #x0000FECA5FD3ADC0))
(constraint (= (f #xA11AF7B5367F513A) #x0000A11AF7B5367F))
(constraint (= (f #xA5058CD02A91673E) #x0000A5058CD02A91))
(constraint (= (f #xAD1758D4EB32C2DE) #x0000AD1758D4EB32))
(constraint (= (f #xAA50371EB6F1399F) #x0000AA50371EB6F1))
(constraint (= (f #x0000000000017348) #x0000000000000003))
(constraint (= (f #x000000000001FE4D) #x0000000000000003))
(constraint (= (f #x000000000001564D) #x0000000000000003))
(constraint (= (f #x000000000001AA4C) #x0000000000000003))
(constraint (= (f #x000000000001398D) #x0000000000000003))
(constraint (= (f #xB54723B8D0DFF60B) #x0B54723B8D0DFF60))
(constraint (= (f #xB583C30E822720A2) #x0B583C30E822720A))
(constraint (= (f #xB39316EEF3F4F9CB) #x0B39316EEF3F4F9C))
(constraint (= (f #x1B25F00A432E0E63) #x01B25F00A432E0E6))
(constraint (= (f #x12215DCDB89AEBEF) #x012215DCDB89AEBE))
(constraint (= (f #xAAAAAAAAAAAAAAAA) #x0000AAAAAAAAAAAA))
(constraint (= (f #x19999999999999DE) #x0000199999999999))
(constraint (= (f #x0000011113333FFE) #x0000000001111333))
(constraint (= (f #x08889BBBBBBBBBFE) #x000008889BBBBBBB))
(constraint (= (f #x08888CEEEEFFFFFE) #x000008888CEEEEFF))
(constraint (= (f #x888999DDDDDDDDDE) #x0000888999DDDDDD))
(constraint (= (f #x000000000001F813) #x0000000000000003))
(constraint (= (f #x0000000000017AD3) #x0000000000000003))
(constraint (= (f #x000000000001D2DA) #x0000000000000003))
(constraint (= (f #x0000000000019F37) #x0000000000000003))
(constraint (= (f #x000000000001C896) #x0000000000000003))
(constraint (= (f #x224129C6C8CF6D39) #x0224129C6C8CF6D3))
(constraint (= (f #x45D38A1F956137B1) #x045D38A1F956137B))
(constraint (= (f #x89443130F264A73C) #x089443130F264A73))
(constraint (= (f #x5B0939A62B0B595C) #x05B0939A62B0B595))
(constraint (= (f #xE4057CFA8F7B0D58) #x0E4057CFA8F7B0D5))
(constraint (= (f #x0000000000014C6F) #x00000000000014C6))
(constraint (= (f #x0000000000014EEA) #x00000000000014EE))
(constraint (= (f #x0000000000017B0E) #x00000000000017B0))
(constraint (= (f #x000000000001D2E7) #x0000000000001D2E))
(constraint (= (f #x0000000000011302) #x0000000000001130))
(constraint (= (f #x00000000000111BA) #x0000000000000003))
(constraint (= (f #x00000000000199BA) #x0000000000000003))
(constraint (= (f #x000000000001DDDE) #x0000000000000003))
(constraint (= (f #x0000000000015576) #x0000000000000003))
(constraint (= (f #x0000000000011BFE) #x0000000000000003))
(constraint (= (f #x00088888CCCCCDDC) #x000199999DDDDDFF))
(constraint (= (f #x88CCCDDDDDDDDDDC) #x099DDDFFFFFFFFFF))
(constraint (= (f #x111111111111199C) #x03333333333333BB))
(constraint (= (f #x0000111111199998) #x000003333333BBBB))
(constraint (= (f #x0111111111111118) #x0033333333333333))
(constraint (= (f #x000000000001B555) #x0000000000001B55))
(constraint (= (f #x0000000000014A1C) #x00000000000014A1))
(constraint (= (f #x0000000000010CDD) #x00000000000010CD))
(constraint (= (f #x0000000000013D90) #x00000000000013D9))
(constraint (= (f #x0000000000015DB0) #x00000000000015DB))
(constraint (= (f #x000000000001555C) #x0000000000003FFF))
(constraint (= (f #x0000000000019998) #x0000000000003BBB))
(check-synth)