%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:41 EST 2020

% Result     : Theorem 8.77s
% Output     : CNFRefutation 8.77s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 370 expanded)
%              Number of leaves         :   24 ( 145 expanded)
%              Depth                    :   20
%              Number of atoms          :  510 (2998 expanded)
%              Number of equality atoms :    6 (  48 expanded)
%              Maximal formula depth    :   29 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tsep_1 > k3_xboole_0 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_176,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( ~ v2_struct_0(E)
                          & m1_pre_topc(E,A) )
                       => ( ( m1_pre_topc(B,D)
                            & m1_pre_topc(C,E) )
                         => ( r1_tsep_1(B,C)
                            | m1_pre_topc(k2_tsep_1(A,B,C),k2_tsep_1(A,D,E)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tmap_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k2_tsep_1(A,B,C))
        & v1_pre_topc(k2_tsep_1(A,B,C))
        & m1_pre_topc(k2_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

tff(f_136,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( ~ r1_tsep_1(B,C)
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_pre_topc(D)
                      & m1_pre_topc(D,A) )
                   => ( D = k2_tsep_1(A,B,C)
                    <=> u1_struct_0(D) = k3_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

tff(f_122,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ( m1_pre_topc(B,C)
                   => ( ( ~ r1_tsep_1(C,D)
                        & ~ r1_tsep_1(D,C) )
                      | ( r1_tsep_1(B,D)
                        & r1_tsep_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_46,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_8,plain,(
    ! [A_20,B_21,C_22] :
      ( m1_pre_topc(k2_tsep_1(A_20,B_21,C_22),A_20)
      | ~ m1_pre_topc(C_22,A_20)
      | v2_struct_0(C_22)
      | ~ m1_pre_topc(B_21,A_20)
      | v2_struct_0(B_21)
      | ~ l1_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_28,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_32,plain,(
    m1_pre_topc('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_30,plain,(
    m1_pre_topc('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_34,plain,(
    m1_pre_topc('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_56,plain,(
    ! [B_75,C_76,A_77] :
      ( r1_tarski(u1_struct_0(B_75),u1_struct_0(C_76))
      | ~ m1_pre_topc(B_75,C_76)
      | ~ m1_pre_topc(C_76,A_77)
      | ~ m1_pre_topc(B_75,A_77)
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_58,plain,(
    ! [B_75] :
      ( r1_tarski(u1_struct_0(B_75),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_75,'#skF_4')
      | ~ m1_pre_topc(B_75,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_56])).

tff(c_71,plain,(
    ! [B_75] :
      ( r1_tarski(u1_struct_0(B_75),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_75,'#skF_4')
      | ~ m1_pre_topc(B_75,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_58])).

tff(c_66,plain,(
    ! [B_75] :
      ( r1_tarski(u1_struct_0(B_75),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_75,'#skF_5')
      | ~ m1_pre_topc(B_75,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_56])).

tff(c_81,plain,(
    ! [B_75] :
      ( r1_tarski(u1_struct_0(B_75),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_75,'#skF_5')
      | ~ m1_pre_topc(B_75,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_66])).

tff(c_10,plain,(
    ! [A_20,B_21,C_22] :
      ( v1_pre_topc(k2_tsep_1(A_20,B_21,C_22))
      | ~ m1_pre_topc(C_22,A_20)
      | v2_struct_0(C_22)
      | ~ m1_pre_topc(B_21,A_20)
      | v2_struct_0(B_21)
      | ~ l1_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_117,plain,(
    ! [A_118,B_119,C_120] :
      ( u1_struct_0(k2_tsep_1(A_118,B_119,C_120)) = k3_xboole_0(u1_struct_0(B_119),u1_struct_0(C_120))
      | ~ m1_pre_topc(k2_tsep_1(A_118,B_119,C_120),A_118)
      | ~ v1_pre_topc(k2_tsep_1(A_118,B_119,C_120))
      | v2_struct_0(k2_tsep_1(A_118,B_119,C_120))
      | r1_tsep_1(B_119,C_120)
      | ~ m1_pre_topc(C_120,A_118)
      | v2_struct_0(C_120)
      | ~ m1_pre_topc(B_119,A_118)
      | v2_struct_0(B_119)
      | ~ l1_pre_topc(A_118)
      | v2_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_121,plain,(
    ! [A_121,B_122,C_123] :
      ( u1_struct_0(k2_tsep_1(A_121,B_122,C_123)) = k3_xboole_0(u1_struct_0(B_122),u1_struct_0(C_123))
      | ~ v1_pre_topc(k2_tsep_1(A_121,B_122,C_123))
      | v2_struct_0(k2_tsep_1(A_121,B_122,C_123))
      | r1_tsep_1(B_122,C_123)
      | ~ m1_pre_topc(C_123,A_121)
      | v2_struct_0(C_123)
      | ~ m1_pre_topc(B_122,A_121)
      | v2_struct_0(B_122)
      | ~ l1_pre_topc(A_121)
      | v2_struct_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_8,c_117])).

tff(c_12,plain,(
    ! [A_20,B_21,C_22] :
      ( ~ v2_struct_0(k2_tsep_1(A_20,B_21,C_22))
      | ~ m1_pre_topc(C_22,A_20)
      | v2_struct_0(C_22)
      | ~ m1_pre_topc(B_21,A_20)
      | v2_struct_0(B_21)
      | ~ l1_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_188,plain,(
    ! [A_124,B_125,C_126] :
      ( u1_struct_0(k2_tsep_1(A_124,B_125,C_126)) = k3_xboole_0(u1_struct_0(B_125),u1_struct_0(C_126))
      | ~ v1_pre_topc(k2_tsep_1(A_124,B_125,C_126))
      | r1_tsep_1(B_125,C_126)
      | ~ m1_pre_topc(C_126,A_124)
      | v2_struct_0(C_126)
      | ~ m1_pre_topc(B_125,A_124)
      | v2_struct_0(B_125)
      | ~ l1_pre_topc(A_124)
      | v2_struct_0(A_124) ) ),
    inference(resolution,[status(thm)],[c_121,c_12])).

tff(c_192,plain,(
    ! [A_127,B_128,C_129] :
      ( u1_struct_0(k2_tsep_1(A_127,B_128,C_129)) = k3_xboole_0(u1_struct_0(B_128),u1_struct_0(C_129))
      | r1_tsep_1(B_128,C_129)
      | ~ m1_pre_topc(C_129,A_127)
      | v2_struct_0(C_129)
      | ~ m1_pre_topc(B_128,A_127)
      | v2_struct_0(B_128)
      | ~ l1_pre_topc(A_127)
      | v2_struct_0(A_127) ) ),
    inference(resolution,[status(thm)],[c_10,c_188])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r1_tarski(k3_xboole_0(A_1,C_3),k3_xboole_0(B_2,D_4))
      | ~ r1_tarski(C_3,D_4)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_240,plain,(
    ! [A_127,C_3,A_1,C_129,B_128] :
      ( r1_tarski(k3_xboole_0(A_1,C_3),u1_struct_0(k2_tsep_1(A_127,B_128,C_129)))
      | ~ r1_tarski(C_3,u1_struct_0(C_129))
      | ~ r1_tarski(A_1,u1_struct_0(B_128))
      | r1_tsep_1(B_128,C_129)
      | ~ m1_pre_topc(C_129,A_127)
      | v2_struct_0(C_129)
      | ~ m1_pre_topc(B_128,A_127)
      | v2_struct_0(B_128)
      | ~ l1_pre_topc(A_127)
      | v2_struct_0(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_2])).

tff(c_24,plain,(
    ! [B_42,C_44,A_38] :
      ( m1_pre_topc(B_42,C_44)
      | ~ r1_tarski(u1_struct_0(B_42),u1_struct_0(C_44))
      | ~ m1_pre_topc(C_44,A_38)
      | ~ m1_pre_topc(B_42,A_38)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_440,plain,(
    ! [C_160,C_162,B_159,A_158,A_161] :
      ( m1_pre_topc(k2_tsep_1(A_161,B_159,C_160),C_162)
      | ~ r1_tarski(k3_xboole_0(u1_struct_0(B_159),u1_struct_0(C_160)),u1_struct_0(C_162))
      | ~ m1_pre_topc(C_162,A_158)
      | ~ m1_pre_topc(k2_tsep_1(A_161,B_159,C_160),A_158)
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158)
      | r1_tsep_1(B_159,C_160)
      | ~ m1_pre_topc(C_160,A_161)
      | v2_struct_0(C_160)
      | ~ m1_pre_topc(B_159,A_161)
      | v2_struct_0(B_159)
      | ~ l1_pre_topc(A_161)
      | v2_struct_0(A_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_24])).

tff(c_1370,plain,(
    ! [C_375,B_374,A_372,B_370,C_373,A_371,A_376] :
      ( m1_pre_topc(k2_tsep_1(A_372,B_374,C_375),k2_tsep_1(A_376,B_370,C_373))
      | ~ m1_pre_topc(k2_tsep_1(A_376,B_370,C_373),A_371)
      | ~ m1_pre_topc(k2_tsep_1(A_372,B_374,C_375),A_371)
      | ~ l1_pre_topc(A_371)
      | ~ v2_pre_topc(A_371)
      | r1_tsep_1(B_374,C_375)
      | ~ m1_pre_topc(C_375,A_372)
      | v2_struct_0(C_375)
      | ~ m1_pre_topc(B_374,A_372)
      | v2_struct_0(B_374)
      | ~ l1_pre_topc(A_372)
      | v2_struct_0(A_372)
      | ~ r1_tarski(u1_struct_0(C_375),u1_struct_0(C_373))
      | ~ r1_tarski(u1_struct_0(B_374),u1_struct_0(B_370))
      | r1_tsep_1(B_370,C_373)
      | ~ m1_pre_topc(C_373,A_376)
      | v2_struct_0(C_373)
      | ~ m1_pre_topc(B_370,A_376)
      | v2_struct_0(B_370)
      | ~ l1_pre_topc(A_376)
      | v2_struct_0(A_376) ) ),
    inference(resolution,[status(thm)],[c_240,c_440])).

tff(c_1374,plain,(
    ! [C_381,A_380,B_379,A_378,B_382,C_377] :
      ( m1_pre_topc(k2_tsep_1(A_378,B_382,C_381),k2_tsep_1(A_380,B_379,C_377))
      | ~ m1_pre_topc(k2_tsep_1(A_378,B_382,C_381),A_380)
      | ~ v2_pre_topc(A_380)
      | r1_tsep_1(B_382,C_381)
      | ~ m1_pre_topc(C_381,A_378)
      | v2_struct_0(C_381)
      | ~ m1_pre_topc(B_382,A_378)
      | v2_struct_0(B_382)
      | ~ l1_pre_topc(A_378)
      | v2_struct_0(A_378)
      | ~ r1_tarski(u1_struct_0(C_381),u1_struct_0(C_377))
      | ~ r1_tarski(u1_struct_0(B_382),u1_struct_0(B_379))
      | r1_tsep_1(B_379,C_377)
      | ~ m1_pre_topc(C_377,A_380)
      | v2_struct_0(C_377)
      | ~ m1_pre_topc(B_379,A_380)
      | v2_struct_0(B_379)
      | ~ l1_pre_topc(A_380)
      | v2_struct_0(A_380) ) ),
    inference(resolution,[status(thm)],[c_8,c_1370])).

tff(c_1402,plain,(
    ! [A_380,B_379,B_75,A_378,B_382] :
      ( m1_pre_topc(k2_tsep_1(A_378,B_382,B_75),k2_tsep_1(A_380,B_379,'#skF_5'))
      | ~ m1_pre_topc(k2_tsep_1(A_378,B_382,B_75),A_380)
      | ~ v2_pre_topc(A_380)
      | r1_tsep_1(B_382,B_75)
      | ~ m1_pre_topc(B_75,A_378)
      | v2_struct_0(B_75)
      | ~ m1_pre_topc(B_382,A_378)
      | v2_struct_0(B_382)
      | ~ l1_pre_topc(A_378)
      | v2_struct_0(A_378)
      | ~ r1_tarski(u1_struct_0(B_382),u1_struct_0(B_379))
      | r1_tsep_1(B_379,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_380)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_379,A_380)
      | v2_struct_0(B_379)
      | ~ l1_pre_topc(A_380)
      | v2_struct_0(A_380)
      | ~ m1_pre_topc(B_75,'#skF_5')
      | ~ m1_pre_topc(B_75,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_81,c_1374])).

tff(c_1426,plain,(
    ! [B_386,A_383,B_385,A_384,B_387] :
      ( m1_pre_topc(k2_tsep_1(A_384,B_386,B_387),k2_tsep_1(A_383,B_385,'#skF_5'))
      | ~ m1_pre_topc(k2_tsep_1(A_384,B_386,B_387),A_383)
      | ~ v2_pre_topc(A_383)
      | r1_tsep_1(B_386,B_387)
      | ~ m1_pre_topc(B_387,A_384)
      | v2_struct_0(B_387)
      | ~ m1_pre_topc(B_386,A_384)
      | v2_struct_0(B_386)
      | ~ l1_pre_topc(A_384)
      | v2_struct_0(A_384)
      | ~ r1_tarski(u1_struct_0(B_386),u1_struct_0(B_385))
      | r1_tsep_1(B_385,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_383)
      | ~ m1_pre_topc(B_385,A_383)
      | v2_struct_0(B_385)
      | ~ l1_pre_topc(A_383)
      | v2_struct_0(A_383)
      | ~ m1_pre_topc(B_387,'#skF_5')
      | ~ m1_pre_topc(B_387,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1402])).

tff(c_1460,plain,(
    ! [A_384,B_75,B_387,A_383] :
      ( m1_pre_topc(k2_tsep_1(A_384,B_75,B_387),k2_tsep_1(A_383,'#skF_4','#skF_5'))
      | ~ m1_pre_topc(k2_tsep_1(A_384,B_75,B_387),A_383)
      | ~ v2_pre_topc(A_383)
      | r1_tsep_1(B_75,B_387)
      | ~ m1_pre_topc(B_387,A_384)
      | v2_struct_0(B_387)
      | ~ m1_pre_topc(B_75,A_384)
      | v2_struct_0(B_75)
      | ~ l1_pre_topc(A_384)
      | v2_struct_0(A_384)
      | r1_tsep_1('#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5',A_383)
      | ~ m1_pre_topc('#skF_4',A_383)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_383)
      | v2_struct_0(A_383)
      | ~ m1_pre_topc(B_387,'#skF_5')
      | ~ m1_pre_topc(B_387,'#skF_1')
      | ~ m1_pre_topc(B_75,'#skF_4')
      | ~ m1_pre_topc(B_75,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_71,c_1426])).

tff(c_1477,plain,(
    ! [A_384,B_75,B_387,A_383] :
      ( m1_pre_topc(k2_tsep_1(A_384,B_75,B_387),k2_tsep_1(A_383,'#skF_4','#skF_5'))
      | ~ m1_pre_topc(k2_tsep_1(A_384,B_75,B_387),A_383)
      | ~ v2_pre_topc(A_383)
      | r1_tsep_1(B_75,B_387)
      | ~ m1_pre_topc(B_387,A_384)
      | v2_struct_0(B_387)
      | ~ m1_pre_topc(B_75,A_384)
      | v2_struct_0(B_75)
      | ~ l1_pre_topc(A_384)
      | v2_struct_0(A_384)
      | r1_tsep_1('#skF_4','#skF_5')
      | ~ m1_pre_topc('#skF_5',A_383)
      | ~ m1_pre_topc('#skF_4',A_383)
      | ~ l1_pre_topc(A_383)
      | v2_struct_0(A_383)
      | ~ m1_pre_topc(B_387,'#skF_5')
      | ~ m1_pre_topc(B_387,'#skF_1')
      | ~ m1_pre_topc(B_75,'#skF_4')
      | ~ m1_pre_topc(B_75,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1460])).

tff(c_2270,plain,(
    r1_tsep_1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1477])).

tff(c_20,plain,(
    ! [C_35,D_37,B_31,A_23] :
      ( ~ r1_tsep_1(C_35,D_37)
      | r1_tsep_1(B_31,D_37)
      | ~ m1_pre_topc(B_31,C_35)
      | ~ m1_pre_topc(D_37,A_23)
      | v2_struct_0(D_37)
      | ~ m1_pre_topc(C_35,A_23)
      | v2_struct_0(C_35)
      | ~ m1_pre_topc(B_31,A_23)
      | v2_struct_0(B_31)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2272,plain,(
    ! [B_31,A_23] :
      ( r1_tsep_1(B_31,'#skF_5')
      | ~ m1_pre_topc(B_31,'#skF_4')
      | ~ m1_pre_topc('#skF_5',A_23)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_23)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_31,A_23)
      | v2_struct_0(B_31)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_2270,c_20])).

tff(c_2291,plain,(
    ! [B_481,A_482] :
      ( r1_tsep_1(B_481,'#skF_5')
      | ~ m1_pre_topc(B_481,'#skF_4')
      | ~ m1_pre_topc('#skF_5',A_482)
      | ~ m1_pre_topc('#skF_4',A_482)
      | ~ m1_pre_topc(B_481,A_482)
      | v2_struct_0(B_481)
      | ~ l1_pre_topc(A_482)
      | ~ v2_pre_topc(A_482)
      | v2_struct_0(A_482) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_36,c_2272])).

tff(c_2293,plain,(
    ! [B_481] :
      ( r1_tsep_1(B_481,'#skF_5')
      | ~ m1_pre_topc(B_481,'#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_481,'#skF_1')
      | v2_struct_0(B_481)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_2291])).

tff(c_2296,plain,(
    ! [B_481] :
      ( r1_tsep_1(B_481,'#skF_5')
      | ~ m1_pre_topc(B_481,'#skF_4')
      | ~ m1_pre_topc(B_481,'#skF_1')
      | v2_struct_0(B_481)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_38,c_2293])).

tff(c_2298,plain,(
    ! [B_483] :
      ( r1_tsep_1(B_483,'#skF_5')
      | ~ m1_pre_topc(B_483,'#skF_4')
      | ~ m1_pre_topc(B_483,'#skF_1')
      | v2_struct_0(B_483) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2296])).

tff(c_60,plain,(
    ! [B_75] :
      ( r1_tarski(u1_struct_0(B_75),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_75,'#skF_2')
      | ~ m1_pre_topc(B_75,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_56])).

tff(c_74,plain,(
    ! [B_75] :
      ( r1_tarski(u1_struct_0(B_75),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_75,'#skF_2')
      | ~ m1_pre_topc(B_75,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_60])).

tff(c_1458,plain,(
    ! [A_384,B_75,B_387,A_383] :
      ( m1_pre_topc(k2_tsep_1(A_384,B_75,B_387),k2_tsep_1(A_383,'#skF_2','#skF_5'))
      | ~ m1_pre_topc(k2_tsep_1(A_384,B_75,B_387),A_383)
      | ~ v2_pre_topc(A_383)
      | r1_tsep_1(B_75,B_387)
      | ~ m1_pre_topc(B_387,A_384)
      | v2_struct_0(B_387)
      | ~ m1_pre_topc(B_75,A_384)
      | v2_struct_0(B_75)
      | ~ l1_pre_topc(A_384)
      | v2_struct_0(A_384)
      | r1_tsep_1('#skF_2','#skF_5')
      | ~ m1_pre_topc('#skF_5',A_383)
      | ~ m1_pre_topc('#skF_2',A_383)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_383)
      | v2_struct_0(A_383)
      | ~ m1_pre_topc(B_387,'#skF_5')
      | ~ m1_pre_topc(B_387,'#skF_1')
      | ~ m1_pre_topc(B_75,'#skF_2')
      | ~ m1_pre_topc(B_75,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_74,c_1426])).

tff(c_1474,plain,(
    ! [A_384,B_75,B_387,A_383] :
      ( m1_pre_topc(k2_tsep_1(A_384,B_75,B_387),k2_tsep_1(A_383,'#skF_2','#skF_5'))
      | ~ m1_pre_topc(k2_tsep_1(A_384,B_75,B_387),A_383)
      | ~ v2_pre_topc(A_383)
      | r1_tsep_1(B_75,B_387)
      | ~ m1_pre_topc(B_387,A_384)
      | v2_struct_0(B_387)
      | ~ m1_pre_topc(B_75,A_384)
      | v2_struct_0(B_75)
      | ~ l1_pre_topc(A_384)
      | v2_struct_0(A_384)
      | r1_tsep_1('#skF_2','#skF_5')
      | ~ m1_pre_topc('#skF_5',A_383)
      | ~ m1_pre_topc('#skF_2',A_383)
      | ~ l1_pre_topc(A_383)
      | v2_struct_0(A_383)
      | ~ m1_pre_topc(B_387,'#skF_5')
      | ~ m1_pre_topc(B_387,'#skF_1')
      | ~ m1_pre_topc(B_75,'#skF_2')
      | ~ m1_pre_topc(B_75,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1458])).

tff(c_2104,plain,(
    r1_tsep_1('#skF_2','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1474])).

tff(c_14,plain,(
    ! [D_37,C_35,B_31,A_23] :
      ( ~ r1_tsep_1(D_37,C_35)
      | r1_tsep_1(D_37,B_31)
      | ~ m1_pre_topc(B_31,C_35)
      | ~ m1_pre_topc(D_37,A_23)
      | v2_struct_0(D_37)
      | ~ m1_pre_topc(C_35,A_23)
      | v2_struct_0(C_35)
      | ~ m1_pre_topc(B_31,A_23)
      | v2_struct_0(B_31)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_2112,plain,(
    ! [B_31,A_23] :
      ( r1_tsep_1('#skF_2',B_31)
      | ~ m1_pre_topc(B_31,'#skF_5')
      | ~ m1_pre_topc('#skF_2',A_23)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc('#skF_5',A_23)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_31,A_23)
      | v2_struct_0(B_31)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(resolution,[status(thm)],[c_2104,c_14])).

tff(c_2209,plain,(
    ! [B_454,A_455] :
      ( r1_tsep_1('#skF_2',B_454)
      | ~ m1_pre_topc(B_454,'#skF_5')
      | ~ m1_pre_topc('#skF_2',A_455)
      | ~ m1_pre_topc('#skF_5',A_455)
      | ~ m1_pre_topc(B_454,A_455)
      | v2_struct_0(B_454)
      | ~ l1_pre_topc(A_455)
      | ~ v2_pre_topc(A_455)
      | v2_struct_0(A_455) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_48,c_2112])).

tff(c_2211,plain,(
    ! [B_454] :
      ( r1_tsep_1('#skF_2',B_454)
      | ~ m1_pre_topc(B_454,'#skF_5')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | ~ m1_pre_topc(B_454,'#skF_1')
      | v2_struct_0(B_454)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_2209])).

tff(c_2214,plain,(
    ! [B_454] :
      ( r1_tsep_1('#skF_2',B_454)
      | ~ m1_pre_topc(B_454,'#skF_5')
      | ~ m1_pre_topc(B_454,'#skF_1')
      | v2_struct_0(B_454)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_2211])).

tff(c_2216,plain,(
    ! [B_456] :
      ( r1_tsep_1('#skF_2',B_456)
      | ~ m1_pre_topc(B_456,'#skF_5')
      | ~ m1_pre_topc(B_456,'#skF_1')
      | v2_struct_0(B_456) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2214])).

tff(c_2227,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2216,c_28])).

tff(c_2242,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_30,c_2227])).

tff(c_2244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2242])).

tff(c_2246,plain,(
    ~ r1_tsep_1('#skF_2','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1474])).

tff(c_2301,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2298,c_2246])).

tff(c_2312,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_32,c_2301])).

tff(c_2314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2312])).

tff(c_3112,plain,(
    ! [A_636,B_637,B_638,A_639] :
      ( m1_pre_topc(k2_tsep_1(A_636,B_637,B_638),k2_tsep_1(A_639,'#skF_4','#skF_5'))
      | ~ m1_pre_topc(k2_tsep_1(A_636,B_637,B_638),A_639)
      | ~ v2_pre_topc(A_639)
      | r1_tsep_1(B_637,B_638)
      | ~ m1_pre_topc(B_638,A_636)
      | v2_struct_0(B_638)
      | ~ m1_pre_topc(B_637,A_636)
      | v2_struct_0(B_637)
      | ~ l1_pre_topc(A_636)
      | v2_struct_0(A_636)
      | ~ m1_pre_topc('#skF_5',A_639)
      | ~ m1_pre_topc('#skF_4',A_639)
      | ~ l1_pre_topc(A_639)
      | v2_struct_0(A_639)
      | ~ m1_pre_topc(B_638,'#skF_5')
      | ~ m1_pre_topc(B_638,'#skF_1')
      | ~ m1_pre_topc(B_637,'#skF_4')
      | ~ m1_pre_topc(B_637,'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_1477])).

tff(c_26,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_3238,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_5','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_3112,c_26])).

tff(c_3333,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_32,c_42,c_30,c_50,c_38,c_34,c_52,c_3238])).

tff(c_3334,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_28,c_3333])).

tff(c_3337,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_3334])).

tff(c_3340,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_3337])).

tff(c_3342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_3340])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:11:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.77/3.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.77/3.01  
% 8.77/3.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.77/3.01  %$ r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tsep_1 > k3_xboole_0 > #nlpp > u1_struct_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.77/3.01  
% 8.77/3.01  %Foreground sorts:
% 8.77/3.01  
% 8.77/3.01  
% 8.77/3.01  %Background operators:
% 8.77/3.01  
% 8.77/3.01  
% 8.77/3.01  %Foreground operators:
% 8.77/3.01  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.77/3.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.77/3.01  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.77/3.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.77/3.01  tff('#skF_5', type, '#skF_5': $i).
% 8.77/3.01  tff('#skF_2', type, '#skF_2': $i).
% 8.77/3.01  tff('#skF_3', type, '#skF_3': $i).
% 8.77/3.01  tff('#skF_1', type, '#skF_1': $i).
% 8.77/3.01  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.77/3.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.77/3.01  tff('#skF_4', type, '#skF_4': $i).
% 8.77/3.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.77/3.01  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.77/3.01  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 8.77/3.01  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.77/3.01  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 8.77/3.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.77/3.01  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.77/3.01  
% 8.77/3.03  tff(f_176, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(B, D) & m1_pre_topc(C, E)) => (r1_tsep_1(B, C) | m1_pre_topc(k2_tsep_1(A, B, C), k2_tsep_1(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tmap_1)).
% 8.77/3.03  tff(f_85, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k2_tsep_1(A, B, C)) & v1_pre_topc(k2_tsep_1(A, B, C))) & m1_pre_topc(k2_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 8.77/3.03  tff(f_136, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 8.77/3.03  tff(f_63, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k2_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k3_xboole_0(u1_struct_0(B), u1_struct_0(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tsep_1)).
% 8.77/3.03  tff(f_31, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_xboole_1)).
% 8.77/3.03  tff(f_122, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)) | (r1_tsep_1(B, D) & r1_tsep_1(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tmap_1)).
% 8.77/3.03  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.77/3.03  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.77/3.03  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.77/3.03  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.77/3.03  tff(c_46, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.77/3.03  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.77/3.03  tff(c_8, plain, (![A_20, B_21, C_22]: (m1_pre_topc(k2_tsep_1(A_20, B_21, C_22), A_20) | ~m1_pre_topc(C_22, A_20) | v2_struct_0(C_22) | ~m1_pre_topc(B_21, A_20) | v2_struct_0(B_21) | ~l1_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.77/3.03  tff(c_28, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.77/3.03  tff(c_32, plain, (m1_pre_topc('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.77/3.03  tff(c_30, plain, (m1_pre_topc('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.77/3.03  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.77/3.03  tff(c_34, plain, (m1_pre_topc('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.77/3.03  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.77/3.03  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.77/3.03  tff(c_36, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.77/3.03  tff(c_56, plain, (![B_75, C_76, A_77]: (r1_tarski(u1_struct_0(B_75), u1_struct_0(C_76)) | ~m1_pre_topc(B_75, C_76) | ~m1_pre_topc(C_76, A_77) | ~m1_pre_topc(B_75, A_77) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.77/3.03  tff(c_58, plain, (![B_75]: (r1_tarski(u1_struct_0(B_75), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_75, '#skF_4') | ~m1_pre_topc(B_75, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_56])).
% 8.77/3.03  tff(c_71, plain, (![B_75]: (r1_tarski(u1_struct_0(B_75), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_75, '#skF_4') | ~m1_pre_topc(B_75, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_58])).
% 8.77/3.03  tff(c_66, plain, (![B_75]: (r1_tarski(u1_struct_0(B_75), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_75, '#skF_5') | ~m1_pre_topc(B_75, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_56])).
% 8.77/3.03  tff(c_81, plain, (![B_75]: (r1_tarski(u1_struct_0(B_75), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_75, '#skF_5') | ~m1_pre_topc(B_75, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_66])).
% 8.77/3.03  tff(c_10, plain, (![A_20, B_21, C_22]: (v1_pre_topc(k2_tsep_1(A_20, B_21, C_22)) | ~m1_pre_topc(C_22, A_20) | v2_struct_0(C_22) | ~m1_pre_topc(B_21, A_20) | v2_struct_0(B_21) | ~l1_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.77/3.03  tff(c_117, plain, (![A_118, B_119, C_120]: (u1_struct_0(k2_tsep_1(A_118, B_119, C_120))=k3_xboole_0(u1_struct_0(B_119), u1_struct_0(C_120)) | ~m1_pre_topc(k2_tsep_1(A_118, B_119, C_120), A_118) | ~v1_pre_topc(k2_tsep_1(A_118, B_119, C_120)) | v2_struct_0(k2_tsep_1(A_118, B_119, C_120)) | r1_tsep_1(B_119, C_120) | ~m1_pre_topc(C_120, A_118) | v2_struct_0(C_120) | ~m1_pre_topc(B_119, A_118) | v2_struct_0(B_119) | ~l1_pre_topc(A_118) | v2_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.77/3.03  tff(c_121, plain, (![A_121, B_122, C_123]: (u1_struct_0(k2_tsep_1(A_121, B_122, C_123))=k3_xboole_0(u1_struct_0(B_122), u1_struct_0(C_123)) | ~v1_pre_topc(k2_tsep_1(A_121, B_122, C_123)) | v2_struct_0(k2_tsep_1(A_121, B_122, C_123)) | r1_tsep_1(B_122, C_123) | ~m1_pre_topc(C_123, A_121) | v2_struct_0(C_123) | ~m1_pre_topc(B_122, A_121) | v2_struct_0(B_122) | ~l1_pre_topc(A_121) | v2_struct_0(A_121))), inference(resolution, [status(thm)], [c_8, c_117])).
% 8.77/3.03  tff(c_12, plain, (![A_20, B_21, C_22]: (~v2_struct_0(k2_tsep_1(A_20, B_21, C_22)) | ~m1_pre_topc(C_22, A_20) | v2_struct_0(C_22) | ~m1_pre_topc(B_21, A_20) | v2_struct_0(B_21) | ~l1_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.77/3.03  tff(c_188, plain, (![A_124, B_125, C_126]: (u1_struct_0(k2_tsep_1(A_124, B_125, C_126))=k3_xboole_0(u1_struct_0(B_125), u1_struct_0(C_126)) | ~v1_pre_topc(k2_tsep_1(A_124, B_125, C_126)) | r1_tsep_1(B_125, C_126) | ~m1_pre_topc(C_126, A_124) | v2_struct_0(C_126) | ~m1_pre_topc(B_125, A_124) | v2_struct_0(B_125) | ~l1_pre_topc(A_124) | v2_struct_0(A_124))), inference(resolution, [status(thm)], [c_121, c_12])).
% 8.77/3.03  tff(c_192, plain, (![A_127, B_128, C_129]: (u1_struct_0(k2_tsep_1(A_127, B_128, C_129))=k3_xboole_0(u1_struct_0(B_128), u1_struct_0(C_129)) | r1_tsep_1(B_128, C_129) | ~m1_pre_topc(C_129, A_127) | v2_struct_0(C_129) | ~m1_pre_topc(B_128, A_127) | v2_struct_0(B_128) | ~l1_pre_topc(A_127) | v2_struct_0(A_127))), inference(resolution, [status(thm)], [c_10, c_188])).
% 8.77/3.03  tff(c_2, plain, (![A_1, C_3, B_2, D_4]: (r1_tarski(k3_xboole_0(A_1, C_3), k3_xboole_0(B_2, D_4)) | ~r1_tarski(C_3, D_4) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.77/3.03  tff(c_240, plain, (![A_127, C_3, A_1, C_129, B_128]: (r1_tarski(k3_xboole_0(A_1, C_3), u1_struct_0(k2_tsep_1(A_127, B_128, C_129))) | ~r1_tarski(C_3, u1_struct_0(C_129)) | ~r1_tarski(A_1, u1_struct_0(B_128)) | r1_tsep_1(B_128, C_129) | ~m1_pre_topc(C_129, A_127) | v2_struct_0(C_129) | ~m1_pre_topc(B_128, A_127) | v2_struct_0(B_128) | ~l1_pre_topc(A_127) | v2_struct_0(A_127))), inference(superposition, [status(thm), theory('equality')], [c_192, c_2])).
% 8.77/3.03  tff(c_24, plain, (![B_42, C_44, A_38]: (m1_pre_topc(B_42, C_44) | ~r1_tarski(u1_struct_0(B_42), u1_struct_0(C_44)) | ~m1_pre_topc(C_44, A_38) | ~m1_pre_topc(B_42, A_38) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_136])).
% 8.77/3.03  tff(c_440, plain, (![C_160, C_162, B_159, A_158, A_161]: (m1_pre_topc(k2_tsep_1(A_161, B_159, C_160), C_162) | ~r1_tarski(k3_xboole_0(u1_struct_0(B_159), u1_struct_0(C_160)), u1_struct_0(C_162)) | ~m1_pre_topc(C_162, A_158) | ~m1_pre_topc(k2_tsep_1(A_161, B_159, C_160), A_158) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158) | r1_tsep_1(B_159, C_160) | ~m1_pre_topc(C_160, A_161) | v2_struct_0(C_160) | ~m1_pre_topc(B_159, A_161) | v2_struct_0(B_159) | ~l1_pre_topc(A_161) | v2_struct_0(A_161))), inference(superposition, [status(thm), theory('equality')], [c_192, c_24])).
% 8.77/3.03  tff(c_1370, plain, (![C_375, B_374, A_372, B_370, C_373, A_371, A_376]: (m1_pre_topc(k2_tsep_1(A_372, B_374, C_375), k2_tsep_1(A_376, B_370, C_373)) | ~m1_pre_topc(k2_tsep_1(A_376, B_370, C_373), A_371) | ~m1_pre_topc(k2_tsep_1(A_372, B_374, C_375), A_371) | ~l1_pre_topc(A_371) | ~v2_pre_topc(A_371) | r1_tsep_1(B_374, C_375) | ~m1_pre_topc(C_375, A_372) | v2_struct_0(C_375) | ~m1_pre_topc(B_374, A_372) | v2_struct_0(B_374) | ~l1_pre_topc(A_372) | v2_struct_0(A_372) | ~r1_tarski(u1_struct_0(C_375), u1_struct_0(C_373)) | ~r1_tarski(u1_struct_0(B_374), u1_struct_0(B_370)) | r1_tsep_1(B_370, C_373) | ~m1_pre_topc(C_373, A_376) | v2_struct_0(C_373) | ~m1_pre_topc(B_370, A_376) | v2_struct_0(B_370) | ~l1_pre_topc(A_376) | v2_struct_0(A_376))), inference(resolution, [status(thm)], [c_240, c_440])).
% 8.77/3.03  tff(c_1374, plain, (![C_381, A_380, B_379, A_378, B_382, C_377]: (m1_pre_topc(k2_tsep_1(A_378, B_382, C_381), k2_tsep_1(A_380, B_379, C_377)) | ~m1_pre_topc(k2_tsep_1(A_378, B_382, C_381), A_380) | ~v2_pre_topc(A_380) | r1_tsep_1(B_382, C_381) | ~m1_pre_topc(C_381, A_378) | v2_struct_0(C_381) | ~m1_pre_topc(B_382, A_378) | v2_struct_0(B_382) | ~l1_pre_topc(A_378) | v2_struct_0(A_378) | ~r1_tarski(u1_struct_0(C_381), u1_struct_0(C_377)) | ~r1_tarski(u1_struct_0(B_382), u1_struct_0(B_379)) | r1_tsep_1(B_379, C_377) | ~m1_pre_topc(C_377, A_380) | v2_struct_0(C_377) | ~m1_pre_topc(B_379, A_380) | v2_struct_0(B_379) | ~l1_pre_topc(A_380) | v2_struct_0(A_380))), inference(resolution, [status(thm)], [c_8, c_1370])).
% 8.77/3.03  tff(c_1402, plain, (![A_380, B_379, B_75, A_378, B_382]: (m1_pre_topc(k2_tsep_1(A_378, B_382, B_75), k2_tsep_1(A_380, B_379, '#skF_5')) | ~m1_pre_topc(k2_tsep_1(A_378, B_382, B_75), A_380) | ~v2_pre_topc(A_380) | r1_tsep_1(B_382, B_75) | ~m1_pre_topc(B_75, A_378) | v2_struct_0(B_75) | ~m1_pre_topc(B_382, A_378) | v2_struct_0(B_382) | ~l1_pre_topc(A_378) | v2_struct_0(A_378) | ~r1_tarski(u1_struct_0(B_382), u1_struct_0(B_379)) | r1_tsep_1(B_379, '#skF_5') | ~m1_pre_topc('#skF_5', A_380) | v2_struct_0('#skF_5') | ~m1_pre_topc(B_379, A_380) | v2_struct_0(B_379) | ~l1_pre_topc(A_380) | v2_struct_0(A_380) | ~m1_pre_topc(B_75, '#skF_5') | ~m1_pre_topc(B_75, '#skF_1'))), inference(resolution, [status(thm)], [c_81, c_1374])).
% 8.77/3.03  tff(c_1426, plain, (![B_386, A_383, B_385, A_384, B_387]: (m1_pre_topc(k2_tsep_1(A_384, B_386, B_387), k2_tsep_1(A_383, B_385, '#skF_5')) | ~m1_pre_topc(k2_tsep_1(A_384, B_386, B_387), A_383) | ~v2_pre_topc(A_383) | r1_tsep_1(B_386, B_387) | ~m1_pre_topc(B_387, A_384) | v2_struct_0(B_387) | ~m1_pre_topc(B_386, A_384) | v2_struct_0(B_386) | ~l1_pre_topc(A_384) | v2_struct_0(A_384) | ~r1_tarski(u1_struct_0(B_386), u1_struct_0(B_385)) | r1_tsep_1(B_385, '#skF_5') | ~m1_pre_topc('#skF_5', A_383) | ~m1_pre_topc(B_385, A_383) | v2_struct_0(B_385) | ~l1_pre_topc(A_383) | v2_struct_0(A_383) | ~m1_pre_topc(B_387, '#skF_5') | ~m1_pre_topc(B_387, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_36, c_1402])).
% 8.77/3.03  tff(c_1460, plain, (![A_384, B_75, B_387, A_383]: (m1_pre_topc(k2_tsep_1(A_384, B_75, B_387), k2_tsep_1(A_383, '#skF_4', '#skF_5')) | ~m1_pre_topc(k2_tsep_1(A_384, B_75, B_387), A_383) | ~v2_pre_topc(A_383) | r1_tsep_1(B_75, B_387) | ~m1_pre_topc(B_387, A_384) | v2_struct_0(B_387) | ~m1_pre_topc(B_75, A_384) | v2_struct_0(B_75) | ~l1_pre_topc(A_384) | v2_struct_0(A_384) | r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', A_383) | ~m1_pre_topc('#skF_4', A_383) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_383) | v2_struct_0(A_383) | ~m1_pre_topc(B_387, '#skF_5') | ~m1_pre_topc(B_387, '#skF_1') | ~m1_pre_topc(B_75, '#skF_4') | ~m1_pre_topc(B_75, '#skF_1'))), inference(resolution, [status(thm)], [c_71, c_1426])).
% 8.77/3.03  tff(c_1477, plain, (![A_384, B_75, B_387, A_383]: (m1_pre_topc(k2_tsep_1(A_384, B_75, B_387), k2_tsep_1(A_383, '#skF_4', '#skF_5')) | ~m1_pre_topc(k2_tsep_1(A_384, B_75, B_387), A_383) | ~v2_pre_topc(A_383) | r1_tsep_1(B_75, B_387) | ~m1_pre_topc(B_387, A_384) | v2_struct_0(B_387) | ~m1_pre_topc(B_75, A_384) | v2_struct_0(B_75) | ~l1_pre_topc(A_384) | v2_struct_0(A_384) | r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', A_383) | ~m1_pre_topc('#skF_4', A_383) | ~l1_pre_topc(A_383) | v2_struct_0(A_383) | ~m1_pre_topc(B_387, '#skF_5') | ~m1_pre_topc(B_387, '#skF_1') | ~m1_pre_topc(B_75, '#skF_4') | ~m1_pre_topc(B_75, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_40, c_1460])).
% 8.77/3.03  tff(c_2270, plain, (r1_tsep_1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_1477])).
% 8.77/3.03  tff(c_20, plain, (![C_35, D_37, B_31, A_23]: (~r1_tsep_1(C_35, D_37) | r1_tsep_1(B_31, D_37) | ~m1_pre_topc(B_31, C_35) | ~m1_pre_topc(D_37, A_23) | v2_struct_0(D_37) | ~m1_pre_topc(C_35, A_23) | v2_struct_0(C_35) | ~m1_pre_topc(B_31, A_23) | v2_struct_0(B_31) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.77/3.03  tff(c_2272, plain, (![B_31, A_23]: (r1_tsep_1(B_31, '#skF_5') | ~m1_pre_topc(B_31, '#skF_4') | ~m1_pre_topc('#skF_5', A_23) | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', A_23) | v2_struct_0('#skF_4') | ~m1_pre_topc(B_31, A_23) | v2_struct_0(B_31) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(resolution, [status(thm)], [c_2270, c_20])).
% 8.77/3.03  tff(c_2291, plain, (![B_481, A_482]: (r1_tsep_1(B_481, '#skF_5') | ~m1_pre_topc(B_481, '#skF_4') | ~m1_pre_topc('#skF_5', A_482) | ~m1_pre_topc('#skF_4', A_482) | ~m1_pre_topc(B_481, A_482) | v2_struct_0(B_481) | ~l1_pre_topc(A_482) | ~v2_pre_topc(A_482) | v2_struct_0(A_482))), inference(negUnitSimplification, [status(thm)], [c_40, c_36, c_2272])).
% 8.77/3.03  tff(c_2293, plain, (![B_481]: (r1_tsep_1(B_481, '#skF_5') | ~m1_pre_topc(B_481, '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_481, '#skF_1') | v2_struct_0(B_481) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_2291])).
% 8.77/3.03  tff(c_2296, plain, (![B_481]: (r1_tsep_1(B_481, '#skF_5') | ~m1_pre_topc(B_481, '#skF_4') | ~m1_pre_topc(B_481, '#skF_1') | v2_struct_0(B_481) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_38, c_2293])).
% 8.77/3.03  tff(c_2298, plain, (![B_483]: (r1_tsep_1(B_483, '#skF_5') | ~m1_pre_topc(B_483, '#skF_4') | ~m1_pre_topc(B_483, '#skF_1') | v2_struct_0(B_483))), inference(negUnitSimplification, [status(thm)], [c_54, c_2296])).
% 8.77/3.03  tff(c_60, plain, (![B_75]: (r1_tarski(u1_struct_0(B_75), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_75, '#skF_2') | ~m1_pre_topc(B_75, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_56])).
% 8.77/3.03  tff(c_74, plain, (![B_75]: (r1_tarski(u1_struct_0(B_75), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_75, '#skF_2') | ~m1_pre_topc(B_75, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_60])).
% 8.77/3.03  tff(c_1458, plain, (![A_384, B_75, B_387, A_383]: (m1_pre_topc(k2_tsep_1(A_384, B_75, B_387), k2_tsep_1(A_383, '#skF_2', '#skF_5')) | ~m1_pre_topc(k2_tsep_1(A_384, B_75, B_387), A_383) | ~v2_pre_topc(A_383) | r1_tsep_1(B_75, B_387) | ~m1_pre_topc(B_387, A_384) | v2_struct_0(B_387) | ~m1_pre_topc(B_75, A_384) | v2_struct_0(B_75) | ~l1_pre_topc(A_384) | v2_struct_0(A_384) | r1_tsep_1('#skF_2', '#skF_5') | ~m1_pre_topc('#skF_5', A_383) | ~m1_pre_topc('#skF_2', A_383) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_383) | v2_struct_0(A_383) | ~m1_pre_topc(B_387, '#skF_5') | ~m1_pre_topc(B_387, '#skF_1') | ~m1_pre_topc(B_75, '#skF_2') | ~m1_pre_topc(B_75, '#skF_1'))), inference(resolution, [status(thm)], [c_74, c_1426])).
% 8.77/3.03  tff(c_1474, plain, (![A_384, B_75, B_387, A_383]: (m1_pre_topc(k2_tsep_1(A_384, B_75, B_387), k2_tsep_1(A_383, '#skF_2', '#skF_5')) | ~m1_pre_topc(k2_tsep_1(A_384, B_75, B_387), A_383) | ~v2_pre_topc(A_383) | r1_tsep_1(B_75, B_387) | ~m1_pre_topc(B_387, A_384) | v2_struct_0(B_387) | ~m1_pre_topc(B_75, A_384) | v2_struct_0(B_75) | ~l1_pre_topc(A_384) | v2_struct_0(A_384) | r1_tsep_1('#skF_2', '#skF_5') | ~m1_pre_topc('#skF_5', A_383) | ~m1_pre_topc('#skF_2', A_383) | ~l1_pre_topc(A_383) | v2_struct_0(A_383) | ~m1_pre_topc(B_387, '#skF_5') | ~m1_pre_topc(B_387, '#skF_1') | ~m1_pre_topc(B_75, '#skF_2') | ~m1_pre_topc(B_75, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_48, c_1458])).
% 8.77/3.03  tff(c_2104, plain, (r1_tsep_1('#skF_2', '#skF_5')), inference(splitLeft, [status(thm)], [c_1474])).
% 8.77/3.03  tff(c_14, plain, (![D_37, C_35, B_31, A_23]: (~r1_tsep_1(D_37, C_35) | r1_tsep_1(D_37, B_31) | ~m1_pre_topc(B_31, C_35) | ~m1_pre_topc(D_37, A_23) | v2_struct_0(D_37) | ~m1_pre_topc(C_35, A_23) | v2_struct_0(C_35) | ~m1_pre_topc(B_31, A_23) | v2_struct_0(B_31) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.77/3.03  tff(c_2112, plain, (![B_31, A_23]: (r1_tsep_1('#skF_2', B_31) | ~m1_pre_topc(B_31, '#skF_5') | ~m1_pre_topc('#skF_2', A_23) | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_5', A_23) | v2_struct_0('#skF_5') | ~m1_pre_topc(B_31, A_23) | v2_struct_0(B_31) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(resolution, [status(thm)], [c_2104, c_14])).
% 8.77/3.03  tff(c_2209, plain, (![B_454, A_455]: (r1_tsep_1('#skF_2', B_454) | ~m1_pre_topc(B_454, '#skF_5') | ~m1_pre_topc('#skF_2', A_455) | ~m1_pre_topc('#skF_5', A_455) | ~m1_pre_topc(B_454, A_455) | v2_struct_0(B_454) | ~l1_pre_topc(A_455) | ~v2_pre_topc(A_455) | v2_struct_0(A_455))), inference(negUnitSimplification, [status(thm)], [c_36, c_48, c_2112])).
% 8.77/3.03  tff(c_2211, plain, (![B_454]: (r1_tsep_1('#skF_2', B_454) | ~m1_pre_topc(B_454, '#skF_5') | ~m1_pre_topc('#skF_2', '#skF_1') | ~m1_pre_topc(B_454, '#skF_1') | v2_struct_0(B_454) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_2209])).
% 8.77/3.03  tff(c_2214, plain, (![B_454]: (r1_tsep_1('#skF_2', B_454) | ~m1_pre_topc(B_454, '#skF_5') | ~m1_pre_topc(B_454, '#skF_1') | v2_struct_0(B_454) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_2211])).
% 8.77/3.03  tff(c_2216, plain, (![B_456]: (r1_tsep_1('#skF_2', B_456) | ~m1_pre_topc(B_456, '#skF_5') | ~m1_pre_topc(B_456, '#skF_1') | v2_struct_0(B_456))), inference(negUnitSimplification, [status(thm)], [c_54, c_2214])).
% 8.77/3.03  tff(c_2227, plain, (~m1_pre_topc('#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2216, c_28])).
% 8.77/3.03  tff(c_2242, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_30, c_2227])).
% 8.77/3.03  tff(c_2244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_2242])).
% 8.77/3.03  tff(c_2246, plain, (~r1_tsep_1('#skF_2', '#skF_5')), inference(splitRight, [status(thm)], [c_1474])).
% 8.77/3.03  tff(c_2301, plain, (~m1_pre_topc('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_2298, c_2246])).
% 8.77/3.03  tff(c_2312, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_32, c_2301])).
% 8.77/3.03  tff(c_2314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_2312])).
% 8.77/3.03  tff(c_3112, plain, (![A_636, B_637, B_638, A_639]: (m1_pre_topc(k2_tsep_1(A_636, B_637, B_638), k2_tsep_1(A_639, '#skF_4', '#skF_5')) | ~m1_pre_topc(k2_tsep_1(A_636, B_637, B_638), A_639) | ~v2_pre_topc(A_639) | r1_tsep_1(B_637, B_638) | ~m1_pre_topc(B_638, A_636) | v2_struct_0(B_638) | ~m1_pre_topc(B_637, A_636) | v2_struct_0(B_637) | ~l1_pre_topc(A_636) | v2_struct_0(A_636) | ~m1_pre_topc('#skF_5', A_639) | ~m1_pre_topc('#skF_4', A_639) | ~l1_pre_topc(A_639) | v2_struct_0(A_639) | ~m1_pre_topc(B_638, '#skF_5') | ~m1_pre_topc(B_638, '#skF_1') | ~m1_pre_topc(B_637, '#skF_4') | ~m1_pre_topc(B_637, '#skF_1'))), inference(splitRight, [status(thm)], [c_1477])).
% 8.77/3.03  tff(c_26, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.77/3.03  tff(c_3238, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | ~v2_pre_topc('#skF_1') | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_5', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_3112, c_26])).
% 8.77/3.03  tff(c_3333, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_32, c_42, c_30, c_50, c_38, c_34, c_52, c_3238])).
% 8.77/3.03  tff(c_3334, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_44, c_28, c_3333])).
% 8.77/3.03  tff(c_3337, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_8, c_3334])).
% 8.77/3.03  tff(c_3340, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_42, c_3337])).
% 8.77/3.03  tff(c_3342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_44, c_3340])).
% 8.77/3.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.77/3.03  
% 8.77/3.03  Inference rules
% 8.77/3.03  ----------------------
% 8.77/3.03  #Ref     : 2
% 8.77/3.03  #Sup     : 866
% 8.77/3.03  #Fact    : 0
% 8.77/3.03  #Define  : 0
% 8.77/3.03  #Split   : 16
% 8.77/3.03  #Chain   : 0
% 8.77/3.03  #Close   : 0
% 8.77/3.03  
% 8.77/3.03  Ordering : KBO
% 8.77/3.03  
% 8.77/3.03  Simplification rules
% 8.77/3.03  ----------------------
% 8.77/3.03  #Subsume      : 274
% 8.77/3.03  #Demod        : 303
% 8.77/3.03  #Tautology    : 16
% 8.77/3.03  #SimpNegUnit  : 269
% 8.77/3.03  #BackRed      : 0
% 8.77/3.03  
% 8.77/3.03  #Partial instantiations: 0
% 8.77/3.03  #Strategies tried      : 1
% 8.77/3.03  
% 8.77/3.03  Timing (in seconds)
% 8.77/3.03  ----------------------
% 8.77/3.03  Preprocessing        : 0.32
% 8.77/3.03  Parsing              : 0.17
% 8.77/3.03  CNF conversion       : 0.03
% 8.77/3.03  Main loop            : 1.95
% 8.77/3.03  Inferencing          : 0.53
% 8.77/3.03  Reduction            : 0.37
% 8.77/3.03  Demodulation         : 0.24
% 8.77/3.03  BG Simplification    : 0.06
% 8.77/3.03  Subsumption          : 0.90
% 8.77/3.03  Abstraction          : 0.07
% 8.77/3.03  MUC search           : 0.00
% 8.77/3.03  Cooper               : 0.00
% 8.77/3.03  Total                : 2.31
% 8.77/3.03  Index Insertion      : 0.00
% 8.77/3.03  Index Deletion       : 0.00
% 8.77/3.03  Index Matching       : 0.00
% 8.77/3.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
