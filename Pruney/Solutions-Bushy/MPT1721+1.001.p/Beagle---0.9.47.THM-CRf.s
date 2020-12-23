%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1721+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:18 EST 2020

% Result     : Theorem 15.95s
% Output     : CNFRefutation 16.11s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 228 expanded)
%              Number of leaves         :   25 (  96 expanded)
%              Depth                    :   21
%              Number of atoms          :  280 (1374 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tsep_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_136,negated_conjecture,(
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
                   => ( ( m1_pre_topc(B,D)
                        & m1_pre_topc(C,D) )
                     => ( r1_tsep_1(B,C)
                        | m1_pre_topc(k2_tsep_1(A,B,C),D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tmap_1)).

tff(f_78,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

tff(f_80,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_56,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_38,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_8,plain,(
    ! [A_16,B_17,C_18] :
      ( v1_pre_topc(k2_tsep_1(A_16,B_17,C_18))
      | ~ m1_pre_topc(C_18,A_16)
      | v2_struct_0(C_18)
      | ~ m1_pre_topc(B_17,A_16)
      | v2_struct_0(B_17)
      | ~ l1_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_6,plain,(
    ! [A_16,B_17,C_18] :
      ( m1_pre_topc(k2_tsep_1(A_16,B_17,C_18),A_16)
      | ~ m1_pre_topc(C_18,A_16)
      | v2_struct_0(C_18)
      | ~ m1_pre_topc(B_17,A_16)
      | v2_struct_0(B_17)
      | ~ l1_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [A_19] : k2_xboole_0(A_19,A_19) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_56,plain,(
    ! [A_46,B_47,C_48] : r1_tarski(k3_xboole_0(A_46,B_47),k2_xboole_0(A_46,C_48)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_59,plain,(
    ! [A_19,B_47] : r1_tarski(k3_xboole_0(A_19,B_47),A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_56])).

tff(c_882,plain,(
    ! [A_186,B_187,C_188] :
      ( u1_struct_0(k2_tsep_1(A_186,B_187,C_188)) = k3_xboole_0(u1_struct_0(B_187),u1_struct_0(C_188))
      | ~ m1_pre_topc(k2_tsep_1(A_186,B_187,C_188),A_186)
      | ~ v1_pre_topc(k2_tsep_1(A_186,B_187,C_188))
      | v2_struct_0(k2_tsep_1(A_186,B_187,C_188))
      | r1_tsep_1(B_187,C_188)
      | ~ m1_pre_topc(C_188,A_186)
      | v2_struct_0(C_188)
      | ~ m1_pre_topc(B_187,A_186)
      | v2_struct_0(B_187)
      | ~ l1_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1151,plain,(
    ! [A_220,B_221,C_222] :
      ( u1_struct_0(k2_tsep_1(A_220,B_221,C_222)) = k3_xboole_0(u1_struct_0(B_221),u1_struct_0(C_222))
      | ~ v1_pre_topc(k2_tsep_1(A_220,B_221,C_222))
      | v2_struct_0(k2_tsep_1(A_220,B_221,C_222))
      | r1_tsep_1(B_221,C_222)
      | ~ m1_pre_topc(C_222,A_220)
      | v2_struct_0(C_222)
      | ~ m1_pre_topc(B_221,A_220)
      | v2_struct_0(B_221)
      | ~ l1_pre_topc(A_220)
      | v2_struct_0(A_220) ) ),
    inference(resolution,[status(thm)],[c_6,c_882])).

tff(c_20,plain,(
    ! [B_31,C_33,A_27] :
      ( m1_pre_topc(B_31,C_33)
      | ~ r1_tarski(u1_struct_0(B_31),u1_struct_0(C_33))
      | ~ m1_pre_topc(C_33,A_27)
      | ~ m1_pre_topc(B_31,A_27)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2542,plain,(
    ! [C_396,C_397,B_399,A_400,A_398] :
      ( m1_pre_topc(k2_tsep_1(A_398,B_399,C_397),C_396)
      | ~ r1_tarski(k3_xboole_0(u1_struct_0(B_399),u1_struct_0(C_397)),u1_struct_0(C_396))
      | ~ m1_pre_topc(C_396,A_400)
      | ~ m1_pre_topc(k2_tsep_1(A_398,B_399,C_397),A_400)
      | ~ l1_pre_topc(A_400)
      | ~ v2_pre_topc(A_400)
      | ~ v1_pre_topc(k2_tsep_1(A_398,B_399,C_397))
      | v2_struct_0(k2_tsep_1(A_398,B_399,C_397))
      | r1_tsep_1(B_399,C_397)
      | ~ m1_pre_topc(C_397,A_398)
      | v2_struct_0(C_397)
      | ~ m1_pre_topc(B_399,A_398)
      | v2_struct_0(B_399)
      | ~ l1_pre_topc(A_398)
      | v2_struct_0(A_398) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1151,c_20])).

tff(c_9750,plain,(
    ! [A_1064,B_1065,C_1066,A_1067] :
      ( m1_pre_topc(k2_tsep_1(A_1064,B_1065,C_1066),B_1065)
      | ~ m1_pre_topc(B_1065,A_1067)
      | ~ m1_pre_topc(k2_tsep_1(A_1064,B_1065,C_1066),A_1067)
      | ~ l1_pre_topc(A_1067)
      | ~ v2_pre_topc(A_1067)
      | ~ v1_pre_topc(k2_tsep_1(A_1064,B_1065,C_1066))
      | v2_struct_0(k2_tsep_1(A_1064,B_1065,C_1066))
      | r1_tsep_1(B_1065,C_1066)
      | ~ m1_pre_topc(C_1066,A_1064)
      | v2_struct_0(C_1066)
      | ~ m1_pre_topc(B_1065,A_1064)
      | v2_struct_0(B_1065)
      | ~ l1_pre_topc(A_1064)
      | v2_struct_0(A_1064) ) ),
    inference(resolution,[status(thm)],[c_59,c_2542])).

tff(c_17748,plain,(
    ! [A_2114,B_2115,C_2116] :
      ( m1_pre_topc(k2_tsep_1(A_2114,B_2115,C_2116),B_2115)
      | ~ v2_pre_topc(A_2114)
      | ~ v1_pre_topc(k2_tsep_1(A_2114,B_2115,C_2116))
      | v2_struct_0(k2_tsep_1(A_2114,B_2115,C_2116))
      | r1_tsep_1(B_2115,C_2116)
      | ~ m1_pre_topc(C_2116,A_2114)
      | v2_struct_0(C_2116)
      | ~ m1_pre_topc(B_2115,A_2114)
      | v2_struct_0(B_2115)
      | ~ l1_pre_topc(A_2114)
      | v2_struct_0(A_2114) ) ),
    inference(resolution,[status(thm)],[c_6,c_9750])).

tff(c_30,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_28,plain,(
    m1_pre_topc('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_139,plain,(
    ! [B_84,C_85,A_86] :
      ( r1_tarski(u1_struct_0(B_84),u1_struct_0(C_85))
      | ~ m1_pre_topc(B_84,C_85)
      | ~ m1_pre_topc(C_85,A_86)
      | ~ m1_pre_topc(B_84,A_86)
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_147,plain,(
    ! [B_84] :
      ( r1_tarski(u1_struct_0(B_84),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_84,'#skF_2')
      | ~ m1_pre_topc(B_84,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_139])).

tff(c_157,plain,(
    ! [B_84] :
      ( r1_tarski(u1_struct_0(B_84),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_84,'#skF_2')
      | ~ m1_pre_topc(B_84,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_147])).

tff(c_145,plain,(
    ! [B_84] :
      ( r1_tarski(u1_struct_0(B_84),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_84,'#skF_4')
      | ~ m1_pre_topc(B_84,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_139])).

tff(c_161,plain,(
    ! [B_87] :
      ( r1_tarski(u1_struct_0(B_87),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_87,'#skF_4')
      | ~ m1_pre_topc(B_87,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_145])).

tff(c_14,plain,(
    ! [A_21,C_23,B_22] :
      ( r1_tarski(A_21,C_23)
      | ~ r1_tarski(B_22,C_23)
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_281,plain,(
    ! [A_120,B_121] :
      ( r1_tarski(A_120,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_120,u1_struct_0(B_121))
      | ~ m1_pre_topc(B_121,'#skF_4')
      | ~ m1_pre_topc(B_121,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_161,c_14])).

tff(c_291,plain,(
    ! [B_84] :
      ( r1_tarski(u1_struct_0(B_84),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_2','#skF_4')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | ~ m1_pre_topc(B_84,'#skF_2')
      | ~ m1_pre_topc(B_84,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_157,c_281])).

tff(c_329,plain,(
    ! [B_123] :
      ( r1_tarski(u1_struct_0(B_123),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_123,'#skF_2')
      | ~ m1_pre_topc(B_123,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28,c_291])).

tff(c_2075,plain,(
    ! [B_328,A_329] :
      ( m1_pre_topc(B_328,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_329)
      | ~ m1_pre_topc(B_328,A_329)
      | ~ l1_pre_topc(A_329)
      | ~ v2_pre_topc(A_329)
      | ~ m1_pre_topc(B_328,'#skF_2')
      | ~ m1_pre_topc(B_328,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_329,c_20])).

tff(c_2077,plain,(
    ! [B_328] :
      ( m1_pre_topc(B_328,'#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_pre_topc(B_328,'#skF_2')
      | ~ m1_pre_topc(B_328,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_2075])).

tff(c_2080,plain,(
    ! [B_328] :
      ( m1_pre_topc(B_328,'#skF_4')
      | ~ m1_pre_topc(B_328,'#skF_2')
      | ~ m1_pre_topc(B_328,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_2077])).

tff(c_17828,plain,(
    ! [A_2114,C_2116] :
      ( m1_pre_topc(k2_tsep_1(A_2114,'#skF_2',C_2116),'#skF_4')
      | ~ m1_pre_topc(k2_tsep_1(A_2114,'#skF_2',C_2116),'#skF_1')
      | ~ v2_pre_topc(A_2114)
      | ~ v1_pre_topc(k2_tsep_1(A_2114,'#skF_2',C_2116))
      | v2_struct_0(k2_tsep_1(A_2114,'#skF_2',C_2116))
      | r1_tsep_1('#skF_2',C_2116)
      | ~ m1_pre_topc(C_2116,A_2114)
      | v2_struct_0(C_2116)
      | ~ m1_pre_topc('#skF_2',A_2114)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_2114)
      | v2_struct_0(A_2114) ) ),
    inference(resolution,[status(thm)],[c_17748,c_2080])).

tff(c_17914,plain,(
    ! [A_2119,C_2120] :
      ( m1_pre_topc(k2_tsep_1(A_2119,'#skF_2',C_2120),'#skF_4')
      | ~ m1_pre_topc(k2_tsep_1(A_2119,'#skF_2',C_2120),'#skF_1')
      | ~ v2_pre_topc(A_2119)
      | ~ v1_pre_topc(k2_tsep_1(A_2119,'#skF_2',C_2120))
      | v2_struct_0(k2_tsep_1(A_2119,'#skF_2',C_2120))
      | r1_tsep_1('#skF_2',C_2120)
      | ~ m1_pre_topc(C_2120,A_2119)
      | v2_struct_0(C_2120)
      | ~ m1_pre_topc('#skF_2',A_2119)
      | ~ l1_pre_topc(A_2119)
      | v2_struct_0(A_2119) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_17828])).

tff(c_17918,plain,(
    ! [C_18] :
      ( m1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_18),'#skF_4')
      | ~ v2_pre_topc('#skF_1')
      | ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_18))
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2',C_18))
      | r1_tsep_1('#skF_2',C_18)
      | ~ m1_pre_topc(C_18,'#skF_1')
      | v2_struct_0(C_18)
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6,c_17914])).

tff(c_17921,plain,(
    ! [C_18] :
      ( m1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_18),'#skF_4')
      | ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_18))
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2',C_18))
      | r1_tsep_1('#skF_2',C_18)
      | ~ m1_pre_topc(C_18,'#skF_1')
      | v2_struct_0(C_18)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_44,c_17918])).

tff(c_17923,plain,(
    ! [C_2121] :
      ( m1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_2121),'#skF_4')
      | ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_2121))
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2',C_2121))
      | r1_tsep_1('#skF_2',C_2121)
      | ~ m1_pre_topc(C_2121,'#skF_1')
      | v2_struct_0(C_2121) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_17921])).

tff(c_22,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_17951,plain,
    ( ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_17923,c_22])).

tff(c_17991,plain,
    ( ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_17951])).

tff(c_17992,plain,
    ( ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_24,c_17991])).

tff(c_17993,plain,(
    ~ v1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_17992])).

tff(c_17996,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_17993])).

tff(c_17999,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_34,c_17996])).

tff(c_18001,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_36,c_17999])).

tff(c_18002,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_17992])).

tff(c_10,plain,(
    ! [A_16,B_17,C_18] :
      ( ~ v2_struct_0(k2_tsep_1(A_16,B_17,C_18))
      | ~ m1_pre_topc(C_18,A_16)
      | v2_struct_0(C_18)
      | ~ m1_pre_topc(B_17,A_16)
      | v2_struct_0(B_17)
      | ~ l1_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18006,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18002,c_10])).

tff(c_18009,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_34,c_18006])).

tff(c_18011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_36,c_18009])).

%------------------------------------------------------------------------------
