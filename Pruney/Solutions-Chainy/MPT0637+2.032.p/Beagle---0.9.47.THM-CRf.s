%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:28 EST 2020

% Result     : Theorem 14.28s
% Output     : CNFRefutation 14.28s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 299 expanded)
%              Number of leaves         :   31 ( 117 expanded)
%              Depth                    :   17
%              Number of atoms          :  200 ( 504 expanded)
%              Number of equality atoms :   61 ( 163 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_49,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_20,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    ! [A_29] : k1_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_347,plain,(
    ! [B_76,A_77] :
      ( k7_relat_1(B_76,k3_xboole_0(k1_relat_1(B_76),A_77)) = k7_relat_1(B_76,A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_216,plain,(
    ! [A_64,B_65] :
      ( k5_relat_1(k6_relat_1(A_64),B_65) = k7_relat_1(B_65,A_64)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    ! [B_31,A_30] :
      ( r1_tarski(k5_relat_1(B_31,k6_relat_1(A_30)),B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_226,plain,(
    ! [A_30,A_64] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_30),A_64),k6_relat_1(A_64))
      | ~ v1_relat_1(k6_relat_1(A_64))
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_34])).

tff(c_255,plain,(
    ! [A_30,A_64] : r1_tarski(k7_relat_1(k6_relat_1(A_30),A_64),k6_relat_1(A_64)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_226])).

tff(c_354,plain,(
    ! [A_30,A_77] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_30),A_77),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_30)),A_77)))
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_255])).

tff(c_374,plain,(
    ! [A_30,A_77] : r1_tarski(k7_relat_1(k6_relat_1(A_30),A_77),k6_relat_1(k3_xboole_0(A_30,A_77))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_28,c_354])).

tff(c_30,plain,(
    ! [A_29] : k2_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_38,plain,(
    ! [A_34] :
      ( k5_relat_1(A_34,k6_relat_1(k2_relat_1(A_34))) = A_34
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_234,plain,(
    ! [A_64] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_64))),A_64) = k6_relat_1(A_64)
      | ~ v1_relat_1(k6_relat_1(A_64))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_64)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_38])).

tff(c_259,plain,(
    ! [A_64] : k7_relat_1(k6_relat_1(A_64),A_64) = k6_relat_1(A_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_30,c_234])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_285,plain,(
    ! [A_69,B_70] :
      ( k5_relat_1(k6_relat_1(A_69),B_70) = B_70
      | ~ r1_tarski(k1_relat_1(B_70),A_69)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_288,plain,(
    ! [A_69,A_29] :
      ( k5_relat_1(k6_relat_1(A_69),k6_relat_1(A_29)) = k6_relat_1(A_29)
      | ~ r1_tarski(A_29,A_69)
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_285])).

tff(c_601,plain,(
    ! [A_98,A_99] :
      ( k5_relat_1(k6_relat_1(A_98),k6_relat_1(A_99)) = k6_relat_1(A_99)
      | ~ r1_tarski(A_99,A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_288])).

tff(c_40,plain,(
    ! [A_35,B_36] :
      ( k5_relat_1(k6_relat_1(A_35),B_36) = k7_relat_1(B_36,A_35)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_614,plain,(
    ! [A_99,A_98] :
      ( k7_relat_1(k6_relat_1(A_99),A_98) = k6_relat_1(A_99)
      | ~ v1_relat_1(k6_relat_1(A_99))
      | ~ r1_tarski(A_99,A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_40])).

tff(c_687,plain,(
    ! [A_102,A_103] :
      ( k7_relat_1(k6_relat_1(A_102),A_103) = k6_relat_1(A_102)
      | ~ r1_tarski(A_102,A_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_614])).

tff(c_696,plain,(
    ! [A_102,A_103] :
      ( r1_tarski(k6_relat_1(A_102),k6_relat_1(k3_xboole_0(A_102,A_103)))
      | ~ r1_tarski(A_102,A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_687,c_374])).

tff(c_620,plain,(
    ! [A_99,A_98] :
      ( r1_tarski(k6_relat_1(A_99),k6_relat_1(A_98))
      | ~ v1_relat_1(k6_relat_1(A_98))
      | ~ r1_tarski(A_99,A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_34])).

tff(c_683,plain,(
    ! [A_100,A_101] :
      ( r1_tarski(k6_relat_1(A_100),k6_relat_1(A_101))
      | ~ r1_tarski(A_100,A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_620])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1438,plain,(
    ! [A_137,A_136] :
      ( k6_relat_1(A_137) = k6_relat_1(A_136)
      | ~ r1_tarski(k6_relat_1(A_136),k6_relat_1(A_137))
      | ~ r1_tarski(A_137,A_136) ) ),
    inference(resolution,[status(thm)],[c_683,c_4])).

tff(c_1447,plain,(
    ! [A_102,A_103] :
      ( k6_relat_1(k3_xboole_0(A_102,A_103)) = k6_relat_1(A_102)
      | ~ r1_tarski(k3_xboole_0(A_102,A_103),A_102)
      | ~ r1_tarski(A_102,A_103) ) ),
    inference(resolution,[status(thm)],[c_696,c_1438])).

tff(c_1807,plain,(
    ! [A_143,A_144] :
      ( k6_relat_1(k3_xboole_0(A_143,A_144)) = k6_relat_1(A_143)
      | ~ r1_tarski(A_143,A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1447])).

tff(c_1916,plain,(
    ! [A_143,A_144] :
      ( k3_xboole_0(A_143,A_144) = k2_relat_1(k6_relat_1(A_143))
      | ~ r1_tarski(A_143,A_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1807,c_30])).

tff(c_1950,plain,(
    ! [A_145,A_146] :
      ( k3_xboole_0(A_145,A_146) = A_145
      | ~ r1_tarski(A_145,A_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1916])).

tff(c_2015,plain,(
    ! [A_147,B_148] : k3_xboole_0(k3_xboole_0(A_147,B_148),A_147) = k3_xboole_0(A_147,B_148) ),
    inference(resolution,[status(thm)],[c_10,c_1950])).

tff(c_371,plain,(
    ! [A_29,A_77] :
      ( k7_relat_1(k6_relat_1(A_29),k3_xboole_0(A_29,A_77)) = k7_relat_1(k6_relat_1(A_29),A_77)
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_347])).

tff(c_377,plain,(
    ! [A_29,A_77] : k7_relat_1(k6_relat_1(A_29),k3_xboole_0(A_29,A_77)) = k7_relat_1(k6_relat_1(A_29),A_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_371])).

tff(c_2052,plain,(
    ! [A_147,B_148] : k7_relat_1(k6_relat_1(k3_xboole_0(A_147,B_148)),k3_xboole_0(A_147,B_148)) = k7_relat_1(k6_relat_1(k3_xboole_0(A_147,B_148)),A_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_2015,c_377])).

tff(c_2120,plain,(
    ! [A_147,B_148] : k7_relat_1(k6_relat_1(k3_xboole_0(A_147,B_148)),A_147) = k6_relat_1(k3_xboole_0(A_147,B_148)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_2052])).

tff(c_24,plain,(
    ! [B_21,A_20] :
      ( k7_relat_1(B_21,k3_xboole_0(k1_relat_1(B_21),A_20)) = k7_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_763,plain,(
    ! [A_104,A_105] : k7_relat_1(k6_relat_1(A_104),k3_xboole_0(A_104,A_105)) = k7_relat_1(k6_relat_1(A_104),A_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_371])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k5_relat_1(A_14,B_15))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_222,plain,(
    ! [B_65,A_64] :
      ( v1_relat_1(k7_relat_1(B_65,A_64))
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(k6_relat_1(A_64))
      | ~ v1_relat_1(B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_18])).

tff(c_253,plain,(
    ! [B_65,A_64] :
      ( v1_relat_1(k7_relat_1(B_65,A_64))
      | ~ v1_relat_1(B_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_222])).

tff(c_787,plain,(
    ! [A_104,A_105] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_104),A_105))
      | ~ v1_relat_1(k6_relat_1(A_104)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_253])).

tff(c_809,plain,(
    ! [A_104,A_105] : v1_relat_1(k7_relat_1(k6_relat_1(A_104),A_105)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_787])).

tff(c_133,plain,(
    ! [A_53] :
      ( k5_relat_1(A_53,k6_relat_1(k2_relat_1(A_53))) = A_53
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_146,plain,(
    ! [A_29] :
      ( k5_relat_1(k6_relat_1(A_29),k6_relat_1(A_29)) = k6_relat_1(A_29)
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_133])).

tff(c_152,plain,(
    ! [A_29] : k5_relat_1(k6_relat_1(A_29),k6_relat_1(A_29)) = k6_relat_1(A_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_146])).

tff(c_508,plain,(
    ! [A_91,B_92,C_93] :
      ( k5_relat_1(k5_relat_1(A_91,B_92),C_93) = k5_relat_1(A_91,k5_relat_1(B_92,C_93))
      | ~ v1_relat_1(C_93)
      | ~ v1_relat_1(B_92)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_537,plain,(
    ! [A_35,B_36,C_93] :
      ( k5_relat_1(k6_relat_1(A_35),k5_relat_1(B_36,C_93)) = k5_relat_1(k7_relat_1(B_36,A_35),C_93)
      | ~ v1_relat_1(C_93)
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(k6_relat_1(A_35))
      | ~ v1_relat_1(B_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_508])).

tff(c_1710,plain,(
    ! [A_140,B_141,C_142] :
      ( k5_relat_1(k6_relat_1(A_140),k5_relat_1(B_141,C_142)) = k5_relat_1(k7_relat_1(B_141,A_140),C_142)
      | ~ v1_relat_1(C_142)
      | ~ v1_relat_1(B_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_537])).

tff(c_1779,plain,(
    ! [A_29,A_140] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_29),A_140),k6_relat_1(A_29)) = k5_relat_1(k6_relat_1(A_140),k6_relat_1(A_29))
      | ~ v1_relat_1(k6_relat_1(A_29))
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_1710])).

tff(c_8871,plain,(
    ! [A_253,A_254] : k5_relat_1(k7_relat_1(k6_relat_1(A_253),A_254),k6_relat_1(A_253)) = k5_relat_1(k6_relat_1(A_254),k6_relat_1(A_253)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_1779])).

tff(c_8901,plain,(
    ! [A_254,A_253] :
      ( v1_relat_1(k5_relat_1(k6_relat_1(A_254),k6_relat_1(A_253)))
      | ~ v1_relat_1(k6_relat_1(A_253))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_253),A_254)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8871,c_18])).

tff(c_8994,plain,(
    ! [A_254,A_253] : v1_relat_1(k5_relat_1(k6_relat_1(A_254),k6_relat_1(A_253))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_809,c_20,c_8901])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_800,plain,(
    ! [B_2,A_1] : k7_relat_1(k6_relat_1(B_2),k3_xboole_0(A_1,B_2)) = k7_relat_1(k6_relat_1(B_2),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_763])).

tff(c_431,plain,(
    ! [C_85,A_86,B_87] :
      ( k7_relat_1(k7_relat_1(C_85,A_86),B_87) = k7_relat_1(C_85,k3_xboole_0(A_86,B_87))
      | ~ v1_relat_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2393,plain,(
    ! [B_153,A_154,B_155] :
      ( k7_relat_1(B_153,k3_xboole_0(k3_xboole_0(k1_relat_1(B_153),A_154),B_155)) = k7_relat_1(k7_relat_1(B_153,A_154),B_155)
      | ~ v1_relat_1(B_153)
      | ~ v1_relat_1(B_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_431])).

tff(c_2479,plain,(
    ! [B_2,A_154] :
      ( k7_relat_1(k6_relat_1(B_2),k3_xboole_0(k1_relat_1(k6_relat_1(B_2)),A_154)) = k7_relat_1(k7_relat_1(k6_relat_1(B_2),A_154),B_2)
      | ~ v1_relat_1(k6_relat_1(B_2))
      | ~ v1_relat_1(k6_relat_1(B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_800,c_2393])).

tff(c_2530,plain,(
    ! [B_2,A_154] : k7_relat_1(k7_relat_1(k6_relat_1(B_2),A_154),B_2) = k7_relat_1(k6_relat_1(B_2),A_154) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_377,c_28,c_2479])).

tff(c_32,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_30),B_31),B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_177,plain,(
    ! [B_57,A_58] :
      ( B_57 = A_58
      | ~ r1_tarski(B_57,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1320,plain,(
    ! [A_132,B_133] :
      ( k5_relat_1(k6_relat_1(A_132),B_133) = B_133
      | ~ r1_tarski(B_133,k5_relat_1(k6_relat_1(A_132),B_133))
      | ~ v1_relat_1(B_133) ) ),
    inference(resolution,[status(thm)],[c_32,c_177])).

tff(c_17318,plain,(
    ! [A_347,B_348] :
      ( k5_relat_1(k6_relat_1(A_347),B_348) = B_348
      | ~ r1_tarski(B_348,k7_relat_1(B_348,A_347))
      | ~ v1_relat_1(B_348)
      | ~ v1_relat_1(B_348) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1320])).

tff(c_17351,plain,(
    ! [B_2,A_154] :
      ( k5_relat_1(k6_relat_1(B_2),k7_relat_1(k6_relat_1(B_2),A_154)) = k7_relat_1(k6_relat_1(B_2),A_154)
      | ~ r1_tarski(k7_relat_1(k6_relat_1(B_2),A_154),k7_relat_1(k6_relat_1(B_2),A_154))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(B_2),A_154))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(B_2),A_154)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2530,c_17318])).

tff(c_17402,plain,(
    ! [B_2,A_154] : k5_relat_1(k6_relat_1(B_2),k7_relat_1(k6_relat_1(B_2),A_154)) = k7_relat_1(k6_relat_1(B_2),A_154) ),
    inference(demodulation,[status(thm),theory(equality)],[c_809,c_809,c_8,c_17351])).

tff(c_521,plain,(
    ! [A_91,B_92,A_30] :
      ( r1_tarski(k5_relat_1(A_91,k5_relat_1(B_92,k6_relat_1(A_30))),k5_relat_1(A_91,B_92))
      | ~ v1_relat_1(k5_relat_1(A_91,B_92))
      | ~ v1_relat_1(k6_relat_1(A_30))
      | ~ v1_relat_1(B_92)
      | ~ v1_relat_1(A_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_34])).

tff(c_3411,plain,(
    ! [A_172,B_173,A_174] :
      ( r1_tarski(k5_relat_1(A_172,k5_relat_1(B_173,k6_relat_1(A_174))),k5_relat_1(A_172,B_173))
      | ~ v1_relat_1(k5_relat_1(A_172,B_173))
      | ~ v1_relat_1(B_173)
      | ~ v1_relat_1(A_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_521])).

tff(c_3464,plain,(
    ! [A_172,A_174,A_35] :
      ( r1_tarski(k5_relat_1(A_172,k7_relat_1(k6_relat_1(A_174),A_35)),k5_relat_1(A_172,k6_relat_1(A_35)))
      | ~ v1_relat_1(k5_relat_1(A_172,k6_relat_1(A_35)))
      | ~ v1_relat_1(k6_relat_1(A_35))
      | ~ v1_relat_1(A_172)
      | ~ v1_relat_1(k6_relat_1(A_174)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_3411])).

tff(c_33558,plain,(
    ! [A_485,A_486,A_487] :
      ( r1_tarski(k5_relat_1(A_485,k7_relat_1(k6_relat_1(A_486),A_487)),k5_relat_1(A_485,k6_relat_1(A_487)))
      | ~ v1_relat_1(k5_relat_1(A_485,k6_relat_1(A_487)))
      | ~ v1_relat_1(A_485) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_3464])).

tff(c_33611,plain,(
    ! [B_2,A_154] :
      ( r1_tarski(k7_relat_1(k6_relat_1(B_2),A_154),k5_relat_1(k6_relat_1(B_2),k6_relat_1(A_154)))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(B_2),k6_relat_1(A_154)))
      | ~ v1_relat_1(k6_relat_1(B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17402,c_33558])).

tff(c_33827,plain,(
    ! [B_488,A_489] : r1_tarski(k7_relat_1(k6_relat_1(B_488),A_489),k5_relat_1(k6_relat_1(B_488),k6_relat_1(A_489))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_8994,c_33611])).

tff(c_34005,plain,(
    ! [A_35,A_489] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_35),A_489),k7_relat_1(k6_relat_1(A_489),A_35))
      | ~ v1_relat_1(k6_relat_1(A_489)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_33827])).

tff(c_34046,plain,(
    ! [A_490,A_491] : r1_tarski(k7_relat_1(k6_relat_1(A_490),A_491),k7_relat_1(k6_relat_1(A_491),A_490)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_34005])).

tff(c_34232,plain,(
    ! [A_491,A_20] :
      ( r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_491)),A_20)),A_491),k7_relat_1(k6_relat_1(A_491),A_20))
      | ~ v1_relat_1(k6_relat_1(A_491)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_34046])).

tff(c_35035,plain,(
    ! [A_494,A_495] : r1_tarski(k6_relat_1(k3_xboole_0(A_494,A_495)),k7_relat_1(k6_relat_1(A_494),A_495)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2120,c_28,c_34232])).

tff(c_35045,plain,(
    ! [A_494,A_495] :
      ( k7_relat_1(k6_relat_1(A_494),A_495) = k6_relat_1(k3_xboole_0(A_494,A_495))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(A_494),A_495),k6_relat_1(k3_xboole_0(A_494,A_495))) ) ),
    inference(resolution,[status(thm)],[c_35035,c_4])).

tff(c_35255,plain,(
    ! [A_494,A_495] : k7_relat_1(k6_relat_1(A_494),A_495) = k6_relat_1(k3_xboole_0(A_494,A_495)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_35045])).

tff(c_42,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_240,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_42])).

tff(c_261,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_240])).

tff(c_35375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_35255,c_261])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.28/6.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.28/6.51  
% 14.28/6.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.28/6.51  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 14.28/6.51  
% 14.28/6.51  %Foreground sorts:
% 14.28/6.51  
% 14.28/6.51  
% 14.28/6.51  %Background operators:
% 14.28/6.51  
% 14.28/6.51  
% 14.28/6.51  %Foreground operators:
% 14.28/6.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.28/6.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 14.28/6.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 14.28/6.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.28/6.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.28/6.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.28/6.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.28/6.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.28/6.51  tff('#skF_2', type, '#skF_2': $i).
% 14.28/6.51  tff('#skF_1', type, '#skF_1': $i).
% 14.28/6.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.28/6.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.28/6.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 14.28/6.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.28/6.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.28/6.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.28/6.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.28/6.51  
% 14.28/6.53  tff(f_49, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 14.28/6.53  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 14.28/6.53  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 14.28/6.53  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 14.28/6.53  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 14.28/6.53  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 14.28/6.53  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 14.28/6.53  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 14.28/6.53  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.28/6.53  tff(f_47, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 14.28/6.53  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 14.28/6.53  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 14.28/6.53  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 14.28/6.53  tff(f_94, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 14.28/6.53  tff(c_20, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.28/6.53  tff(c_28, plain, (![A_29]: (k1_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.28/6.53  tff(c_347, plain, (![B_76, A_77]: (k7_relat_1(B_76, k3_xboole_0(k1_relat_1(B_76), A_77))=k7_relat_1(B_76, A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.28/6.53  tff(c_216, plain, (![A_64, B_65]: (k5_relat_1(k6_relat_1(A_64), B_65)=k7_relat_1(B_65, A_64) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.28/6.53  tff(c_34, plain, (![B_31, A_30]: (r1_tarski(k5_relat_1(B_31, k6_relat_1(A_30)), B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_77])).
% 14.28/6.53  tff(c_226, plain, (![A_30, A_64]: (r1_tarski(k7_relat_1(k6_relat_1(A_30), A_64), k6_relat_1(A_64)) | ~v1_relat_1(k6_relat_1(A_64)) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_216, c_34])).
% 14.28/6.53  tff(c_255, plain, (![A_30, A_64]: (r1_tarski(k7_relat_1(k6_relat_1(A_30), A_64), k6_relat_1(A_64)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_226])).
% 14.28/6.53  tff(c_354, plain, (![A_30, A_77]: (r1_tarski(k7_relat_1(k6_relat_1(A_30), A_77), k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_30)), A_77))) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_347, c_255])).
% 14.28/6.53  tff(c_374, plain, (![A_30, A_77]: (r1_tarski(k7_relat_1(k6_relat_1(A_30), A_77), k6_relat_1(k3_xboole_0(A_30, A_77))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_28, c_354])).
% 14.28/6.53  tff(c_30, plain, (![A_29]: (k2_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.28/6.53  tff(c_38, plain, (![A_34]: (k5_relat_1(A_34, k6_relat_1(k2_relat_1(A_34)))=A_34 | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.28/6.53  tff(c_234, plain, (![A_64]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_64))), A_64)=k6_relat_1(A_64) | ~v1_relat_1(k6_relat_1(A_64)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_64)))))), inference(superposition, [status(thm), theory('equality')], [c_216, c_38])).
% 14.28/6.53  tff(c_259, plain, (![A_64]: (k7_relat_1(k6_relat_1(A_64), A_64)=k6_relat_1(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_30, c_234])).
% 14.28/6.53  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.28/6.53  tff(c_285, plain, (![A_69, B_70]: (k5_relat_1(k6_relat_1(A_69), B_70)=B_70 | ~r1_tarski(k1_relat_1(B_70), A_69) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_83])).
% 14.28/6.53  tff(c_288, plain, (![A_69, A_29]: (k5_relat_1(k6_relat_1(A_69), k6_relat_1(A_29))=k6_relat_1(A_29) | ~r1_tarski(A_29, A_69) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_285])).
% 14.28/6.53  tff(c_601, plain, (![A_98, A_99]: (k5_relat_1(k6_relat_1(A_98), k6_relat_1(A_99))=k6_relat_1(A_99) | ~r1_tarski(A_99, A_98))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_288])).
% 14.28/6.53  tff(c_40, plain, (![A_35, B_36]: (k5_relat_1(k6_relat_1(A_35), B_36)=k7_relat_1(B_36, A_35) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.28/6.53  tff(c_614, plain, (![A_99, A_98]: (k7_relat_1(k6_relat_1(A_99), A_98)=k6_relat_1(A_99) | ~v1_relat_1(k6_relat_1(A_99)) | ~r1_tarski(A_99, A_98))), inference(superposition, [status(thm), theory('equality')], [c_601, c_40])).
% 14.28/6.53  tff(c_687, plain, (![A_102, A_103]: (k7_relat_1(k6_relat_1(A_102), A_103)=k6_relat_1(A_102) | ~r1_tarski(A_102, A_103))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_614])).
% 14.28/6.53  tff(c_696, plain, (![A_102, A_103]: (r1_tarski(k6_relat_1(A_102), k6_relat_1(k3_xboole_0(A_102, A_103))) | ~r1_tarski(A_102, A_103))), inference(superposition, [status(thm), theory('equality')], [c_687, c_374])).
% 14.28/6.53  tff(c_620, plain, (![A_99, A_98]: (r1_tarski(k6_relat_1(A_99), k6_relat_1(A_98)) | ~v1_relat_1(k6_relat_1(A_98)) | ~r1_tarski(A_99, A_98))), inference(superposition, [status(thm), theory('equality')], [c_601, c_34])).
% 14.28/6.53  tff(c_683, plain, (![A_100, A_101]: (r1_tarski(k6_relat_1(A_100), k6_relat_1(A_101)) | ~r1_tarski(A_100, A_101))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_620])).
% 14.28/6.53  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.28/6.53  tff(c_1438, plain, (![A_137, A_136]: (k6_relat_1(A_137)=k6_relat_1(A_136) | ~r1_tarski(k6_relat_1(A_136), k6_relat_1(A_137)) | ~r1_tarski(A_137, A_136))), inference(resolution, [status(thm)], [c_683, c_4])).
% 14.28/6.53  tff(c_1447, plain, (![A_102, A_103]: (k6_relat_1(k3_xboole_0(A_102, A_103))=k6_relat_1(A_102) | ~r1_tarski(k3_xboole_0(A_102, A_103), A_102) | ~r1_tarski(A_102, A_103))), inference(resolution, [status(thm)], [c_696, c_1438])).
% 14.28/6.53  tff(c_1807, plain, (![A_143, A_144]: (k6_relat_1(k3_xboole_0(A_143, A_144))=k6_relat_1(A_143) | ~r1_tarski(A_143, A_144))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1447])).
% 14.28/6.53  tff(c_1916, plain, (![A_143, A_144]: (k3_xboole_0(A_143, A_144)=k2_relat_1(k6_relat_1(A_143)) | ~r1_tarski(A_143, A_144))), inference(superposition, [status(thm), theory('equality')], [c_1807, c_30])).
% 14.28/6.53  tff(c_1950, plain, (![A_145, A_146]: (k3_xboole_0(A_145, A_146)=A_145 | ~r1_tarski(A_145, A_146))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1916])).
% 14.28/6.53  tff(c_2015, plain, (![A_147, B_148]: (k3_xboole_0(k3_xboole_0(A_147, B_148), A_147)=k3_xboole_0(A_147, B_148))), inference(resolution, [status(thm)], [c_10, c_1950])).
% 14.28/6.53  tff(c_371, plain, (![A_29, A_77]: (k7_relat_1(k6_relat_1(A_29), k3_xboole_0(A_29, A_77))=k7_relat_1(k6_relat_1(A_29), A_77) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_347])).
% 14.28/6.53  tff(c_377, plain, (![A_29, A_77]: (k7_relat_1(k6_relat_1(A_29), k3_xboole_0(A_29, A_77))=k7_relat_1(k6_relat_1(A_29), A_77))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_371])).
% 14.28/6.53  tff(c_2052, plain, (![A_147, B_148]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_147, B_148)), k3_xboole_0(A_147, B_148))=k7_relat_1(k6_relat_1(k3_xboole_0(A_147, B_148)), A_147))), inference(superposition, [status(thm), theory('equality')], [c_2015, c_377])).
% 14.28/6.53  tff(c_2120, plain, (![A_147, B_148]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_147, B_148)), A_147)=k6_relat_1(k3_xboole_0(A_147, B_148)))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_2052])).
% 14.28/6.53  tff(c_24, plain, (![B_21, A_20]: (k7_relat_1(B_21, k3_xboole_0(k1_relat_1(B_21), A_20))=k7_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.28/6.53  tff(c_763, plain, (![A_104, A_105]: (k7_relat_1(k6_relat_1(A_104), k3_xboole_0(A_104, A_105))=k7_relat_1(k6_relat_1(A_104), A_105))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_371])).
% 14.28/6.53  tff(c_18, plain, (![A_14, B_15]: (v1_relat_1(k5_relat_1(A_14, B_15)) | ~v1_relat_1(B_15) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.28/6.53  tff(c_222, plain, (![B_65, A_64]: (v1_relat_1(k7_relat_1(B_65, A_64)) | ~v1_relat_1(B_65) | ~v1_relat_1(k6_relat_1(A_64)) | ~v1_relat_1(B_65))), inference(superposition, [status(thm), theory('equality')], [c_216, c_18])).
% 14.28/6.53  tff(c_253, plain, (![B_65, A_64]: (v1_relat_1(k7_relat_1(B_65, A_64)) | ~v1_relat_1(B_65))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_222])).
% 14.28/6.53  tff(c_787, plain, (![A_104, A_105]: (v1_relat_1(k7_relat_1(k6_relat_1(A_104), A_105)) | ~v1_relat_1(k6_relat_1(A_104)))), inference(superposition, [status(thm), theory('equality')], [c_763, c_253])).
% 14.28/6.53  tff(c_809, plain, (![A_104, A_105]: (v1_relat_1(k7_relat_1(k6_relat_1(A_104), A_105)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_787])).
% 14.28/6.53  tff(c_133, plain, (![A_53]: (k5_relat_1(A_53, k6_relat_1(k2_relat_1(A_53)))=A_53 | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.28/6.53  tff(c_146, plain, (![A_29]: (k5_relat_1(k6_relat_1(A_29), k6_relat_1(A_29))=k6_relat_1(A_29) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_133])).
% 14.28/6.53  tff(c_152, plain, (![A_29]: (k5_relat_1(k6_relat_1(A_29), k6_relat_1(A_29))=k6_relat_1(A_29))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_146])).
% 14.28/6.53  tff(c_508, plain, (![A_91, B_92, C_93]: (k5_relat_1(k5_relat_1(A_91, B_92), C_93)=k5_relat_1(A_91, k5_relat_1(B_92, C_93)) | ~v1_relat_1(C_93) | ~v1_relat_1(B_92) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_67])).
% 14.28/6.53  tff(c_537, plain, (![A_35, B_36, C_93]: (k5_relat_1(k6_relat_1(A_35), k5_relat_1(B_36, C_93))=k5_relat_1(k7_relat_1(B_36, A_35), C_93) | ~v1_relat_1(C_93) | ~v1_relat_1(B_36) | ~v1_relat_1(k6_relat_1(A_35)) | ~v1_relat_1(B_36))), inference(superposition, [status(thm), theory('equality')], [c_40, c_508])).
% 14.28/6.53  tff(c_1710, plain, (![A_140, B_141, C_142]: (k5_relat_1(k6_relat_1(A_140), k5_relat_1(B_141, C_142))=k5_relat_1(k7_relat_1(B_141, A_140), C_142) | ~v1_relat_1(C_142) | ~v1_relat_1(B_141))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_537])).
% 14.28/6.53  tff(c_1779, plain, (![A_29, A_140]: (k5_relat_1(k7_relat_1(k6_relat_1(A_29), A_140), k6_relat_1(A_29))=k5_relat_1(k6_relat_1(A_140), k6_relat_1(A_29)) | ~v1_relat_1(k6_relat_1(A_29)) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_152, c_1710])).
% 14.28/6.53  tff(c_8871, plain, (![A_253, A_254]: (k5_relat_1(k7_relat_1(k6_relat_1(A_253), A_254), k6_relat_1(A_253))=k5_relat_1(k6_relat_1(A_254), k6_relat_1(A_253)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_1779])).
% 14.28/6.53  tff(c_8901, plain, (![A_254, A_253]: (v1_relat_1(k5_relat_1(k6_relat_1(A_254), k6_relat_1(A_253))) | ~v1_relat_1(k6_relat_1(A_253)) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_253), A_254)))), inference(superposition, [status(thm), theory('equality')], [c_8871, c_18])).
% 14.28/6.53  tff(c_8994, plain, (![A_254, A_253]: (v1_relat_1(k5_relat_1(k6_relat_1(A_254), k6_relat_1(A_253))))), inference(demodulation, [status(thm), theory('equality')], [c_809, c_20, c_8901])).
% 14.28/6.53  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.28/6.53  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.28/6.53  tff(c_800, plain, (![B_2, A_1]: (k7_relat_1(k6_relat_1(B_2), k3_xboole_0(A_1, B_2))=k7_relat_1(k6_relat_1(B_2), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_763])).
% 14.28/6.53  tff(c_431, plain, (![C_85, A_86, B_87]: (k7_relat_1(k7_relat_1(C_85, A_86), B_87)=k7_relat_1(C_85, k3_xboole_0(A_86, B_87)) | ~v1_relat_1(C_85))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.28/6.53  tff(c_2393, plain, (![B_153, A_154, B_155]: (k7_relat_1(B_153, k3_xboole_0(k3_xboole_0(k1_relat_1(B_153), A_154), B_155))=k7_relat_1(k7_relat_1(B_153, A_154), B_155) | ~v1_relat_1(B_153) | ~v1_relat_1(B_153))), inference(superposition, [status(thm), theory('equality')], [c_24, c_431])).
% 14.28/6.53  tff(c_2479, plain, (![B_2, A_154]: (k7_relat_1(k6_relat_1(B_2), k3_xboole_0(k1_relat_1(k6_relat_1(B_2)), A_154))=k7_relat_1(k7_relat_1(k6_relat_1(B_2), A_154), B_2) | ~v1_relat_1(k6_relat_1(B_2)) | ~v1_relat_1(k6_relat_1(B_2)))), inference(superposition, [status(thm), theory('equality')], [c_800, c_2393])).
% 14.28/6.53  tff(c_2530, plain, (![B_2, A_154]: (k7_relat_1(k7_relat_1(k6_relat_1(B_2), A_154), B_2)=k7_relat_1(k6_relat_1(B_2), A_154))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_377, c_28, c_2479])).
% 14.28/6.53  tff(c_32, plain, (![A_30, B_31]: (r1_tarski(k5_relat_1(k6_relat_1(A_30), B_31), B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_77])).
% 14.28/6.53  tff(c_177, plain, (![B_57, A_58]: (B_57=A_58 | ~r1_tarski(B_57, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.28/6.53  tff(c_1320, plain, (![A_132, B_133]: (k5_relat_1(k6_relat_1(A_132), B_133)=B_133 | ~r1_tarski(B_133, k5_relat_1(k6_relat_1(A_132), B_133)) | ~v1_relat_1(B_133))), inference(resolution, [status(thm)], [c_32, c_177])).
% 14.28/6.53  tff(c_17318, plain, (![A_347, B_348]: (k5_relat_1(k6_relat_1(A_347), B_348)=B_348 | ~r1_tarski(B_348, k7_relat_1(B_348, A_347)) | ~v1_relat_1(B_348) | ~v1_relat_1(B_348))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1320])).
% 14.28/6.53  tff(c_17351, plain, (![B_2, A_154]: (k5_relat_1(k6_relat_1(B_2), k7_relat_1(k6_relat_1(B_2), A_154))=k7_relat_1(k6_relat_1(B_2), A_154) | ~r1_tarski(k7_relat_1(k6_relat_1(B_2), A_154), k7_relat_1(k6_relat_1(B_2), A_154)) | ~v1_relat_1(k7_relat_1(k6_relat_1(B_2), A_154)) | ~v1_relat_1(k7_relat_1(k6_relat_1(B_2), A_154)))), inference(superposition, [status(thm), theory('equality')], [c_2530, c_17318])).
% 14.28/6.53  tff(c_17402, plain, (![B_2, A_154]: (k5_relat_1(k6_relat_1(B_2), k7_relat_1(k6_relat_1(B_2), A_154))=k7_relat_1(k6_relat_1(B_2), A_154))), inference(demodulation, [status(thm), theory('equality')], [c_809, c_809, c_8, c_17351])).
% 14.28/6.53  tff(c_521, plain, (![A_91, B_92, A_30]: (r1_tarski(k5_relat_1(A_91, k5_relat_1(B_92, k6_relat_1(A_30))), k5_relat_1(A_91, B_92)) | ~v1_relat_1(k5_relat_1(A_91, B_92)) | ~v1_relat_1(k6_relat_1(A_30)) | ~v1_relat_1(B_92) | ~v1_relat_1(A_91))), inference(superposition, [status(thm), theory('equality')], [c_508, c_34])).
% 14.28/6.53  tff(c_3411, plain, (![A_172, B_173, A_174]: (r1_tarski(k5_relat_1(A_172, k5_relat_1(B_173, k6_relat_1(A_174))), k5_relat_1(A_172, B_173)) | ~v1_relat_1(k5_relat_1(A_172, B_173)) | ~v1_relat_1(B_173) | ~v1_relat_1(A_172))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_521])).
% 14.28/6.53  tff(c_3464, plain, (![A_172, A_174, A_35]: (r1_tarski(k5_relat_1(A_172, k7_relat_1(k6_relat_1(A_174), A_35)), k5_relat_1(A_172, k6_relat_1(A_35))) | ~v1_relat_1(k5_relat_1(A_172, k6_relat_1(A_35))) | ~v1_relat_1(k6_relat_1(A_35)) | ~v1_relat_1(A_172) | ~v1_relat_1(k6_relat_1(A_174)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_3411])).
% 14.28/6.53  tff(c_33558, plain, (![A_485, A_486, A_487]: (r1_tarski(k5_relat_1(A_485, k7_relat_1(k6_relat_1(A_486), A_487)), k5_relat_1(A_485, k6_relat_1(A_487))) | ~v1_relat_1(k5_relat_1(A_485, k6_relat_1(A_487))) | ~v1_relat_1(A_485))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_3464])).
% 14.28/6.53  tff(c_33611, plain, (![B_2, A_154]: (r1_tarski(k7_relat_1(k6_relat_1(B_2), A_154), k5_relat_1(k6_relat_1(B_2), k6_relat_1(A_154))) | ~v1_relat_1(k5_relat_1(k6_relat_1(B_2), k6_relat_1(A_154))) | ~v1_relat_1(k6_relat_1(B_2)))), inference(superposition, [status(thm), theory('equality')], [c_17402, c_33558])).
% 14.28/6.53  tff(c_33827, plain, (![B_488, A_489]: (r1_tarski(k7_relat_1(k6_relat_1(B_488), A_489), k5_relat_1(k6_relat_1(B_488), k6_relat_1(A_489))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_8994, c_33611])).
% 14.28/6.53  tff(c_34005, plain, (![A_35, A_489]: (r1_tarski(k7_relat_1(k6_relat_1(A_35), A_489), k7_relat_1(k6_relat_1(A_489), A_35)) | ~v1_relat_1(k6_relat_1(A_489)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_33827])).
% 14.28/6.53  tff(c_34046, plain, (![A_490, A_491]: (r1_tarski(k7_relat_1(k6_relat_1(A_490), A_491), k7_relat_1(k6_relat_1(A_491), A_490)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_34005])).
% 14.28/6.53  tff(c_34232, plain, (![A_491, A_20]: (r1_tarski(k7_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_491)), A_20)), A_491), k7_relat_1(k6_relat_1(A_491), A_20)) | ~v1_relat_1(k6_relat_1(A_491)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_34046])).
% 14.28/6.53  tff(c_35035, plain, (![A_494, A_495]: (r1_tarski(k6_relat_1(k3_xboole_0(A_494, A_495)), k7_relat_1(k6_relat_1(A_494), A_495)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2120, c_28, c_34232])).
% 14.28/6.53  tff(c_35045, plain, (![A_494, A_495]: (k7_relat_1(k6_relat_1(A_494), A_495)=k6_relat_1(k3_xboole_0(A_494, A_495)) | ~r1_tarski(k7_relat_1(k6_relat_1(A_494), A_495), k6_relat_1(k3_xboole_0(A_494, A_495))))), inference(resolution, [status(thm)], [c_35035, c_4])).
% 14.28/6.53  tff(c_35255, plain, (![A_494, A_495]: (k7_relat_1(k6_relat_1(A_494), A_495)=k6_relat_1(k3_xboole_0(A_494, A_495)))), inference(demodulation, [status(thm), theory('equality')], [c_374, c_35045])).
% 14.28/6.53  tff(c_42, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 14.28/6.53  tff(c_240, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_216, c_42])).
% 14.28/6.53  tff(c_261, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_240])).
% 14.28/6.53  tff(c_35375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_35255, c_261])).
% 14.28/6.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.28/6.53  
% 14.28/6.53  Inference rules
% 14.28/6.53  ----------------------
% 14.28/6.53  #Ref     : 0
% 14.28/6.53  #Sup     : 8757
% 14.28/6.53  #Fact    : 0
% 14.28/6.53  #Define  : 0
% 14.28/6.53  #Split   : 1
% 14.28/6.53  #Chain   : 0
% 14.28/6.53  #Close   : 0
% 14.28/6.53  
% 14.28/6.53  Ordering : KBO
% 14.28/6.53  
% 14.28/6.53  Simplification rules
% 14.28/6.53  ----------------------
% 14.28/6.53  #Subsume      : 1016
% 14.28/6.53  #Demod        : 10107
% 14.28/6.53  #Tautology    : 3368
% 14.28/6.53  #SimpNegUnit  : 0
% 14.28/6.53  #BackRed      : 62
% 14.28/6.53  
% 14.28/6.53  #Partial instantiations: 0
% 14.28/6.53  #Strategies tried      : 1
% 14.28/6.53  
% 14.28/6.53  Timing (in seconds)
% 14.28/6.53  ----------------------
% 14.28/6.54  Preprocessing        : 0.32
% 14.28/6.54  Parsing              : 0.18
% 14.28/6.54  CNF conversion       : 0.02
% 14.28/6.54  Main loop            : 5.40
% 14.28/6.54  Inferencing          : 0.98
% 14.28/6.54  Reduction            : 2.91
% 14.28/6.54  Demodulation         : 2.60
% 14.28/6.54  BG Simplification    : 0.15
% 14.28/6.54  Subsumption          : 1.08
% 14.28/6.54  Abstraction          : 0.25
% 14.28/6.54  MUC search           : 0.00
% 14.28/6.54  Cooper               : 0.00
% 14.28/6.54  Total                : 5.76
% 14.28/6.54  Index Insertion      : 0.00
% 14.28/6.54  Index Deletion       : 0.00
% 14.28/6.54  Index Matching       : 0.00
% 14.28/6.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
