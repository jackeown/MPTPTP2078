%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:33 EST 2020

% Result     : Theorem 4.00s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 398 expanded)
%              Number of leaves         :   36 ( 157 expanded)
%              Depth                    :   17
%              Number of atoms          :  128 ( 757 expanded)
%              Number of equality atoms :   51 ( 217 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_113,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_95,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_116,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_46,plain,(
    ! [A_46] : v1_relat_1(k6_relat_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_48,plain,(
    ! [A_46] : v4_relat_1(k6_relat_1(A_46),A_46) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_165,plain,(
    ! [B_73,A_74] :
      ( k7_relat_1(B_73,A_74) = B_73
      | ~ v4_relat_1(B_73,A_74)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_168,plain,(
    ! [A_46] :
      ( k7_relat_1(k6_relat_1(A_46),A_46) = k6_relat_1(A_46)
      | ~ v1_relat_1(k6_relat_1(A_46)) ) ),
    inference(resolution,[status(thm)],[c_48,c_165])).

tff(c_171,plain,(
    ! [A_46] : k7_relat_1(k6_relat_1(A_46),A_46) = k6_relat_1(A_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_168])).

tff(c_726,plain,(
    ! [C_131,A_132,B_133] :
      ( k7_relat_1(k7_relat_1(C_131,A_132),B_133) = k7_relat_1(C_131,k3_xboole_0(A_132,B_133))
      | ~ v1_relat_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_753,plain,(
    ! [A_46,B_133] :
      ( k7_relat_1(k6_relat_1(A_46),k3_xboole_0(A_46,B_133)) = k7_relat_1(k6_relat_1(A_46),B_133)
      | ~ v1_relat_1(k6_relat_1(A_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_726])).

tff(c_759,plain,(
    ! [A_46,B_133] : k7_relat_1(k6_relat_1(A_46),k3_xboole_0(A_46,B_133)) = k7_relat_1(k6_relat_1(A_46),B_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_753])).

tff(c_20,plain,(
    ! [B_26,A_25] :
      ( k5_relat_1(B_26,k6_relat_1(A_25)) = k8_relat_1(A_25,B_26)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_172,plain,(
    ! [A_75,B_76] :
      ( k5_relat_1(k6_relat_1(A_75),B_76) = k7_relat_1(B_76,A_75)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_199,plain,(
    ! [A_25,A_75] :
      ( k8_relat_1(A_25,k6_relat_1(A_75)) = k7_relat_1(k6_relat_1(A_25),A_75)
      | ~ v1_relat_1(k6_relat_1(A_25))
      | ~ v1_relat_1(k6_relat_1(A_75)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_172])).

tff(c_211,plain,(
    ! [A_25,A_75] : k8_relat_1(A_25,k6_relat_1(A_75)) = k7_relat_1(k6_relat_1(A_25),A_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_199])).

tff(c_36,plain,(
    ! [A_40] : k2_relat_1(k6_relat_1(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_318,plain,(
    ! [B_99,A_100] :
      ( k3_xboole_0(k2_relat_1(B_99),A_100) = k2_relat_1(k8_relat_1(A_100,B_99))
      | ~ v1_relat_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_327,plain,(
    ! [A_100,A_40] :
      ( k2_relat_1(k8_relat_1(A_100,k6_relat_1(A_40))) = k3_xboole_0(A_40,A_100)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_318])).

tff(c_331,plain,(
    ! [A_100,A_40] : k2_relat_1(k7_relat_1(k6_relat_1(A_100),A_40)) = k3_xboole_0(A_40,A_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_211,c_327])).

tff(c_1113,plain,(
    ! [A_151,C_152,B_153] :
      ( k8_relat_1(A_151,k7_relat_1(C_152,B_153)) = k7_relat_1(k8_relat_1(A_151,C_152),B_153)
      | ~ v1_relat_1(C_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_234,plain,(
    ! [A_83,A_84] : k8_relat_1(A_83,k6_relat_1(A_84)) = k7_relat_1(k6_relat_1(A_83),A_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_199])).

tff(c_126,plain,(
    ! [B_64,A_65] :
      ( k5_relat_1(B_64,k6_relat_1(A_65)) = k8_relat_1(A_65,B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k5_relat_1(A_17,B_18))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_139,plain,(
    ! [A_65,B_64] :
      ( v1_relat_1(k8_relat_1(A_65,B_64))
      | ~ v1_relat_1(k6_relat_1(A_65))
      | ~ v1_relat_1(B_64)
      | ~ v1_relat_1(B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_12])).

tff(c_150,plain,(
    ! [A_65,B_64] :
      ( v1_relat_1(k8_relat_1(A_65,B_64))
      | ~ v1_relat_1(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_139])).

tff(c_240,plain,(
    ! [A_83,A_84] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_83),A_84))
      | ~ v1_relat_1(k6_relat_1(A_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_150])).

tff(c_246,plain,(
    ! [A_83,A_84] : v1_relat_1(k7_relat_1(k6_relat_1(A_83),A_84)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_240])).

tff(c_42,plain,(
    ! [B_43,A_42] :
      ( r1_tarski(k5_relat_1(B_43,k6_relat_1(A_42)),B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_183,plain,(
    ! [A_42,A_75] :
      ( r1_tarski(k7_relat_1(k6_relat_1(A_42),A_75),k6_relat_1(A_75))
      | ~ v1_relat_1(k6_relat_1(A_75))
      | ~ v1_relat_1(k6_relat_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_42])).

tff(c_204,plain,(
    ! [A_42,A_75] : r1_tarski(k7_relat_1(k6_relat_1(A_42),A_75),k6_relat_1(A_75)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_183])).

tff(c_577,plain,(
    ! [A_121,B_122] :
      ( r1_tarski(k2_relat_1(A_121),k2_relat_1(B_122))
      | ~ r1_tarski(A_121,B_122)
      | ~ v1_relat_1(B_122)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_601,plain,(
    ! [A_121,A_40] :
      ( r1_tarski(k2_relat_1(A_121),A_40)
      | ~ r1_tarski(A_121,k6_relat_1(A_40))
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1(A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_577])).

tff(c_693,plain,(
    ! [A_127,A_128] :
      ( r1_tarski(k2_relat_1(A_127),A_128)
      | ~ r1_tarski(A_127,k6_relat_1(A_128))
      | ~ v1_relat_1(A_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_601])).

tff(c_22,plain,(
    ! [A_27,B_28] :
      ( k8_relat_1(A_27,B_28) = B_28
      | ~ r1_tarski(k2_relat_1(B_28),A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_760,plain,(
    ! [A_134,A_135] :
      ( k8_relat_1(A_134,A_135) = A_135
      | ~ r1_tarski(A_135,k6_relat_1(A_134))
      | ~ v1_relat_1(A_135) ) ),
    inference(resolution,[status(thm)],[c_693,c_22])).

tff(c_785,plain,(
    ! [A_75,A_42] :
      ( k8_relat_1(A_75,k7_relat_1(k6_relat_1(A_42),A_75)) = k7_relat_1(k6_relat_1(A_42),A_75)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(A_42),A_75)) ) ),
    inference(resolution,[status(thm)],[c_204,c_760])).

tff(c_812,plain,(
    ! [A_75,A_42] : k8_relat_1(A_75,k7_relat_1(k6_relat_1(A_42),A_75)) = k7_relat_1(k6_relat_1(A_42),A_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_785])).

tff(c_1120,plain,(
    ! [B_153,A_42] :
      ( k7_relat_1(k8_relat_1(B_153,k6_relat_1(A_42)),B_153) = k7_relat_1(k6_relat_1(A_42),B_153)
      | ~ v1_relat_1(k6_relat_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1113,c_812])).

tff(c_1316,plain,(
    ! [B_160,A_161] : k7_relat_1(k7_relat_1(k6_relat_1(B_160),A_161),B_160) = k7_relat_1(k6_relat_1(A_161),B_160) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_211,c_1120])).

tff(c_16,plain,(
    ! [C_22,A_20,B_21] :
      ( k7_relat_1(k7_relat_1(C_22,A_20),B_21) = k7_relat_1(C_22,k3_xboole_0(A_20,B_21))
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1332,plain,(
    ! [B_160,A_161] :
      ( k7_relat_1(k6_relat_1(B_160),k3_xboole_0(A_161,B_160)) = k7_relat_1(k6_relat_1(A_161),B_160)
      | ~ v1_relat_1(k6_relat_1(B_160)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1316,c_16])).

tff(c_2022,plain,(
    ! [B_187,A_188] : k7_relat_1(k6_relat_1(B_187),k3_xboole_0(A_188,B_187)) = k7_relat_1(k6_relat_1(A_188),B_187) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1332])).

tff(c_2071,plain,(
    ! [A_188,B_187] : k3_xboole_0(k3_xboole_0(A_188,B_187),B_187) = k2_relat_1(k7_relat_1(k6_relat_1(A_188),B_187)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2022,c_331])).

tff(c_2155,plain,(
    ! [A_188,B_187] : k3_xboole_0(k3_xboole_0(A_188,B_187),B_187) = k3_xboole_0(B_187,A_188) ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_2071])).

tff(c_819,plain,(
    ! [A_136,B_137] : k7_relat_1(k6_relat_1(A_136),k3_xboole_0(A_136,B_137)) = k7_relat_1(k6_relat_1(A_136),B_137) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_753])).

tff(c_837,plain,(
    ! [A_136,B_137] : k3_xboole_0(k3_xboole_0(A_136,B_137),A_136) = k2_relat_1(k7_relat_1(k6_relat_1(A_136),B_137)) ),
    inference(superposition,[status(thm),theory(equality)],[c_819,c_331])).

tff(c_890,plain,(
    ! [A_136,B_137] : k3_xboole_0(k3_xboole_0(A_136,B_137),A_136) = k3_xboole_0(B_137,A_136) ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_837])).

tff(c_2173,plain,(
    ! [A_189,B_190] : k3_xboole_0(k3_xboole_0(A_189,B_190),B_190) = k3_xboole_0(B_190,A_189) ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_2071])).

tff(c_2225,plain,(
    ! [B_137,A_136] : k3_xboole_0(k3_xboole_0(B_137,A_136),A_136) = k3_xboole_0(A_136,k3_xboole_0(A_136,B_137)) ),
    inference(superposition,[status(thm),theory(equality)],[c_890,c_2173])).

tff(c_2660,plain,(
    ! [A_203,B_204] : k3_xboole_0(A_203,k3_xboole_0(A_203,B_204)) = k3_xboole_0(A_203,B_204) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2155,c_2225])).

tff(c_1369,plain,(
    ! [B_160,A_161] : k7_relat_1(k6_relat_1(B_160),k3_xboole_0(A_161,B_160)) = k7_relat_1(k6_relat_1(A_161),B_160) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1332])).

tff(c_2679,plain,(
    ! [A_203,B_204] : k7_relat_1(k6_relat_1(k3_xboole_0(A_203,B_204)),k3_xboole_0(A_203,B_204)) = k7_relat_1(k6_relat_1(A_203),k3_xboole_0(A_203,B_204)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2660,c_1369])).

tff(c_2757,plain,(
    ! [A_203,B_204] : k7_relat_1(k6_relat_1(A_203),B_204) = k6_relat_1(k3_xboole_0(A_203,B_204)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_171,c_2679])).

tff(c_52,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_142,plain,
    ( k8_relat_1('#skF_1',k6_relat_1('#skF_2')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_52])).

tff(c_152,plain,(
    k8_relat_1('#skF_1',k6_relat_1('#skF_2')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_142])).

tff(c_232,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_152])).

tff(c_2833,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2757,c_232])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:34:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.00/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/1.67  
% 4.00/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/1.67  %$ v5_relat_1 > v4_relat_1 > r1_tarski > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.00/1.67  
% 4.00/1.67  %Foreground sorts:
% 4.00/1.67  
% 4.00/1.67  
% 4.00/1.67  %Background operators:
% 4.00/1.67  
% 4.00/1.67  
% 4.00/1.67  %Foreground operators:
% 4.00/1.67  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 4.00/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.00/1.67  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.00/1.67  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.00/1.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.00/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.00/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.00/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.00/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.00/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.00/1.67  tff('#skF_2', type, '#skF_2': $i).
% 4.00/1.67  tff('#skF_1', type, '#skF_1': $i).
% 4.00/1.67  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.00/1.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.00/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.00/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.00/1.68  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.00/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.00/1.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.00/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.00/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.00/1.68  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.00/1.68  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.00/1.68  
% 4.12/1.71  tff(f_113, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 4.12/1.71  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 4.12/1.71  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 4.12/1.71  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 4.12/1.71  tff(f_107, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 4.12/1.71  tff(f_95, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.12/1.71  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_relat_1)).
% 4.12/1.71  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_relat_1)).
% 4.12/1.71  tff(f_41, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 4.12/1.71  tff(f_103, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 4.12/1.71  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 4.12/1.71  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 4.12/1.71  tff(f_116, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 4.12/1.71  tff(c_46, plain, (![A_46]: (v1_relat_1(k6_relat_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.12/1.71  tff(c_48, plain, (![A_46]: (v4_relat_1(k6_relat_1(A_46), A_46))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.12/1.71  tff(c_165, plain, (![B_73, A_74]: (k7_relat_1(B_73, A_74)=B_73 | ~v4_relat_1(B_73, A_74) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.12/1.71  tff(c_168, plain, (![A_46]: (k7_relat_1(k6_relat_1(A_46), A_46)=k6_relat_1(A_46) | ~v1_relat_1(k6_relat_1(A_46)))), inference(resolution, [status(thm)], [c_48, c_165])).
% 4.12/1.71  tff(c_171, plain, (![A_46]: (k7_relat_1(k6_relat_1(A_46), A_46)=k6_relat_1(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_168])).
% 4.12/1.71  tff(c_726, plain, (![C_131, A_132, B_133]: (k7_relat_1(k7_relat_1(C_131, A_132), B_133)=k7_relat_1(C_131, k3_xboole_0(A_132, B_133)) | ~v1_relat_1(C_131))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.12/1.71  tff(c_753, plain, (![A_46, B_133]: (k7_relat_1(k6_relat_1(A_46), k3_xboole_0(A_46, B_133))=k7_relat_1(k6_relat_1(A_46), B_133) | ~v1_relat_1(k6_relat_1(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_171, c_726])).
% 4.12/1.71  tff(c_759, plain, (![A_46, B_133]: (k7_relat_1(k6_relat_1(A_46), k3_xboole_0(A_46, B_133))=k7_relat_1(k6_relat_1(A_46), B_133))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_753])).
% 4.12/1.71  tff(c_20, plain, (![B_26, A_25]: (k5_relat_1(B_26, k6_relat_1(A_25))=k8_relat_1(A_25, B_26) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.12/1.71  tff(c_172, plain, (![A_75, B_76]: (k5_relat_1(k6_relat_1(A_75), B_76)=k7_relat_1(B_76, A_75) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.12/1.71  tff(c_199, plain, (![A_25, A_75]: (k8_relat_1(A_25, k6_relat_1(A_75))=k7_relat_1(k6_relat_1(A_25), A_75) | ~v1_relat_1(k6_relat_1(A_25)) | ~v1_relat_1(k6_relat_1(A_75)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_172])).
% 4.12/1.71  tff(c_211, plain, (![A_25, A_75]: (k8_relat_1(A_25, k6_relat_1(A_75))=k7_relat_1(k6_relat_1(A_25), A_75))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_199])).
% 4.12/1.71  tff(c_36, plain, (![A_40]: (k2_relat_1(k6_relat_1(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.12/1.71  tff(c_318, plain, (![B_99, A_100]: (k3_xboole_0(k2_relat_1(B_99), A_100)=k2_relat_1(k8_relat_1(A_100, B_99)) | ~v1_relat_1(B_99))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.12/1.71  tff(c_327, plain, (![A_100, A_40]: (k2_relat_1(k8_relat_1(A_100, k6_relat_1(A_40)))=k3_xboole_0(A_40, A_100) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_318])).
% 4.12/1.71  tff(c_331, plain, (![A_100, A_40]: (k2_relat_1(k7_relat_1(k6_relat_1(A_100), A_40))=k3_xboole_0(A_40, A_100))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_211, c_327])).
% 4.12/1.71  tff(c_1113, plain, (![A_151, C_152, B_153]: (k8_relat_1(A_151, k7_relat_1(C_152, B_153))=k7_relat_1(k8_relat_1(A_151, C_152), B_153) | ~v1_relat_1(C_152))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.12/1.71  tff(c_234, plain, (![A_83, A_84]: (k8_relat_1(A_83, k6_relat_1(A_84))=k7_relat_1(k6_relat_1(A_83), A_84))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_199])).
% 4.12/1.71  tff(c_126, plain, (![B_64, A_65]: (k5_relat_1(B_64, k6_relat_1(A_65))=k8_relat_1(A_65, B_64) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.12/1.71  tff(c_12, plain, (![A_17, B_18]: (v1_relat_1(k5_relat_1(A_17, B_18)) | ~v1_relat_1(B_18) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.12/1.71  tff(c_139, plain, (![A_65, B_64]: (v1_relat_1(k8_relat_1(A_65, B_64)) | ~v1_relat_1(k6_relat_1(A_65)) | ~v1_relat_1(B_64) | ~v1_relat_1(B_64))), inference(superposition, [status(thm), theory('equality')], [c_126, c_12])).
% 4.12/1.71  tff(c_150, plain, (![A_65, B_64]: (v1_relat_1(k8_relat_1(A_65, B_64)) | ~v1_relat_1(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_139])).
% 4.12/1.71  tff(c_240, plain, (![A_83, A_84]: (v1_relat_1(k7_relat_1(k6_relat_1(A_83), A_84)) | ~v1_relat_1(k6_relat_1(A_84)))), inference(superposition, [status(thm), theory('equality')], [c_234, c_150])).
% 4.12/1.71  tff(c_246, plain, (![A_83, A_84]: (v1_relat_1(k7_relat_1(k6_relat_1(A_83), A_84)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_240])).
% 4.12/1.71  tff(c_42, plain, (![B_43, A_42]: (r1_tarski(k5_relat_1(B_43, k6_relat_1(A_42)), B_43) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.12/1.71  tff(c_183, plain, (![A_42, A_75]: (r1_tarski(k7_relat_1(k6_relat_1(A_42), A_75), k6_relat_1(A_75)) | ~v1_relat_1(k6_relat_1(A_75)) | ~v1_relat_1(k6_relat_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_172, c_42])).
% 4.12/1.71  tff(c_204, plain, (![A_42, A_75]: (r1_tarski(k7_relat_1(k6_relat_1(A_42), A_75), k6_relat_1(A_75)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_183])).
% 4.12/1.71  tff(c_577, plain, (![A_121, B_122]: (r1_tarski(k2_relat_1(A_121), k2_relat_1(B_122)) | ~r1_tarski(A_121, B_122) | ~v1_relat_1(B_122) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.12/1.71  tff(c_601, plain, (![A_121, A_40]: (r1_tarski(k2_relat_1(A_121), A_40) | ~r1_tarski(A_121, k6_relat_1(A_40)) | ~v1_relat_1(k6_relat_1(A_40)) | ~v1_relat_1(A_121))), inference(superposition, [status(thm), theory('equality')], [c_36, c_577])).
% 4.12/1.71  tff(c_693, plain, (![A_127, A_128]: (r1_tarski(k2_relat_1(A_127), A_128) | ~r1_tarski(A_127, k6_relat_1(A_128)) | ~v1_relat_1(A_127))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_601])).
% 4.12/1.71  tff(c_22, plain, (![A_27, B_28]: (k8_relat_1(A_27, B_28)=B_28 | ~r1_tarski(k2_relat_1(B_28), A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.12/1.71  tff(c_760, plain, (![A_134, A_135]: (k8_relat_1(A_134, A_135)=A_135 | ~r1_tarski(A_135, k6_relat_1(A_134)) | ~v1_relat_1(A_135))), inference(resolution, [status(thm)], [c_693, c_22])).
% 4.12/1.71  tff(c_785, plain, (![A_75, A_42]: (k8_relat_1(A_75, k7_relat_1(k6_relat_1(A_42), A_75))=k7_relat_1(k6_relat_1(A_42), A_75) | ~v1_relat_1(k7_relat_1(k6_relat_1(A_42), A_75)))), inference(resolution, [status(thm)], [c_204, c_760])).
% 4.12/1.71  tff(c_812, plain, (![A_75, A_42]: (k8_relat_1(A_75, k7_relat_1(k6_relat_1(A_42), A_75))=k7_relat_1(k6_relat_1(A_42), A_75))), inference(demodulation, [status(thm), theory('equality')], [c_246, c_785])).
% 4.12/1.71  tff(c_1120, plain, (![B_153, A_42]: (k7_relat_1(k8_relat_1(B_153, k6_relat_1(A_42)), B_153)=k7_relat_1(k6_relat_1(A_42), B_153) | ~v1_relat_1(k6_relat_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_1113, c_812])).
% 4.12/1.71  tff(c_1316, plain, (![B_160, A_161]: (k7_relat_1(k7_relat_1(k6_relat_1(B_160), A_161), B_160)=k7_relat_1(k6_relat_1(A_161), B_160))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_211, c_1120])).
% 4.12/1.71  tff(c_16, plain, (![C_22, A_20, B_21]: (k7_relat_1(k7_relat_1(C_22, A_20), B_21)=k7_relat_1(C_22, k3_xboole_0(A_20, B_21)) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.12/1.71  tff(c_1332, plain, (![B_160, A_161]: (k7_relat_1(k6_relat_1(B_160), k3_xboole_0(A_161, B_160))=k7_relat_1(k6_relat_1(A_161), B_160) | ~v1_relat_1(k6_relat_1(B_160)))), inference(superposition, [status(thm), theory('equality')], [c_1316, c_16])).
% 4.12/1.71  tff(c_2022, plain, (![B_187, A_188]: (k7_relat_1(k6_relat_1(B_187), k3_xboole_0(A_188, B_187))=k7_relat_1(k6_relat_1(A_188), B_187))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1332])).
% 4.12/1.71  tff(c_2071, plain, (![A_188, B_187]: (k3_xboole_0(k3_xboole_0(A_188, B_187), B_187)=k2_relat_1(k7_relat_1(k6_relat_1(A_188), B_187)))), inference(superposition, [status(thm), theory('equality')], [c_2022, c_331])).
% 4.12/1.71  tff(c_2155, plain, (![A_188, B_187]: (k3_xboole_0(k3_xboole_0(A_188, B_187), B_187)=k3_xboole_0(B_187, A_188))), inference(demodulation, [status(thm), theory('equality')], [c_331, c_2071])).
% 4.12/1.71  tff(c_819, plain, (![A_136, B_137]: (k7_relat_1(k6_relat_1(A_136), k3_xboole_0(A_136, B_137))=k7_relat_1(k6_relat_1(A_136), B_137))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_753])).
% 4.12/1.71  tff(c_837, plain, (![A_136, B_137]: (k3_xboole_0(k3_xboole_0(A_136, B_137), A_136)=k2_relat_1(k7_relat_1(k6_relat_1(A_136), B_137)))), inference(superposition, [status(thm), theory('equality')], [c_819, c_331])).
% 4.12/1.71  tff(c_890, plain, (![A_136, B_137]: (k3_xboole_0(k3_xboole_0(A_136, B_137), A_136)=k3_xboole_0(B_137, A_136))), inference(demodulation, [status(thm), theory('equality')], [c_331, c_837])).
% 4.12/1.71  tff(c_2173, plain, (![A_189, B_190]: (k3_xboole_0(k3_xboole_0(A_189, B_190), B_190)=k3_xboole_0(B_190, A_189))), inference(demodulation, [status(thm), theory('equality')], [c_331, c_2071])).
% 4.12/1.71  tff(c_2225, plain, (![B_137, A_136]: (k3_xboole_0(k3_xboole_0(B_137, A_136), A_136)=k3_xboole_0(A_136, k3_xboole_0(A_136, B_137)))), inference(superposition, [status(thm), theory('equality')], [c_890, c_2173])).
% 4.12/1.71  tff(c_2660, plain, (![A_203, B_204]: (k3_xboole_0(A_203, k3_xboole_0(A_203, B_204))=k3_xboole_0(A_203, B_204))), inference(demodulation, [status(thm), theory('equality')], [c_2155, c_2225])).
% 4.12/1.71  tff(c_1369, plain, (![B_160, A_161]: (k7_relat_1(k6_relat_1(B_160), k3_xboole_0(A_161, B_160))=k7_relat_1(k6_relat_1(A_161), B_160))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1332])).
% 4.12/1.71  tff(c_2679, plain, (![A_203, B_204]: (k7_relat_1(k6_relat_1(k3_xboole_0(A_203, B_204)), k3_xboole_0(A_203, B_204))=k7_relat_1(k6_relat_1(A_203), k3_xboole_0(A_203, B_204)))), inference(superposition, [status(thm), theory('equality')], [c_2660, c_1369])).
% 4.12/1.71  tff(c_2757, plain, (![A_203, B_204]: (k7_relat_1(k6_relat_1(A_203), B_204)=k6_relat_1(k3_xboole_0(A_203, B_204)))), inference(demodulation, [status(thm), theory('equality')], [c_759, c_171, c_2679])).
% 4.12/1.71  tff(c_52, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.12/1.71  tff(c_142, plain, (k8_relat_1('#skF_1', k6_relat_1('#skF_2'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_52])).
% 4.12/1.71  tff(c_152, plain, (k8_relat_1('#skF_1', k6_relat_1('#skF_2'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_142])).
% 4.12/1.71  tff(c_232, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_152])).
% 4.12/1.71  tff(c_2833, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2757, c_232])).
% 4.12/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.71  
% 4.12/1.71  Inference rules
% 4.12/1.71  ----------------------
% 4.12/1.71  #Ref     : 0
% 4.12/1.71  #Sup     : 646
% 4.12/1.71  #Fact    : 0
% 4.12/1.71  #Define  : 0
% 4.12/1.71  #Split   : 1
% 4.12/1.71  #Chain   : 0
% 4.12/1.71  #Close   : 0
% 4.12/1.71  
% 4.12/1.71  Ordering : KBO
% 4.12/1.71  
% 4.12/1.71  Simplification rules
% 4.12/1.71  ----------------------
% 4.12/1.71  #Subsume      : 54
% 4.12/1.71  #Demod        : 531
% 4.12/1.71  #Tautology    : 309
% 4.12/1.71  #SimpNegUnit  : 0
% 4.12/1.71  #BackRed      : 24
% 4.12/1.71  
% 4.12/1.71  #Partial instantiations: 0
% 4.12/1.71  #Strategies tried      : 1
% 4.12/1.71  
% 4.12/1.71  Timing (in seconds)
% 4.12/1.71  ----------------------
% 4.12/1.71  Preprocessing        : 0.32
% 4.12/1.71  Parsing              : 0.17
% 4.12/1.71  CNF conversion       : 0.02
% 4.12/1.71  Main loop            : 0.60
% 4.12/1.71  Inferencing          : 0.22
% 4.12/1.71  Reduction            : 0.22
% 4.12/1.71  Demodulation         : 0.17
% 4.12/1.71  BG Simplification    : 0.03
% 4.12/1.71  Subsumption          : 0.09
% 4.12/1.71  Abstraction          : 0.04
% 4.12/1.71  MUC search           : 0.00
% 4.12/1.71  Cooper               : 0.00
% 4.12/1.71  Total                : 0.97
% 4.12/1.71  Index Insertion      : 0.00
% 4.12/1.71  Index Deletion       : 0.00
% 4.12/1.71  Index Matching       : 0.00
% 4.12/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
