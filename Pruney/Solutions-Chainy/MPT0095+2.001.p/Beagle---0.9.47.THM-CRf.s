%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:34 EST 2020

% Result     : Theorem 36.63s
% Output     : CNFRefutation 36.78s
% Verified   : 
% Statistics : Number of formulae       :  233 (4676 expanded)
%              Number of leaves         :   21 (1594 expanded)
%              Depth                    :   24
%              Number of atoms          :  290 (5480 expanded)
%              Number of equality atoms :  207 (4432 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
       => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(c_37,plain,(
    ! [B_21,A_22] : k2_xboole_0(B_21,A_22) = k2_xboole_0(A_22,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_53,plain,(
    ! [A_22] : k2_xboole_0(k1_xboole_0,A_22) = A_22 ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_14])).

tff(c_177,plain,(
    ! [A_37,B_38] : k4_xboole_0(k2_xboole_0(A_37,B_38),B_38) = k4_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_189,plain,(
    ! [A_22] : k4_xboole_0(k1_xboole_0,A_22) = k4_xboole_0(A_22,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_177])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] : k4_xboole_0(k4_xboole_0(A_13,B_14),C_15) = k4_xboole_0(A_13,k2_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_11,B_12] : k4_xboole_0(k2_xboole_0(A_11,B_12),B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_347,plain,(
    ! [A_52,B_53,C_54] : k4_xboole_0(k4_xboole_0(A_52,B_53),C_54) = k4_xboole_0(A_52,k2_xboole_0(B_53,C_54)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_391,plain,(
    ! [A_11,B_12,C_54] : k4_xboole_0(k2_xboole_0(A_11,B_12),k2_xboole_0(B_12,C_54)) = k4_xboole_0(k4_xboole_0(A_11,B_12),C_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_347])).

tff(c_2117,plain,(
    ! [A_109,B_110,C_111] : k4_xboole_0(k2_xboole_0(A_109,B_110),k2_xboole_0(B_110,C_111)) = k4_xboole_0(A_109,k2_xboole_0(B_110,C_111)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_391])).

tff(c_2512,plain,(
    ! [A_115,C_116] : k4_xboole_0(k1_xboole_0,k2_xboole_0(A_115,C_116)) = k4_xboole_0(A_115,k2_xboole_0(A_115,C_116)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_2117])).

tff(c_2658,plain,(
    ! [A_1,B_2] : k4_xboole_0(k1_xboole_0,k2_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2512])).

tff(c_22,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_131,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_131])).

tff(c_144,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_624,plain,(
    ! [A_70,B_71] : k4_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k3_xboole_0(A_70,k4_xboole_0(A_70,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_22])).

tff(c_669,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_624])).

tff(c_3206,plain,(
    ! [A_121,B_122,C_123] : k4_xboole_0(A_121,k2_xboole_0(k4_xboole_0(A_121,B_122),C_123)) = k4_xboole_0(k3_xboole_0(A_121,B_122),C_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_347])).

tff(c_3418,plain,(
    ! [A_121,B_122] : k4_xboole_0(k3_xboole_0(A_121,B_122),k1_xboole_0) = k4_xboole_0(A_121,k4_xboole_0(A_121,B_122)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3206])).

tff(c_3439,plain,(
    ! [A_124,B_125] : k4_xboole_0(k3_xboole_0(A_124,B_125),k1_xboole_0) = k3_xboole_0(A_124,B_125) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_3418])).

tff(c_3476,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),k1_xboole_0) = k3_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_669,c_3439])).

tff(c_3489,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),k1_xboole_0) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_3476])).

tff(c_3516,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),k4_xboole_0('#skF_1',k1_xboole_0)) = k3_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3489,c_22])).

tff(c_4513,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',k1_xboole_0))) = k3_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3516,c_18])).

tff(c_4538,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),k1_xboole_0) = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_53,c_4513])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_159,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_tarski(A_34,C_35)
      | ~ r1_tarski(k2_xboole_0(A_34,B_36),C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_202,plain,(
    ! [C_39,A_40] :
      ( r1_tarski(k1_xboole_0,C_39)
      | ~ r1_tarski(A_40,C_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_159])).

tff(c_229,plain,(
    ! [B_42,A_43] :
      ( r1_tarski(k1_xboole_0,B_42)
      | k4_xboole_0(A_43,B_42) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_202])).

tff(c_237,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(k1_xboole_0,k4_xboole_0(A_18,B_19))
      | k3_xboole_0(A_18,B_19) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_229])).

tff(c_3500,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0('#skF_1',k1_xboole_0))
    | k3_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3489,c_237])).

tff(c_3530,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3500])).

tff(c_4542,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4538,c_3530])).

tff(c_206,plain,(
    ! [A_41] : k4_xboole_0(k1_xboole_0,A_41) = k4_xboole_0(A_41,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_177])).

tff(c_218,plain,(
    ! [A_41] : k4_xboole_0(k1_xboole_0,k4_xboole_0(A_41,A_41)) = k3_xboole_0(k1_xboole_0,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_22])).

tff(c_1317,plain,(
    ! [A_102,C_103] : k4_xboole_0(k4_xboole_0(A_102,A_102),C_103) = k4_xboole_0(k1_xboole_0,k2_xboole_0(A_102,C_103)) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_347])).

tff(c_1432,plain,(
    ! [A_102] : k4_xboole_0(k1_xboole_0,k2_xboole_0(A_102,k4_xboole_0(A_102,A_102))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(A_102,A_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_1317])).

tff(c_5810,plain,(
    ! [A_145] : k4_xboole_0(k1_xboole_0,k2_xboole_0(A_145,k4_xboole_0(A_145,A_145))) = k3_xboole_0(k1_xboole_0,A_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_1432])).

tff(c_205,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k1_xboole_0,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_202])).

tff(c_1081,plain,(
    ! [C_90,A_91,B_92] :
      ( r1_tarski(k1_xboole_0,C_90)
      | k4_xboole_0(A_91,k2_xboole_0(B_92,C_90)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_205])).

tff(c_1112,plain,(
    ! [B_2,A_91,A_1] :
      ( r1_tarski(k1_xboole_0,B_2)
      | k4_xboole_0(A_91,k2_xboole_0(B_2,A_1)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1081])).

tff(c_6088,plain,(
    ! [A_148] :
      ( r1_tarski(k1_xboole_0,A_148)
      | k3_xboole_0(k1_xboole_0,A_148) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5810,c_1112])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6877,plain,(
    ! [A_156] :
      ( k4_xboole_0(k1_xboole_0,A_156) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,A_156) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6088,c_10])).

tff(c_195,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_177])).

tff(c_3437,plain,(
    ! [A_121,B_122] : k4_xboole_0(k3_xboole_0(A_121,B_122),k1_xboole_0) = k3_xboole_0(A_121,B_122) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_3418])).

tff(c_4135,plain,(
    ! [A_130,B_131] : k4_xboole_0(k2_xboole_0(A_130,B_131),k4_xboole_0(A_130,B_131)) = k3_xboole_0(k2_xboole_0(A_130,B_131),B_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_22])).

tff(c_4193,plain,(
    ! [A_121,B_122] : k4_xboole_0(k2_xboole_0(k3_xboole_0(A_121,B_122),k1_xboole_0),k3_xboole_0(A_121,B_122)) = k3_xboole_0(k2_xboole_0(k3_xboole_0(A_121,B_122),k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3437,c_4135])).

tff(c_4786,plain,(
    ! [A_136,B_137] : k4_xboole_0(k1_xboole_0,k3_xboole_0(A_136,B_137)) = k3_xboole_0(k3_xboole_0(A_136,B_137),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_2,c_195,c_4193])).

tff(c_4866,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_669,c_4786])).

tff(c_4887,plain,(
    k4_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',k1_xboole_0)) = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4538,c_669,c_4866])).

tff(c_6924,plain,
    ( k3_xboole_0('#skF_1',k1_xboole_0) = k1_xboole_0
    | k3_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',k1_xboole_0)) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6877,c_4887])).

tff(c_7193,plain,(
    k3_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',k1_xboole_0)) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_4542,c_6924])).

tff(c_539,plain,(
    ! [A_62,B_63,B_64] :
      ( r1_tarski(A_62,B_63)
      | k4_xboole_0(k2_xboole_0(A_62,B_64),B_63) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_159])).

tff(c_573,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(A_65,A_65)
      | k4_xboole_0(B_66,A_65) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_539])).

tff(c_752,plain,(
    ! [C_74,A_75,B_76] :
      ( r1_tarski(C_74,C_74)
      | k4_xboole_0(A_75,k2_xboole_0(B_76,C_74)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_573])).

tff(c_776,plain,(
    ! [A_75,A_10] :
      ( r1_tarski(k1_xboole_0,k1_xboole_0)
      | k4_xboole_0(A_75,A_10) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_752])).

tff(c_779,plain,(
    ! [A_77,A_78] : k4_xboole_0(A_77,A_78) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_776])).

tff(c_797,plain,(
    ! [A_18,B_19] : k3_xboole_0(A_18,B_19) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_779])).

tff(c_805,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_797,c_139])).

tff(c_806,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_776])).

tff(c_238,plain,(
    ! [A_44,B_45] :
      ( k2_xboole_0(A_44,k4_xboole_0(B_45,A_44)) = B_45
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_251,plain,(
    ! [B_45] :
      ( k4_xboole_0(B_45,k1_xboole_0) = B_45
      | ~ r1_tarski(k1_xboole_0,B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_53])).

tff(c_824,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_806,c_251])).

tff(c_4305,plain,(
    ! [A_121,B_122] : k4_xboole_0(k1_xboole_0,k3_xboole_0(A_121,B_122)) = k3_xboole_0(k3_xboole_0(A_121,B_122),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_2,c_195,c_4193])).

tff(c_369,plain,(
    ! [A_52,B_53,B_19] : k4_xboole_0(A_52,k2_xboole_0(B_53,k4_xboole_0(k4_xboole_0(A_52,B_53),B_19))) = k3_xboole_0(k4_xboole_0(A_52,B_53),B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_22])).

tff(c_6367,plain,(
    ! [A_150,B_151,B_152] : k4_xboole_0(A_150,k2_xboole_0(B_151,k4_xboole_0(A_150,k2_xboole_0(B_151,B_152)))) = k3_xboole_0(k4_xboole_0(A_150,B_151),B_152) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_369])).

tff(c_6635,plain,(
    ! [A_150,A_22] : k4_xboole_0(A_150,k2_xboole_0(k1_xboole_0,k4_xboole_0(A_150,A_22))) = k3_xboole_0(k4_xboole_0(A_150,k1_xboole_0),A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_6367])).

tff(c_6681,plain,(
    ! [A_150,A_22] : k3_xboole_0(k4_xboole_0(A_150,k1_xboole_0),A_22) = k3_xboole_0(A_150,A_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_53,c_6635])).

tff(c_8704,plain,(
    ! [A_178,B_179,C_180] : k4_xboole_0(k4_xboole_0(A_178,B_179),k4_xboole_0(A_178,k2_xboole_0(B_179,C_180))) = k3_xboole_0(k4_xboole_0(A_178,B_179),C_180) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_22])).

tff(c_9030,plain,(
    ! [A_178,A_22] : k4_xboole_0(k4_xboole_0(A_178,k1_xboole_0),k4_xboole_0(A_178,A_22)) = k3_xboole_0(k4_xboole_0(A_178,k1_xboole_0),A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_8704])).

tff(c_9807,plain,(
    ! [A_189,A_190] : k4_xboole_0(k4_xboole_0(A_189,k1_xboole_0),k4_xboole_0(A_189,A_190)) = k3_xboole_0(A_189,A_190) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6681,c_9030])).

tff(c_13481,plain,(
    ! [A_218] : k4_xboole_0(k1_xboole_0,k3_xboole_0(A_218,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(A_218,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9807,c_218])).

tff(c_13594,plain,(
    ! [A_121] : k3_xboole_0(k3_xboole_0(A_121,k1_xboole_0),k1_xboole_0) = k3_xboole_0(k1_xboole_0,k4_xboole_0(A_121,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4305,c_13481])).

tff(c_10266,plain,(
    ! [A_191] : k4_xboole_0(k1_xboole_0,k4_xboole_0(A_191,k1_xboole_0)) = k3_xboole_0(A_191,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9807,c_189])).

tff(c_10418,plain,(
    ! [A_13,B_14] : k4_xboole_0(k1_xboole_0,k4_xboole_0(A_13,k2_xboole_0(B_14,k1_xboole_0))) = k3_xboole_0(k4_xboole_0(A_13,B_14),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_10266])).

tff(c_10465,plain,(
    ! [A_13,B_14] : k4_xboole_0(k1_xboole_0,k4_xboole_0(A_13,B_14)) = k3_xboole_0(k4_xboole_0(A_13,B_14),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_10418])).

tff(c_1451,plain,(
    ! [A_104,C_105] : k4_xboole_0(k4_xboole_0(k1_xboole_0,A_104),C_105) = k4_xboole_0(A_104,k2_xboole_0(A_104,C_105)) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_347])).

tff(c_1706,plain,(
    ! [A_106] : k4_xboole_0(k4_xboole_0(k1_xboole_0,A_106),k1_xboole_0) = k4_xboole_0(A_106,A_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1451])).

tff(c_1865,plain,(
    ! [A_22] : k4_xboole_0(k4_xboole_0(A_22,A_22),k1_xboole_0) = k4_xboole_0(A_22,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_1706])).

tff(c_4226,plain,(
    ! [A_22] : k4_xboole_0(k2_xboole_0(k4_xboole_0(A_22,A_22),k1_xboole_0),k4_xboole_0(A_22,A_22)) = k3_xboole_0(k2_xboole_0(k4_xboole_0(A_22,A_22),k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1865,c_4135])).

tff(c_4311,plain,(
    ! [A_22] : k3_xboole_0(k4_xboole_0(A_22,A_22),k1_xboole_0) = k3_xboole_0(k1_xboole_0,A_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_2,c_218,c_195,c_4226])).

tff(c_6648,plain,(
    ! [A_150,A_10] : k4_xboole_0(A_150,k2_xboole_0(A_10,k4_xboole_0(A_150,A_10))) = k3_xboole_0(k4_xboole_0(A_150,A_10),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_6367])).

tff(c_23292,plain,(
    ! [A_264,B_265,B_266] : k4_xboole_0(A_264,k2_xboole_0(B_265,k4_xboole_0(A_264,B_266))) = k4_xboole_0(k3_xboole_0(A_264,B_266),B_265) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3206])).

tff(c_28783,plain,(
    ! [A_306,A_307] : k4_xboole_0(k3_xboole_0(A_306,A_307),A_307) = k3_xboole_0(k4_xboole_0(A_306,A_307),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6648,c_23292])).

tff(c_29050,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = k4_xboole_0(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_28783])).

tff(c_29106,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = k4_xboole_0('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_29050])).

tff(c_266,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(k4_xboole_0(A_18,B_19),k3_xboole_0(A_18,B_19)) = A_18
      | ~ r1_tarski(k4_xboole_0(A_18,B_19),A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_238])).

tff(c_274,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(k3_xboole_0(A_18,B_19),k4_xboole_0(A_18,B_19)) = A_18
      | ~ r1_tarski(k4_xboole_0(A_18,B_19),A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_266])).

tff(c_29127,plain,
    ( k2_xboole_0(k4_xboole_0('#skF_2','#skF_2'),k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0)) = k4_xboole_0('#skF_1','#skF_2')
    | ~ r1_tarski(k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0),k4_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_29106,c_274])).

tff(c_29140,plain,
    ( k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_2','#skF_2')) = k4_xboole_0('#skF_1','#skF_2')
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18,c_2,c_14,c_18,c_29127])).

tff(c_30397,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_29140])).

tff(c_30409,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_30397])).

tff(c_30416,plain,(
    k4_xboole_0('#skF_2','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_29106,c_6648,c_18,c_30409])).

tff(c_1033,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(k1_xboole_0,k4_xboole_0(A_88,B_89))
      | k3_xboole_0(A_88,B_89) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_229])).

tff(c_1078,plain,(
    ! [A_88,B_89] :
      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(A_88,B_89)) = k1_xboole_0
      | k3_xboole_0(A_88,B_89) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1033,c_10])).

tff(c_31296,plain,(
    ! [A_320,B_321] :
      ( k3_xboole_0(k4_xboole_0(A_320,B_321),k1_xboole_0) = k1_xboole_0
      | k3_xboole_0(A_320,B_321) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10465,c_1078])).

tff(c_31302,plain,
    ( k4_xboole_0('#skF_2','#skF_2') = k1_xboole_0
    | k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_31296,c_29106])).

tff(c_31646,plain,(
    k4_xboole_0('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_31302])).

tff(c_31648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30416,c_31646])).

tff(c_31649,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_2','#skF_2')) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_29140])).

tff(c_394,plain,(
    ! [A_18,B_19,C_54] : k4_xboole_0(A_18,k2_xboole_0(k4_xboole_0(A_18,B_19),C_54)) = k4_xboole_0(k3_xboole_0(A_18,B_19),C_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_347])).

tff(c_32241,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_2','#skF_2')) = k4_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_31649,c_394])).

tff(c_32322,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_4311,c_10465,c_139,c_22,c_32241])).

tff(c_9913,plain,(
    ! [A_189] : k4_xboole_0(k1_xboole_0,k3_xboole_0(A_189,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(A_189,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_9807,c_218])).

tff(c_29116,plain,(
    k3_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0('#skF_2','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_29106,c_9913])).

tff(c_29138,plain,(
    k3_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_2')) = k3_xboole_0(k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18,c_218,c_29116])).

tff(c_32337,plain,(
    k3_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32322,c_29138])).

tff(c_1805,plain,(
    ! [A_106] : k4_xboole_0(k4_xboole_0(k1_xboole_0,A_106),k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_1706,c_189])).

tff(c_4229,plain,(
    ! [A_106] : k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,A_106),k1_xboole_0),k4_xboole_0(k1_xboole_0,A_106)) = k3_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0,A_106),k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1805,c_4135])).

tff(c_4312,plain,(
    ! [A_106] : k3_xboole_0(k4_xboole_0(k1_xboole_0,A_106),k1_xboole_0) = k3_xboole_0(k1_xboole_0,A_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_2,c_22,c_195,c_4229])).

tff(c_23668,plain,(
    ! [A_150,A_10] : k4_xboole_0(k3_xboole_0(A_150,A_10),A_10) = k3_xboole_0(k4_xboole_0(A_150,A_10),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6648,c_23292])).

tff(c_32341,plain,(
    k3_xboole_0(k4_xboole_0(k1_xboole_0,'#skF_2'),k1_xboole_0) = k4_xboole_0(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_32322,c_23668])).

tff(c_32372,plain,(
    k4_xboole_0('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32322,c_189,c_4312,c_32341])).

tff(c_388,plain,(
    ! [A_22,C_54] : k4_xboole_0(k4_xboole_0(A_22,A_22),C_54) = k4_xboole_0(k1_xboole_0,k2_xboole_0(A_22,C_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_347])).

tff(c_39700,plain,(
    ! [C_355] : k4_xboole_0(k1_xboole_0,k2_xboole_0('#skF_2',C_355)) = k4_xboole_0(k1_xboole_0,C_355) ),
    inference(superposition,[status(thm),theory(equality)],[c_32372,c_388])).

tff(c_39931,plain,(
    ! [C_355] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,C_355)) = k3_xboole_0(k1_xboole_0,k2_xboole_0('#skF_2',C_355)) ),
    inference(superposition,[status(thm),theory(equality)],[c_39700,c_22])).

tff(c_40082,plain,(
    ! [C_355] : k3_xboole_0(k1_xboole_0,k2_xboole_0('#skF_2',C_355)) = k3_xboole_0(k1_xboole_0,C_355) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_39931])).

tff(c_31650,plain,(
    r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_29140])).

tff(c_31941,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_31650,c_10])).

tff(c_38490,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2'))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_31941])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_401,plain,(
    ! [A_52,B_53,B_19] : k4_xboole_0(A_52,k2_xboole_0(B_53,k4_xboole_0(A_52,k2_xboole_0(B_53,B_19)))) = k3_xboole_0(k4_xboole_0(A_52,B_53),B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_369])).

tff(c_10471,plain,(
    ! [C_192] : k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),C_192)) = k4_xboole_0(k3_xboole_0('#skF_1',k1_xboole_0),C_192) ),
    inference(superposition,[status(thm),theory(equality)],[c_4887,c_18])).

tff(c_10552,plain,(
    ! [C_192] :
      ( r1_tarski(k1_xboole_0,k4_xboole_0('#skF_1',k1_xboole_0))
      | k4_xboole_0(k3_xboole_0('#skF_1',k1_xboole_0),C_192) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10471,c_1112])).

tff(c_24223,plain,(
    ! [C_268] : k4_xboole_0(k3_xboole_0('#skF_1',k1_xboole_0),C_268) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10552])).

tff(c_24295,plain,(
    ! [B_53,B_19] : k3_xboole_0(k4_xboole_0(k3_xboole_0('#skF_1',k1_xboole_0),B_53),B_19) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_24223])).

tff(c_4929,plain,(
    ! [C_15] : k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),C_15)) = k4_xboole_0(k3_xboole_0('#skF_1',k1_xboole_0),C_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_4887,c_18])).

tff(c_75034,plain,(
    ! [A_474,B_475] :
      ( k3_xboole_0(k4_xboole_0(A_474,B_475),k1_xboole_0) = k1_xboole_0
      | k3_xboole_0(A_474,B_475) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10465,c_1078])).

tff(c_75429,plain,(
    ! [C_15] :
      ( k3_xboole_0(k4_xboole_0(k3_xboole_0('#skF_1',k1_xboole_0),C_15),k1_xboole_0) = k1_xboole_0
      | k3_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),C_15)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4929,c_75034])).

tff(c_76645,plain,(
    ! [C_486] : k3_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),C_486)) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_24295,c_75429])).

tff(c_78622,plain,(
    ! [B_496] :
      ( k3_xboole_0(k1_xboole_0,B_496) != k1_xboole_0
      | ~ r1_tarski(k4_xboole_0('#skF_1',k1_xboole_0),B_496) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_76645])).

tff(c_78657,plain,(
    ! [B_6] :
      ( k3_xboole_0(k1_xboole_0,B_6) != k1_xboole_0
      | k4_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_78622])).

tff(c_78674,plain,(
    ! [B_497] :
      ( k3_xboole_0(k1_xboole_0,B_497) != k1_xboole_0
      | k4_xboole_0('#skF_1',B_497) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_18,c_78657])).

tff(c_78772,plain,(
    k3_xboole_0(k1_xboole_0,k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2'))) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38490,c_78674])).

tff(c_78898,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32337,c_40082,c_78772])).

tff(c_78899,plain,(
    r1_tarski(k1_xboole_0,k4_xboole_0('#skF_1',k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_10552])).

tff(c_78923,plain,(
    k4_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78899,c_10])).

tff(c_79100,plain,(
    k3_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',k1_xboole_0)),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_78923,c_10465])).

tff(c_79221,plain,(
    k3_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_824,c_3489,c_13594,c_10465,c_79100])).

tff(c_79223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7193,c_79221])).

tff(c_79225,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3500])).

tff(c_79258,plain,(
    ! [A_499,B_500] : k4_xboole_0(k2_xboole_0(A_499,B_500),k4_xboole_0(A_499,B_500)) = k3_xboole_0(k2_xboole_0(A_499,B_500),B_500) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_22])).

tff(c_79301,plain,(
    k4_xboole_0(k2_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),k1_xboole_0),k4_xboole_0('#skF_1',k1_xboole_0)) = k3_xboole_0(k2_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3489,c_79258])).

tff(c_79413,plain,(
    k4_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_79225,c_53,c_2,c_195,c_79301])).

tff(c_546,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,A_1)
      | k4_xboole_0(B_2,A_1) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_539])).

tff(c_79489,plain,(
    r1_tarski(k4_xboole_0('#skF_1',k1_xboole_0),k4_xboole_0('#skF_1',k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_79413,c_546])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(k2_xboole_0(A_7,B_8),C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_535,plain,(
    ! [A_59,C_60,B_61] :
      ( r1_tarski(A_59,C_60)
      | ~ r1_tarski(B_61,C_60)
      | ~ r1_tarski(A_59,B_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_12])).

tff(c_538,plain,(
    ! [A_59,B_6,A_5] :
      ( r1_tarski(A_59,B_6)
      | ~ r1_tarski(A_59,A_5)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_535])).

tff(c_79612,plain,(
    ! [B_6] :
      ( r1_tarski(k4_xboole_0('#skF_1',k1_xboole_0),B_6)
      | k4_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_79489,c_538])).

tff(c_79624,plain,(
    ! [B_6] :
      ( r1_tarski(k4_xboole_0('#skF_1',k1_xboole_0),B_6)
      | k4_xboole_0('#skF_1',B_6) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_18,c_79612])).

tff(c_79511,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),k4_xboole_0('#skF_1',k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_79225,c_3516])).

tff(c_79555,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_79511,c_18])).

tff(c_79588,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_53,c_79555])).

tff(c_79853,plain,(
    ! [A_506,B_507] :
      ( k2_xboole_0(k3_xboole_0(A_506,B_507),k4_xboole_0(A_506,B_507)) = A_506
      | ~ r1_tarski(k4_xboole_0(A_506,B_507),A_506) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_266])).

tff(c_79923,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',k1_xboole_0)) = '#skF_1'
    | ~ r1_tarski(k4_xboole_0('#skF_1',k1_xboole_0),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_79588,c_79853])).

tff(c_80052,plain,
    ( k4_xboole_0('#skF_1',k1_xboole_0) = '#skF_1'
    | ~ r1_tarski(k4_xboole_0('#skF_1',k1_xboole_0),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_79923])).

tff(c_80147,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1',k1_xboole_0),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_80052])).

tff(c_80154,plain,(
    k4_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_79624,c_80147])).

tff(c_2226,plain,(
    ! [A_22,C_111] : k4_xboole_0(k1_xboole_0,k2_xboole_0(A_22,C_111)) = k4_xboole_0(A_22,k2_xboole_0(A_22,C_111)) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_2117])).

tff(c_3494,plain,(
    ! [C_54] : k4_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),k2_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),C_54)) = k4_xboole_0(k3_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),k1_xboole_0),C_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_3489,c_394])).

tff(c_3522,plain,(
    ! [C_54] : k4_xboole_0(k3_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),k1_xboole_0),C_54) = k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),C_54)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2226,c_3494])).

tff(c_80718,plain,(
    ! [C_514] : k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0('#skF_1',k1_xboole_0),C_514)) = k4_xboole_0(k1_xboole_0,C_514) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79225,c_3522])).

tff(c_2655,plain,(
    ! [B_2,A_1] : k4_xboole_0(k1_xboole_0,k2_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2512])).

tff(c_84571,plain,(
    ! [C_558] : k4_xboole_0(C_558,k2_xboole_0(C_558,k4_xboole_0('#skF_1',k1_xboole_0))) = k4_xboole_0(k1_xboole_0,C_558) ),
    inference(superposition,[status(thm),theory(equality)],[c_80718,c_2655])).

tff(c_84756,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,'#skF_1')
    | ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_84571])).

tff(c_84806,plain,
    ( k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_824,c_84756])).

tff(c_84807,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_80154,c_84806])).

tff(c_176,plain,(
    ! [A_34,B_6,B_36] :
      ( r1_tarski(A_34,B_6)
      | k4_xboole_0(k2_xboole_0(A_34,B_36),B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_159])).

tff(c_84822,plain,(
    ! [A_559,B_560] :
      ( r1_tarski(A_559,k4_xboole_0(A_559,B_560))
      | k3_xboole_0(k2_xboole_0(A_559,B_560),B_560) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79258,c_176])).

tff(c_84842,plain,(
    ! [A_10] :
      ( r1_tarski(A_10,k4_xboole_0(A_10,k1_xboole_0))
      | k3_xboole_0(A_10,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_84822])).

tff(c_991,plain,(
    ! [A_83,A_84,B_85] :
      ( r1_tarski(A_83,A_83)
      | k4_xboole_0(A_84,k2_xboole_0(A_83,B_85)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_752])).

tff(c_102249,plain,(
    ! [A_659,A_660,B_661] :
      ( r1_tarski(A_659,A_659)
      | k4_xboole_0(A_660,B_661) != k1_xboole_0
      | ~ r1_tarski(A_659,B_661) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_991])).

tff(c_102429,plain,(
    ! [A_662] :
      ( r1_tarski(A_662,A_662)
      | ~ r1_tarski(A_662,k4_xboole_0('#skF_1',k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79511,c_102249])).

tff(c_102438,plain,
    ( r1_tarski('#skF_1','#skF_1')
    | k3_xboole_0('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84842,c_102429])).

tff(c_102471,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79588,c_102438])).

tff(c_166,plain,(
    ! [C_35,A_22] :
      ( r1_tarski(k1_xboole_0,C_35)
      | ~ r1_tarski(A_22,C_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_159])).

tff(c_102503,plain,(
    r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(resolution,[status(thm)],[c_102471,c_166])).

tff(c_102514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84807,c_102503])).

tff(c_102515,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_80052])).

tff(c_103429,plain,(
    ! [C_670] : k4_xboole_0('#skF_1',k2_xboole_0(C_670,'#skF_1')) = k4_xboole_0(k1_xboole_0,C_670) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2658,c_102515,c_79588,c_102515,c_3522])).

tff(c_103507,plain,(
    ! [B_2] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_1',B_2)) = k4_xboole_0(k1_xboole_0,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_103429])).

tff(c_24,plain,(
    k4_xboole_0(k2_xboole_0('#skF_1','#skF_2'),'#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_27,plain,(
    k4_xboole_0('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_24])).

tff(c_80040,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_2')) = '#skF_1'
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_79853])).

tff(c_80090,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_80040])).

tff(c_80091,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_27,c_80090])).

tff(c_80094,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_80091])).

tff(c_80096,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18,c_80094])).

tff(c_103969,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103507,c_80096])).

tff(c_103970,plain,(
    k4_xboole_0('#skF_2','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_103969])).

tff(c_102523,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_102515,c_102515,c_79511])).

tff(c_111657,plain,(
    ! [B_739] : k4_xboole_0(k3_xboole_0('#skF_1',B_739),'#skF_1') = k4_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',B_739)) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_103429])).

tff(c_111734,plain,(
    k4_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_2')) = k4_xboole_0(k1_xboole_0,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_111657])).

tff(c_111752,plain,(
    k4_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_102523,c_189,c_111734])).

tff(c_275,plain,(
    ! [B_46] :
      ( k4_xboole_0(B_46,k1_xboole_0) = B_46
      | ~ r1_tarski(k1_xboole_0,B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_53])).

tff(c_280,plain,(
    ! [B_6] :
      ( k4_xboole_0(B_6,k1_xboole_0) = B_6
      | k4_xboole_0(k1_xboole_0,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_275])).

tff(c_111860,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_111752,c_280])).

tff(c_79406,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = k3_xboole_0(k2_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_79258])).

tff(c_111956,plain,(
    k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_2')),k4_xboole_0('#skF_1','#skF_2')) = k3_xboole_0(k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_111860,c_79406])).

tff(c_112026,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111752,c_53,c_2,c_16,c_111956])).

tff(c_398,plain,(
    ! [A_52,B_53,B_19] : k4_xboole_0(A_52,k2_xboole_0(B_53,k4_xboole_0(k4_xboole_0(A_52,B_53),B_19))) = k3_xboole_0(k4_xboole_0(A_52,B_53),B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_347])).

tff(c_103521,plain,(
    ! [A_671,B_672,B_673] : k4_xboole_0(A_671,k2_xboole_0(B_672,k4_xboole_0(A_671,k2_xboole_0(B_672,B_673)))) = k3_xboole_0(k4_xboole_0(A_671,B_672),B_673) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_398])).

tff(c_774,plain,(
    ! [A_1,A_75,B_2] :
      ( r1_tarski(A_1,A_1)
      | k4_xboole_0(A_75,k2_xboole_0(A_1,B_2)) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_752])).

tff(c_103604,plain,(
    ! [B_672,A_671,B_673] :
      ( r1_tarski(B_672,B_672)
      | k3_xboole_0(k4_xboole_0(A_671,B_672),B_673) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103521,c_774])).

tff(c_112074,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_112026,c_103604])).

tff(c_112091,plain,(
    k4_xboole_0('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_112074,c_10])).

tff(c_112099,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103970,c_112091])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:19:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.63/26.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.78/26.88  
% 36.78/26.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.78/26.88  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 36.78/26.88  
% 36.78/26.88  %Foreground sorts:
% 36.78/26.88  
% 36.78/26.88  
% 36.78/26.88  %Background operators:
% 36.78/26.88  
% 36.78/26.88  
% 36.78/26.88  %Foreground operators:
% 36.78/26.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.78/26.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 36.78/26.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 36.78/26.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 36.78/26.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 36.78/26.88  tff('#skF_2', type, '#skF_2': $i).
% 36.78/26.88  tff('#skF_1', type, '#skF_1': $i).
% 36.78/26.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.78/26.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.78/26.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 36.78/26.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 36.78/26.88  
% 36.78/26.91  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 36.78/26.91  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 36.78/26.91  tff(f_43, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 36.78/26.91  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 36.78/26.91  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 36.78/26.91  tff(f_56, negated_conjecture, ~(![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 36.78/26.91  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 36.78/26.91  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 36.78/26.91  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 36.78/26.91  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 36.78/26.91  tff(c_37, plain, (![B_21, A_22]: (k2_xboole_0(B_21, A_22)=k2_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_27])).
% 36.78/26.91  tff(c_14, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 36.78/26.91  tff(c_53, plain, (![A_22]: (k2_xboole_0(k1_xboole_0, A_22)=A_22)), inference(superposition, [status(thm), theory('equality')], [c_37, c_14])).
% 36.78/26.91  tff(c_177, plain, (![A_37, B_38]: (k4_xboole_0(k2_xboole_0(A_37, B_38), B_38)=k4_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.78/26.91  tff(c_189, plain, (![A_22]: (k4_xboole_0(k1_xboole_0, A_22)=k4_xboole_0(A_22, A_22))), inference(superposition, [status(thm), theory('equality')], [c_53, c_177])).
% 36.78/26.91  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 36.78/26.91  tff(c_18, plain, (![A_13, B_14, C_15]: (k4_xboole_0(k4_xboole_0(A_13, B_14), C_15)=k4_xboole_0(A_13, k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 36.78/26.91  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(k2_xboole_0(A_11, B_12), B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 36.78/26.91  tff(c_347, plain, (![A_52, B_53, C_54]: (k4_xboole_0(k4_xboole_0(A_52, B_53), C_54)=k4_xboole_0(A_52, k2_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 36.78/26.91  tff(c_391, plain, (![A_11, B_12, C_54]: (k4_xboole_0(k2_xboole_0(A_11, B_12), k2_xboole_0(B_12, C_54))=k4_xboole_0(k4_xboole_0(A_11, B_12), C_54))), inference(superposition, [status(thm), theory('equality')], [c_16, c_347])).
% 36.78/26.91  tff(c_2117, plain, (![A_109, B_110, C_111]: (k4_xboole_0(k2_xboole_0(A_109, B_110), k2_xboole_0(B_110, C_111))=k4_xboole_0(A_109, k2_xboole_0(B_110, C_111)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_391])).
% 36.78/26.91  tff(c_2512, plain, (![A_115, C_116]: (k4_xboole_0(k1_xboole_0, k2_xboole_0(A_115, C_116))=k4_xboole_0(A_115, k2_xboole_0(A_115, C_116)))), inference(superposition, [status(thm), theory('equality')], [c_53, c_2117])).
% 36.78/26.91  tff(c_2658, plain, (![A_1, B_2]: (k4_xboole_0(k1_xboole_0, k2_xboole_0(A_1, B_2))=k4_xboole_0(A_1, k2_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2512])).
% 36.78/26.91  tff(c_22, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 36.78/26.91  tff(c_26, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 36.78/26.91  tff(c_131, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 36.78/26.91  tff(c_139, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_131])).
% 36.78/26.91  tff(c_144, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_51])).
% 36.78/26.91  tff(c_624, plain, (![A_70, B_71]: (k4_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k3_xboole_0(A_70, k4_xboole_0(A_70, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_144, c_22])).
% 36.78/26.91  tff(c_669, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_139, c_624])).
% 36.78/26.91  tff(c_3206, plain, (![A_121, B_122, C_123]: (k4_xboole_0(A_121, k2_xboole_0(k4_xboole_0(A_121, B_122), C_123))=k4_xboole_0(k3_xboole_0(A_121, B_122), C_123))), inference(superposition, [status(thm), theory('equality')], [c_22, c_347])).
% 36.78/26.91  tff(c_3418, plain, (![A_121, B_122]: (k4_xboole_0(k3_xboole_0(A_121, B_122), k1_xboole_0)=k4_xboole_0(A_121, k4_xboole_0(A_121, B_122)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_3206])).
% 36.78/26.91  tff(c_3439, plain, (![A_124, B_125]: (k4_xboole_0(k3_xboole_0(A_124, B_125), k1_xboole_0)=k3_xboole_0(A_124, B_125))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_3418])).
% 36.78/26.91  tff(c_3476, plain, (k4_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), k1_xboole_0)=k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_669, c_3439])).
% 36.78/26.91  tff(c_3489, plain, (k4_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), k1_xboole_0)=k4_xboole_0('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_669, c_3476])).
% 36.78/26.91  tff(c_3516, plain, (k4_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), k4_xboole_0('#skF_1', k1_xboole_0))=k3_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3489, c_22])).
% 36.78/26.91  tff(c_4513, plain, (k4_xboole_0('#skF_1', k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', k1_xboole_0)))=k3_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3516, c_18])).
% 36.78/26.91  tff(c_4538, plain, (k3_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), k1_xboole_0)=k3_xboole_0('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_53, c_4513])).
% 36.78/26.91  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 36.78/26.91  tff(c_159, plain, (![A_34, C_35, B_36]: (r1_tarski(A_34, C_35) | ~r1_tarski(k2_xboole_0(A_34, B_36), C_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 36.78/26.91  tff(c_202, plain, (![C_39, A_40]: (r1_tarski(k1_xboole_0, C_39) | ~r1_tarski(A_40, C_39))), inference(superposition, [status(thm), theory('equality')], [c_53, c_159])).
% 36.78/26.91  tff(c_229, plain, (![B_42, A_43]: (r1_tarski(k1_xboole_0, B_42) | k4_xboole_0(A_43, B_42)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_202])).
% 36.78/26.91  tff(c_237, plain, (![A_18, B_19]: (r1_tarski(k1_xboole_0, k4_xboole_0(A_18, B_19)) | k3_xboole_0(A_18, B_19)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_229])).
% 36.78/26.91  tff(c_3500, plain, (r1_tarski(k1_xboole_0, k4_xboole_0('#skF_1', k1_xboole_0)) | k3_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3489, c_237])).
% 36.78/26.91  tff(c_3530, plain, (k3_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3500])).
% 36.78/26.91  tff(c_4542, plain, (k3_xboole_0('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4538, c_3530])).
% 36.78/26.91  tff(c_206, plain, (![A_41]: (k4_xboole_0(k1_xboole_0, A_41)=k4_xboole_0(A_41, A_41))), inference(superposition, [status(thm), theory('equality')], [c_53, c_177])).
% 36.78/26.91  tff(c_218, plain, (![A_41]: (k4_xboole_0(k1_xboole_0, k4_xboole_0(A_41, A_41))=k3_xboole_0(k1_xboole_0, A_41))), inference(superposition, [status(thm), theory('equality')], [c_206, c_22])).
% 36.78/26.91  tff(c_1317, plain, (![A_102, C_103]: (k4_xboole_0(k4_xboole_0(A_102, A_102), C_103)=k4_xboole_0(k1_xboole_0, k2_xboole_0(A_102, C_103)))), inference(superposition, [status(thm), theory('equality')], [c_189, c_347])).
% 36.78/26.91  tff(c_1432, plain, (![A_102]: (k4_xboole_0(k1_xboole_0, k2_xboole_0(A_102, k4_xboole_0(A_102, A_102)))=k4_xboole_0(k1_xboole_0, k4_xboole_0(A_102, A_102)))), inference(superposition, [status(thm), theory('equality')], [c_189, c_1317])).
% 36.78/26.91  tff(c_5810, plain, (![A_145]: (k4_xboole_0(k1_xboole_0, k2_xboole_0(A_145, k4_xboole_0(A_145, A_145)))=k3_xboole_0(k1_xboole_0, A_145))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_1432])).
% 36.78/26.91  tff(c_205, plain, (![B_6, A_5]: (r1_tarski(k1_xboole_0, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_202])).
% 36.78/26.91  tff(c_1081, plain, (![C_90, A_91, B_92]: (r1_tarski(k1_xboole_0, C_90) | k4_xboole_0(A_91, k2_xboole_0(B_92, C_90))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_347, c_205])).
% 36.78/26.91  tff(c_1112, plain, (![B_2, A_91, A_1]: (r1_tarski(k1_xboole_0, B_2) | k4_xboole_0(A_91, k2_xboole_0(B_2, A_1))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1081])).
% 36.78/26.91  tff(c_6088, plain, (![A_148]: (r1_tarski(k1_xboole_0, A_148) | k3_xboole_0(k1_xboole_0, A_148)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5810, c_1112])).
% 36.78/26.91  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 36.78/26.91  tff(c_6877, plain, (![A_156]: (k4_xboole_0(k1_xboole_0, A_156)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, A_156)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6088, c_10])).
% 36.78/26.91  tff(c_195, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_177])).
% 36.78/26.91  tff(c_3437, plain, (![A_121, B_122]: (k4_xboole_0(k3_xboole_0(A_121, B_122), k1_xboole_0)=k3_xboole_0(A_121, B_122))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_3418])).
% 36.78/26.91  tff(c_4135, plain, (![A_130, B_131]: (k4_xboole_0(k2_xboole_0(A_130, B_131), k4_xboole_0(A_130, B_131))=k3_xboole_0(k2_xboole_0(A_130, B_131), B_131))), inference(superposition, [status(thm), theory('equality')], [c_177, c_22])).
% 36.78/26.91  tff(c_4193, plain, (![A_121, B_122]: (k4_xboole_0(k2_xboole_0(k3_xboole_0(A_121, B_122), k1_xboole_0), k3_xboole_0(A_121, B_122))=k3_xboole_0(k2_xboole_0(k3_xboole_0(A_121, B_122), k1_xboole_0), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3437, c_4135])).
% 36.78/26.91  tff(c_4786, plain, (![A_136, B_137]: (k4_xboole_0(k1_xboole_0, k3_xboole_0(A_136, B_137))=k3_xboole_0(k3_xboole_0(A_136, B_137), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_2, c_195, c_4193])).
% 36.78/26.91  tff(c_4866, plain, (k3_xboole_0(k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2')), k1_xboole_0)=k4_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_669, c_4786])).
% 36.78/26.91  tff(c_4887, plain, (k4_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', k1_xboole_0))=k3_xboole_0('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4538, c_669, c_4866])).
% 36.78/26.91  tff(c_6924, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', k1_xboole_0))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6877, c_4887])).
% 36.78/26.91  tff(c_7193, plain, (k3_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', k1_xboole_0))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_4542, c_6924])).
% 36.78/26.91  tff(c_539, plain, (![A_62, B_63, B_64]: (r1_tarski(A_62, B_63) | k4_xboole_0(k2_xboole_0(A_62, B_64), B_63)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_159])).
% 36.78/26.91  tff(c_573, plain, (![A_65, B_66]: (r1_tarski(A_65, A_65) | k4_xboole_0(B_66, A_65)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_195, c_539])).
% 36.78/26.91  tff(c_752, plain, (![C_74, A_75, B_76]: (r1_tarski(C_74, C_74) | k4_xboole_0(A_75, k2_xboole_0(B_76, C_74))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_573])).
% 36.78/26.91  tff(c_776, plain, (![A_75, A_10]: (r1_tarski(k1_xboole_0, k1_xboole_0) | k4_xboole_0(A_75, A_10)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_752])).
% 36.78/26.91  tff(c_779, plain, (![A_77, A_78]: (k4_xboole_0(A_77, A_78)!=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_776])).
% 36.78/26.91  tff(c_797, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_779])).
% 36.78/26.91  tff(c_805, plain, $false, inference(negUnitSimplification, [status(thm)], [c_797, c_139])).
% 36.78/26.91  tff(c_806, plain, (r1_tarski(k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_776])).
% 36.78/26.91  tff(c_238, plain, (![A_44, B_45]: (k2_xboole_0(A_44, k4_xboole_0(B_45, A_44))=B_45 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 36.78/26.91  tff(c_251, plain, (![B_45]: (k4_xboole_0(B_45, k1_xboole_0)=B_45 | ~r1_tarski(k1_xboole_0, B_45))), inference(superposition, [status(thm), theory('equality')], [c_238, c_53])).
% 36.78/26.91  tff(c_824, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_806, c_251])).
% 36.78/26.91  tff(c_4305, plain, (![A_121, B_122]: (k4_xboole_0(k1_xboole_0, k3_xboole_0(A_121, B_122))=k3_xboole_0(k3_xboole_0(A_121, B_122), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_2, c_195, c_4193])).
% 36.78/26.91  tff(c_369, plain, (![A_52, B_53, B_19]: (k4_xboole_0(A_52, k2_xboole_0(B_53, k4_xboole_0(k4_xboole_0(A_52, B_53), B_19)))=k3_xboole_0(k4_xboole_0(A_52, B_53), B_19))), inference(superposition, [status(thm), theory('equality')], [c_347, c_22])).
% 36.78/26.91  tff(c_6367, plain, (![A_150, B_151, B_152]: (k4_xboole_0(A_150, k2_xboole_0(B_151, k4_xboole_0(A_150, k2_xboole_0(B_151, B_152))))=k3_xboole_0(k4_xboole_0(A_150, B_151), B_152))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_369])).
% 36.78/26.91  tff(c_6635, plain, (![A_150, A_22]: (k4_xboole_0(A_150, k2_xboole_0(k1_xboole_0, k4_xboole_0(A_150, A_22)))=k3_xboole_0(k4_xboole_0(A_150, k1_xboole_0), A_22))), inference(superposition, [status(thm), theory('equality')], [c_53, c_6367])).
% 36.78/26.91  tff(c_6681, plain, (![A_150, A_22]: (k3_xboole_0(k4_xboole_0(A_150, k1_xboole_0), A_22)=k3_xboole_0(A_150, A_22))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_53, c_6635])).
% 36.78/26.91  tff(c_8704, plain, (![A_178, B_179, C_180]: (k4_xboole_0(k4_xboole_0(A_178, B_179), k4_xboole_0(A_178, k2_xboole_0(B_179, C_180)))=k3_xboole_0(k4_xboole_0(A_178, B_179), C_180))), inference(superposition, [status(thm), theory('equality')], [c_347, c_22])).
% 36.78/26.91  tff(c_9030, plain, (![A_178, A_22]: (k4_xboole_0(k4_xboole_0(A_178, k1_xboole_0), k4_xboole_0(A_178, A_22))=k3_xboole_0(k4_xboole_0(A_178, k1_xboole_0), A_22))), inference(superposition, [status(thm), theory('equality')], [c_53, c_8704])).
% 36.78/26.91  tff(c_9807, plain, (![A_189, A_190]: (k4_xboole_0(k4_xboole_0(A_189, k1_xboole_0), k4_xboole_0(A_189, A_190))=k3_xboole_0(A_189, A_190))), inference(demodulation, [status(thm), theory('equality')], [c_6681, c_9030])).
% 36.78/26.91  tff(c_13481, plain, (![A_218]: (k4_xboole_0(k1_xboole_0, k3_xboole_0(A_218, k1_xboole_0))=k3_xboole_0(k1_xboole_0, k4_xboole_0(A_218, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_9807, c_218])).
% 36.78/26.91  tff(c_13594, plain, (![A_121]: (k3_xboole_0(k3_xboole_0(A_121, k1_xboole_0), k1_xboole_0)=k3_xboole_0(k1_xboole_0, k4_xboole_0(A_121, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_4305, c_13481])).
% 36.78/26.91  tff(c_10266, plain, (![A_191]: (k4_xboole_0(k1_xboole_0, k4_xboole_0(A_191, k1_xboole_0))=k3_xboole_0(A_191, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_9807, c_189])).
% 36.78/26.91  tff(c_10418, plain, (![A_13, B_14]: (k4_xboole_0(k1_xboole_0, k4_xboole_0(A_13, k2_xboole_0(B_14, k1_xboole_0)))=k3_xboole_0(k4_xboole_0(A_13, B_14), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_10266])).
% 36.78/26.91  tff(c_10465, plain, (![A_13, B_14]: (k4_xboole_0(k1_xboole_0, k4_xboole_0(A_13, B_14))=k3_xboole_0(k4_xboole_0(A_13, B_14), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_10418])).
% 36.78/26.91  tff(c_1451, plain, (![A_104, C_105]: (k4_xboole_0(k4_xboole_0(k1_xboole_0, A_104), C_105)=k4_xboole_0(A_104, k2_xboole_0(A_104, C_105)))), inference(superposition, [status(thm), theory('equality')], [c_189, c_347])).
% 36.78/26.91  tff(c_1706, plain, (![A_106]: (k4_xboole_0(k4_xboole_0(k1_xboole_0, A_106), k1_xboole_0)=k4_xboole_0(A_106, A_106))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1451])).
% 36.78/26.91  tff(c_1865, plain, (![A_22]: (k4_xboole_0(k4_xboole_0(A_22, A_22), k1_xboole_0)=k4_xboole_0(A_22, A_22))), inference(superposition, [status(thm), theory('equality')], [c_189, c_1706])).
% 36.78/26.91  tff(c_4226, plain, (![A_22]: (k4_xboole_0(k2_xboole_0(k4_xboole_0(A_22, A_22), k1_xboole_0), k4_xboole_0(A_22, A_22))=k3_xboole_0(k2_xboole_0(k4_xboole_0(A_22, A_22), k1_xboole_0), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1865, c_4135])).
% 36.78/26.91  tff(c_4311, plain, (![A_22]: (k3_xboole_0(k4_xboole_0(A_22, A_22), k1_xboole_0)=k3_xboole_0(k1_xboole_0, A_22))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_2, c_218, c_195, c_4226])).
% 36.78/26.91  tff(c_6648, plain, (![A_150, A_10]: (k4_xboole_0(A_150, k2_xboole_0(A_10, k4_xboole_0(A_150, A_10)))=k3_xboole_0(k4_xboole_0(A_150, A_10), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_6367])).
% 36.78/26.91  tff(c_23292, plain, (![A_264, B_265, B_266]: (k4_xboole_0(A_264, k2_xboole_0(B_265, k4_xboole_0(A_264, B_266)))=k4_xboole_0(k3_xboole_0(A_264, B_266), B_265))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3206])).
% 36.78/26.91  tff(c_28783, plain, (![A_306, A_307]: (k4_xboole_0(k3_xboole_0(A_306, A_307), A_307)=k3_xboole_0(k4_xboole_0(A_306, A_307), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6648, c_23292])).
% 36.78/26.91  tff(c_29050, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)=k4_xboole_0(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_139, c_28783])).
% 36.78/26.91  tff(c_29106, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_29050])).
% 36.78/26.91  tff(c_266, plain, (![A_18, B_19]: (k2_xboole_0(k4_xboole_0(A_18, B_19), k3_xboole_0(A_18, B_19))=A_18 | ~r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(superposition, [status(thm), theory('equality')], [c_22, c_238])).
% 36.78/26.91  tff(c_274, plain, (![A_18, B_19]: (k2_xboole_0(k3_xboole_0(A_18, B_19), k4_xboole_0(A_18, B_19))=A_18 | ~r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_266])).
% 36.78/26.91  tff(c_29127, plain, (k2_xboole_0(k4_xboole_0('#skF_2', '#skF_2'), k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0))=k4_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0), k4_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_29106, c_274])).
% 36.78/26.91  tff(c_29140, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_2', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18, c_2, c_14, c_18, c_29127])).
% 36.78/26.91  tff(c_30397, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_29140])).
% 36.78/26.91  tff(c_30409, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_30397])).
% 36.78/26.91  tff(c_30416, plain, (k4_xboole_0('#skF_2', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_29106, c_6648, c_18, c_30409])).
% 36.78/26.91  tff(c_1033, plain, (![A_88, B_89]: (r1_tarski(k1_xboole_0, k4_xboole_0(A_88, B_89)) | k3_xboole_0(A_88, B_89)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_229])).
% 36.78/26.91  tff(c_1078, plain, (![A_88, B_89]: (k4_xboole_0(k1_xboole_0, k4_xboole_0(A_88, B_89))=k1_xboole_0 | k3_xboole_0(A_88, B_89)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1033, c_10])).
% 36.78/26.91  tff(c_31296, plain, (![A_320, B_321]: (k3_xboole_0(k4_xboole_0(A_320, B_321), k1_xboole_0)=k1_xboole_0 | k3_xboole_0(A_320, B_321)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10465, c_1078])).
% 36.78/26.91  tff(c_31302, plain, (k4_xboole_0('#skF_2', '#skF_2')=k1_xboole_0 | k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_31296, c_29106])).
% 36.78/26.91  tff(c_31646, plain, (k4_xboole_0('#skF_2', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_139, c_31302])).
% 36.78/26.91  tff(c_31648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30416, c_31646])).
% 36.78/26.91  tff(c_31649, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_2', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_29140])).
% 36.78/26.91  tff(c_394, plain, (![A_18, B_19, C_54]: (k4_xboole_0(A_18, k2_xboole_0(k4_xboole_0(A_18, B_19), C_54))=k4_xboole_0(k3_xboole_0(A_18, B_19), C_54))), inference(superposition, [status(thm), theory('equality')], [c_22, c_347])).
% 36.78/26.91  tff(c_32241, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_2', '#skF_2'))=k4_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_31649, c_394])).
% 36.78/26.91  tff(c_32322, plain, (k3_xboole_0(k1_xboole_0, '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_139, c_4311, c_10465, c_139, c_22, c_32241])).
% 36.78/26.91  tff(c_9913, plain, (![A_189]: (k4_xboole_0(k1_xboole_0, k3_xboole_0(A_189, k1_xboole_0))=k3_xboole_0(k1_xboole_0, k4_xboole_0(A_189, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_9807, c_218])).
% 36.78/26.91  tff(c_29116, plain, (k3_xboole_0(k1_xboole_0, k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0))=k4_xboole_0(k1_xboole_0, k4_xboole_0('#skF_2', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_29106, c_9913])).
% 36.78/26.91  tff(c_29138, plain, (k3_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_2'))=k3_xboole_0(k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18, c_218, c_29116])).
% 36.78/26.91  tff(c_32337, plain, (k3_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32322, c_29138])).
% 36.78/26.91  tff(c_1805, plain, (![A_106]: (k4_xboole_0(k4_xboole_0(k1_xboole_0, A_106), k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_106))), inference(superposition, [status(thm), theory('equality')], [c_1706, c_189])).
% 36.78/26.91  tff(c_4229, plain, (![A_106]: (k4_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0, A_106), k1_xboole_0), k4_xboole_0(k1_xboole_0, A_106))=k3_xboole_0(k2_xboole_0(k4_xboole_0(k1_xboole_0, A_106), k1_xboole_0), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1805, c_4135])).
% 36.78/26.91  tff(c_4312, plain, (![A_106]: (k3_xboole_0(k4_xboole_0(k1_xboole_0, A_106), k1_xboole_0)=k3_xboole_0(k1_xboole_0, A_106))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_2, c_22, c_195, c_4229])).
% 36.78/26.91  tff(c_23668, plain, (![A_150, A_10]: (k4_xboole_0(k3_xboole_0(A_150, A_10), A_10)=k3_xboole_0(k4_xboole_0(A_150, A_10), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6648, c_23292])).
% 36.78/26.91  tff(c_32341, plain, (k3_xboole_0(k4_xboole_0(k1_xboole_0, '#skF_2'), k1_xboole_0)=k4_xboole_0(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_32322, c_23668])).
% 36.78/26.91  tff(c_32372, plain, (k4_xboole_0('#skF_2', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32322, c_189, c_4312, c_32341])).
% 36.78/26.91  tff(c_388, plain, (![A_22, C_54]: (k4_xboole_0(k4_xboole_0(A_22, A_22), C_54)=k4_xboole_0(k1_xboole_0, k2_xboole_0(A_22, C_54)))), inference(superposition, [status(thm), theory('equality')], [c_189, c_347])).
% 36.78/26.91  tff(c_39700, plain, (![C_355]: (k4_xboole_0(k1_xboole_0, k2_xboole_0('#skF_2', C_355))=k4_xboole_0(k1_xboole_0, C_355))), inference(superposition, [status(thm), theory('equality')], [c_32372, c_388])).
% 36.78/26.91  tff(c_39931, plain, (![C_355]: (k4_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, C_355))=k3_xboole_0(k1_xboole_0, k2_xboole_0('#skF_2', C_355)))), inference(superposition, [status(thm), theory('equality')], [c_39700, c_22])).
% 36.78/26.91  tff(c_40082, plain, (![C_355]: (k3_xboole_0(k1_xboole_0, k2_xboole_0('#skF_2', C_355))=k3_xboole_0(k1_xboole_0, C_355))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_39931])).
% 36.78/26.91  tff(c_31650, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_29140])).
% 36.78/26.91  tff(c_31941, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_31650, c_10])).
% 36.78/26.91  tff(c_38490, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2')))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_18, c_31941])).
% 36.78/26.91  tff(c_20, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 36.78/26.91  tff(c_401, plain, (![A_52, B_53, B_19]: (k4_xboole_0(A_52, k2_xboole_0(B_53, k4_xboole_0(A_52, k2_xboole_0(B_53, B_19))))=k3_xboole_0(k4_xboole_0(A_52, B_53), B_19))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_369])).
% 36.78/26.91  tff(c_10471, plain, (![C_192]: (k4_xboole_0(k1_xboole_0, k2_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), C_192))=k4_xboole_0(k3_xboole_0('#skF_1', k1_xboole_0), C_192))), inference(superposition, [status(thm), theory('equality')], [c_4887, c_18])).
% 36.78/26.91  tff(c_10552, plain, (![C_192]: (r1_tarski(k1_xboole_0, k4_xboole_0('#skF_1', k1_xboole_0)) | k4_xboole_0(k3_xboole_0('#skF_1', k1_xboole_0), C_192)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10471, c_1112])).
% 36.78/26.91  tff(c_24223, plain, (![C_268]: (k4_xboole_0(k3_xboole_0('#skF_1', k1_xboole_0), C_268)!=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_10552])).
% 36.78/26.91  tff(c_24295, plain, (![B_53, B_19]: (k3_xboole_0(k4_xboole_0(k3_xboole_0('#skF_1', k1_xboole_0), B_53), B_19)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_401, c_24223])).
% 36.78/26.91  tff(c_4929, plain, (![C_15]: (k4_xboole_0(k1_xboole_0, k2_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), C_15))=k4_xboole_0(k3_xboole_0('#skF_1', k1_xboole_0), C_15))), inference(superposition, [status(thm), theory('equality')], [c_4887, c_18])).
% 36.78/26.91  tff(c_75034, plain, (![A_474, B_475]: (k3_xboole_0(k4_xboole_0(A_474, B_475), k1_xboole_0)=k1_xboole_0 | k3_xboole_0(A_474, B_475)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10465, c_1078])).
% 36.78/26.91  tff(c_75429, plain, (![C_15]: (k3_xboole_0(k4_xboole_0(k3_xboole_0('#skF_1', k1_xboole_0), C_15), k1_xboole_0)=k1_xboole_0 | k3_xboole_0(k1_xboole_0, k2_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), C_15))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4929, c_75034])).
% 36.78/26.91  tff(c_76645, plain, (![C_486]: (k3_xboole_0(k1_xboole_0, k2_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), C_486))!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_24295, c_75429])).
% 36.78/26.91  tff(c_78622, plain, (![B_496]: (k3_xboole_0(k1_xboole_0, B_496)!=k1_xboole_0 | ~r1_tarski(k4_xboole_0('#skF_1', k1_xboole_0), B_496))), inference(superposition, [status(thm), theory('equality')], [c_20, c_76645])).
% 36.78/26.91  tff(c_78657, plain, (![B_6]: (k3_xboole_0(k1_xboole_0, B_6)!=k1_xboole_0 | k4_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_78622])).
% 36.78/26.91  tff(c_78674, plain, (![B_497]: (k3_xboole_0(k1_xboole_0, B_497)!=k1_xboole_0 | k4_xboole_0('#skF_1', B_497)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_53, c_18, c_78657])).
% 36.78/26.91  tff(c_78772, plain, (k3_xboole_0(k1_xboole_0, k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2')))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_38490, c_78674])).
% 36.78/26.91  tff(c_78898, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32337, c_40082, c_78772])).
% 36.78/26.91  tff(c_78899, plain, (r1_tarski(k1_xboole_0, k4_xboole_0('#skF_1', k1_xboole_0))), inference(splitRight, [status(thm)], [c_10552])).
% 36.78/26.91  tff(c_78923, plain, (k4_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_78899, c_10])).
% 36.78/26.91  tff(c_79100, plain, (k3_xboole_0(k4_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', k1_xboole_0)), k1_xboole_0)=k4_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_78923, c_10465])).
% 36.78/26.91  tff(c_79221, plain, (k3_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_824, c_3489, c_13594, c_10465, c_79100])).
% 36.78/26.91  tff(c_79223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7193, c_79221])).
% 36.78/26.91  tff(c_79225, plain, (k3_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_3500])).
% 36.78/26.91  tff(c_79258, plain, (![A_499, B_500]: (k4_xboole_0(k2_xboole_0(A_499, B_500), k4_xboole_0(A_499, B_500))=k3_xboole_0(k2_xboole_0(A_499, B_500), B_500))), inference(superposition, [status(thm), theory('equality')], [c_177, c_22])).
% 36.78/26.91  tff(c_79301, plain, (k4_xboole_0(k2_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), k1_xboole_0), k4_xboole_0('#skF_1', k1_xboole_0))=k3_xboole_0(k2_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), k1_xboole_0), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3489, c_79258])).
% 36.78/26.91  tff(c_79413, plain, (k4_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_79225, c_53, c_2, c_195, c_79301])).
% 36.78/26.91  tff(c_546, plain, (![A_1, B_2]: (r1_tarski(A_1, A_1) | k4_xboole_0(B_2, A_1)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_195, c_539])).
% 36.78/26.91  tff(c_79489, plain, (r1_tarski(k4_xboole_0('#skF_1', k1_xboole_0), k4_xboole_0('#skF_1', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_79413, c_546])).
% 36.78/26.91  tff(c_12, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(k2_xboole_0(A_7, B_8), C_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 36.78/26.91  tff(c_535, plain, (![A_59, C_60, B_61]: (r1_tarski(A_59, C_60) | ~r1_tarski(B_61, C_60) | ~r1_tarski(A_59, B_61))), inference(superposition, [status(thm), theory('equality')], [c_238, c_12])).
% 36.78/26.91  tff(c_538, plain, (![A_59, B_6, A_5]: (r1_tarski(A_59, B_6) | ~r1_tarski(A_59, A_5) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_535])).
% 36.78/26.91  tff(c_79612, plain, (![B_6]: (r1_tarski(k4_xboole_0('#skF_1', k1_xboole_0), B_6) | k4_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_79489, c_538])).
% 36.78/26.91  tff(c_79624, plain, (![B_6]: (r1_tarski(k4_xboole_0('#skF_1', k1_xboole_0), B_6) | k4_xboole_0('#skF_1', B_6)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_53, c_18, c_79612])).
% 36.78/26.91  tff(c_79511, plain, (k4_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), k4_xboole_0('#skF_1', k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_79225, c_3516])).
% 36.78/26.91  tff(c_79555, plain, (k4_xboole_0('#skF_1', k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', k1_xboole_0)))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_79511, c_18])).
% 36.78/26.91  tff(c_79588, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_53, c_79555])).
% 36.78/26.91  tff(c_79853, plain, (![A_506, B_507]: (k2_xboole_0(k3_xboole_0(A_506, B_507), k4_xboole_0(A_506, B_507))=A_506 | ~r1_tarski(k4_xboole_0(A_506, B_507), A_506))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_266])).
% 36.78/26.91  tff(c_79923, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', k1_xboole_0))='#skF_1' | ~r1_tarski(k4_xboole_0('#skF_1', k1_xboole_0), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_79588, c_79853])).
% 36.78/26.91  tff(c_80052, plain, (k4_xboole_0('#skF_1', k1_xboole_0)='#skF_1' | ~r1_tarski(k4_xboole_0('#skF_1', k1_xboole_0), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_79923])).
% 36.78/26.91  tff(c_80147, plain, (~r1_tarski(k4_xboole_0('#skF_1', k1_xboole_0), '#skF_1')), inference(splitLeft, [status(thm)], [c_80052])).
% 36.78/26.91  tff(c_80154, plain, (k4_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_79624, c_80147])).
% 36.78/26.91  tff(c_2226, plain, (![A_22, C_111]: (k4_xboole_0(k1_xboole_0, k2_xboole_0(A_22, C_111))=k4_xboole_0(A_22, k2_xboole_0(A_22, C_111)))), inference(superposition, [status(thm), theory('equality')], [c_53, c_2117])).
% 36.78/26.91  tff(c_3494, plain, (![C_54]: (k4_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), k2_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), C_54))=k4_xboole_0(k3_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), k1_xboole_0), C_54))), inference(superposition, [status(thm), theory('equality')], [c_3489, c_394])).
% 36.78/26.91  tff(c_3522, plain, (![C_54]: (k4_xboole_0(k3_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), k1_xboole_0), C_54)=k4_xboole_0(k1_xboole_0, k2_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), C_54)))), inference(demodulation, [status(thm), theory('equality')], [c_2226, c_3494])).
% 36.78/26.91  tff(c_80718, plain, (![C_514]: (k4_xboole_0(k1_xboole_0, k2_xboole_0(k4_xboole_0('#skF_1', k1_xboole_0), C_514))=k4_xboole_0(k1_xboole_0, C_514))), inference(demodulation, [status(thm), theory('equality')], [c_79225, c_3522])).
% 36.78/26.91  tff(c_2655, plain, (![B_2, A_1]: (k4_xboole_0(k1_xboole_0, k2_xboole_0(B_2, A_1))=k4_xboole_0(A_1, k2_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2512])).
% 36.78/26.91  tff(c_84571, plain, (![C_558]: (k4_xboole_0(C_558, k2_xboole_0(C_558, k4_xboole_0('#skF_1', k1_xboole_0)))=k4_xboole_0(k1_xboole_0, C_558))), inference(superposition, [status(thm), theory('equality')], [c_80718, c_2655])).
% 36.78/26.91  tff(c_84756, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, '#skF_1') | ~r1_tarski(k1_xboole_0, '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_20, c_84571])).
% 36.78/26.91  tff(c_84806, plain, (k4_xboole_0('#skF_1', '#skF_1')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_824, c_84756])).
% 36.78/26.91  tff(c_84807, plain, (~r1_tarski(k1_xboole_0, '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_80154, c_84806])).
% 36.78/26.91  tff(c_176, plain, (![A_34, B_6, B_36]: (r1_tarski(A_34, B_6) | k4_xboole_0(k2_xboole_0(A_34, B_36), B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_159])).
% 36.78/26.91  tff(c_84822, plain, (![A_559, B_560]: (r1_tarski(A_559, k4_xboole_0(A_559, B_560)) | k3_xboole_0(k2_xboole_0(A_559, B_560), B_560)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_79258, c_176])).
% 36.78/26.91  tff(c_84842, plain, (![A_10]: (r1_tarski(A_10, k4_xboole_0(A_10, k1_xboole_0)) | k3_xboole_0(A_10, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_84822])).
% 36.78/26.91  tff(c_991, plain, (![A_83, A_84, B_85]: (r1_tarski(A_83, A_83) | k4_xboole_0(A_84, k2_xboole_0(A_83, B_85))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_752])).
% 36.78/26.91  tff(c_102249, plain, (![A_659, A_660, B_661]: (r1_tarski(A_659, A_659) | k4_xboole_0(A_660, B_661)!=k1_xboole_0 | ~r1_tarski(A_659, B_661))), inference(superposition, [status(thm), theory('equality')], [c_20, c_991])).
% 36.78/26.91  tff(c_102429, plain, (![A_662]: (r1_tarski(A_662, A_662) | ~r1_tarski(A_662, k4_xboole_0('#skF_1', k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_79511, c_102249])).
% 36.78/26.91  tff(c_102438, plain, (r1_tarski('#skF_1', '#skF_1') | k3_xboole_0('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_84842, c_102429])).
% 36.78/26.91  tff(c_102471, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_79588, c_102438])).
% 36.78/26.91  tff(c_166, plain, (![C_35, A_22]: (r1_tarski(k1_xboole_0, C_35) | ~r1_tarski(A_22, C_35))), inference(superposition, [status(thm), theory('equality')], [c_53, c_159])).
% 36.78/26.91  tff(c_102503, plain, (r1_tarski(k1_xboole_0, '#skF_1')), inference(resolution, [status(thm)], [c_102471, c_166])).
% 36.78/26.91  tff(c_102514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84807, c_102503])).
% 36.78/26.91  tff(c_102515, plain, (k4_xboole_0('#skF_1', k1_xboole_0)='#skF_1'), inference(splitRight, [status(thm)], [c_80052])).
% 36.78/26.91  tff(c_103429, plain, (![C_670]: (k4_xboole_0('#skF_1', k2_xboole_0(C_670, '#skF_1'))=k4_xboole_0(k1_xboole_0, C_670))), inference(demodulation, [status(thm), theory('equality')], [c_2658, c_102515, c_79588, c_102515, c_3522])).
% 36.78/26.91  tff(c_103507, plain, (![B_2]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', B_2))=k4_xboole_0(k1_xboole_0, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_103429])).
% 36.78/26.91  tff(c_24, plain, (k4_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), '#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 36.78/26.91  tff(c_27, plain, (k4_xboole_0('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_24])).
% 36.78/26.91  tff(c_80040, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_2'))='#skF_1' | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_139, c_79853])).
% 36.78/26.91  tff(c_80090, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_80040])).
% 36.78/26.91  tff(c_80091, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_27, c_80090])).
% 36.78/26.91  tff(c_80094, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_80091])).
% 36.78/26.91  tff(c_80096, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18, c_80094])).
% 36.78/26.91  tff(c_103969, plain, (k4_xboole_0(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_103507, c_80096])).
% 36.78/26.91  tff(c_103970, plain, (k4_xboole_0('#skF_2', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_189, c_103969])).
% 36.78/26.91  tff(c_102523, plain, (k4_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_102515, c_102515, c_79511])).
% 36.78/26.91  tff(c_111657, plain, (![B_739]: (k4_xboole_0(k3_xboole_0('#skF_1', B_739), '#skF_1')=k4_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', B_739)))), inference(superposition, [status(thm), theory('equality')], [c_394, c_103429])).
% 36.78/26.91  tff(c_111734, plain, (k4_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0(k1_xboole_0, '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_139, c_111657])).
% 36.78/26.91  tff(c_111752, plain, (k4_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_102523, c_189, c_111734])).
% 36.78/26.91  tff(c_275, plain, (![B_46]: (k4_xboole_0(B_46, k1_xboole_0)=B_46 | ~r1_tarski(k1_xboole_0, B_46))), inference(superposition, [status(thm), theory('equality')], [c_238, c_53])).
% 36.78/26.91  tff(c_280, plain, (![B_6]: (k4_xboole_0(B_6, k1_xboole_0)=B_6 | k4_xboole_0(k1_xboole_0, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_275])).
% 36.78/26.91  tff(c_111860, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_111752, c_280])).
% 36.78/26.91  tff(c_79406, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=k3_xboole_0(k2_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_79258])).
% 36.78/26.91  tff(c_111956, plain, (k4_xboole_0(k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_2')), k4_xboole_0('#skF_1', '#skF_2'))=k3_xboole_0(k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_111860, c_79406])).
% 36.78/26.91  tff(c_112026, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_111752, c_53, c_2, c_16, c_111956])).
% 36.78/26.91  tff(c_398, plain, (![A_52, B_53, B_19]: (k4_xboole_0(A_52, k2_xboole_0(B_53, k4_xboole_0(k4_xboole_0(A_52, B_53), B_19)))=k3_xboole_0(k4_xboole_0(A_52, B_53), B_19))), inference(superposition, [status(thm), theory('equality')], [c_22, c_347])).
% 36.78/26.91  tff(c_103521, plain, (![A_671, B_672, B_673]: (k4_xboole_0(A_671, k2_xboole_0(B_672, k4_xboole_0(A_671, k2_xboole_0(B_672, B_673))))=k3_xboole_0(k4_xboole_0(A_671, B_672), B_673))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_398])).
% 36.78/26.91  tff(c_774, plain, (![A_1, A_75, B_2]: (r1_tarski(A_1, A_1) | k4_xboole_0(A_75, k2_xboole_0(A_1, B_2))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_752])).
% 36.78/26.91  tff(c_103604, plain, (![B_672, A_671, B_673]: (r1_tarski(B_672, B_672) | k3_xboole_0(k4_xboole_0(A_671, B_672), B_673)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_103521, c_774])).
% 36.78/26.91  tff(c_112074, plain, (r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_112026, c_103604])).
% 36.78/26.91  tff(c_112091, plain, (k4_xboole_0('#skF_2', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_112074, c_10])).
% 36.78/26.91  tff(c_112099, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103970, c_112091])).
% 36.78/26.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.78/26.91  
% 36.78/26.91  Inference rules
% 36.78/26.91  ----------------------
% 36.78/26.91  #Ref     : 0
% 36.78/26.91  #Sup     : 28358
% 36.78/26.91  #Fact    : 0
% 36.78/26.91  #Define  : 0
% 36.78/26.91  #Split   : 21
% 36.78/26.91  #Chain   : 0
% 36.78/26.91  #Close   : 0
% 36.78/26.91  
% 36.78/26.91  Ordering : KBO
% 36.78/26.91  
% 36.78/26.91  Simplification rules
% 36.78/26.91  ----------------------
% 36.78/26.91  #Subsume      : 3543
% 36.78/26.91  #Demod        : 37680
% 36.78/26.91  #Tautology    : 6965
% 36.78/26.91  #SimpNegUnit  : 132
% 36.78/26.91  #BackRed      : 35
% 36.78/26.91  
% 36.78/26.91  #Partial instantiations: 0
% 36.78/26.91  #Strategies tried      : 1
% 36.78/26.91  
% 36.78/26.91  Timing (in seconds)
% 36.78/26.91  ----------------------
% 36.78/26.92  Preprocessing        : 0.34
% 36.78/26.92  Parsing              : 0.19
% 36.78/26.92  CNF conversion       : 0.02
% 36.78/26.92  Main loop            : 25.76
% 36.78/26.92  Inferencing          : 2.56
% 36.78/26.92  Reduction            : 17.36
% 36.78/26.92  Demodulation         : 16.18
% 36.78/26.92  BG Simplification    : 0.46
% 36.78/26.92  Subsumption          : 4.60
% 36.78/26.92  Abstraction          : 0.71
% 36.78/26.92  MUC search           : 0.00
% 36.78/26.92  Cooper               : 0.00
% 36.78/26.92  Total                : 26.17
% 36.78/26.92  Index Insertion      : 0.00
% 36.78/26.92  Index Deletion       : 0.00
% 36.78/26.92  Index Matching       : 0.00
% 36.78/26.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
