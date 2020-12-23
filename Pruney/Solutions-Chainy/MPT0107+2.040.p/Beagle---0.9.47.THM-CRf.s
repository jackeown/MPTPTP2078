%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:58 EST 2020

% Result     : Theorem 21.46s
% Output     : CNFRefutation 21.46s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 194 expanded)
%              Number of leaves         :   29 (  74 expanded)
%              Depth                    :   17
%              Number of atoms          :   91 ( 209 expanded)
%              Number of equality atoms :   74 ( 153 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_55,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_26,plain,(
    ! [A_23,B_24] : r1_xboole_0(k4_xboole_0(A_23,B_24),B_24) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_79,plain,(
    ! [B_39,A_40] :
      ( r1_xboole_0(B_39,A_40)
      | ~ r1_xboole_0(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,(
    ! [B_24,A_23] : r1_xboole_0(B_24,k4_xboole_0(A_23,B_24)) ),
    inference(resolution,[status(thm)],[c_26,c_79])).

tff(c_213,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = A_51
      | ~ r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_226,plain,(
    ! [B_24,A_23] : k4_xboole_0(B_24,k4_xboole_0(A_23,B_24)) = B_24 ),
    inference(resolution,[status(thm)],[c_85,c_213])).

tff(c_22,plain,(
    ! [A_19,B_20,C_21] : k4_xboole_0(k3_xboole_0(A_19,B_20),C_21) = k3_xboole_0(A_19,k4_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_24,plain,(
    ! [A_22] : k5_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_74,plain,(
    ! [A_36,B_37] : r1_xboole_0(k4_xboole_0(A_36,B_37),B_37) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_77,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_74])).

tff(c_84,plain,(
    ! [A_9] : r1_xboole_0(k1_xboole_0,A_9) ),
    inference(resolution,[status(thm)],[c_77,c_79])).

tff(c_227,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_84,c_213])).

tff(c_495,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k4_xboole_0(B_73,A_72)) = k2_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_517,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = k2_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_495])).

tff(c_632,plain,(
    ! [A_78] : k2_xboole_0(A_78,k1_xboole_0) = A_78 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_517])).

tff(c_16,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_654,plain,(
    ! [A_79] : k4_xboole_0(A_79,A_79) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_16])).

tff(c_36,plain,(
    ! [A_31,B_32] : k5_xboole_0(A_31,k4_xboole_0(B_32,A_31)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_663,plain,(
    ! [A_79] : k5_xboole_0(A_79,k1_xboole_0) = k2_xboole_0(A_79,A_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_654,c_36])).

tff(c_700,plain,(
    ! [A_79] : k2_xboole_0(A_79,A_79) = A_79 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_663])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k4_xboole_0(A_10,B_11),C_12) = k4_xboole_0(A_10,k2_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_115,plain,(
    ! [B_46,A_47] : k5_xboole_0(B_46,A_47) = k5_xboole_0(A_47,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_131,plain,(
    ! [A_47] : k5_xboole_0(k1_xboole_0,A_47) = A_47 ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_24])).

tff(c_744,plain,(
    ! [A_81,B_82,C_83] : k5_xboole_0(k5_xboole_0(A_81,B_82),C_83) = k5_xboole_0(A_81,k5_xboole_0(B_82,C_83)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2630,plain,(
    ! [C_146,A_147,B_148] : k5_xboole_0(C_146,k5_xboole_0(A_147,B_148)) = k5_xboole_0(A_147,k5_xboole_0(B_148,C_146)) ),
    inference(superposition,[status(thm),theory(equality)],[c_744,c_2])).

tff(c_2994,plain,(
    ! [A_151,C_152] : k5_xboole_0(k1_xboole_0,k5_xboole_0(A_151,C_152)) = k5_xboole_0(C_152,A_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_2630])).

tff(c_3087,plain,(
    ! [B_32,A_31] : k5_xboole_0(k4_xboole_0(B_32,A_31),A_31) = k5_xboole_0(k1_xboole_0,k2_xboole_0(A_31,B_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2994])).

tff(c_3502,plain,(
    ! [B_160,A_161] : k5_xboole_0(k4_xboole_0(B_160,A_161),A_161) = k2_xboole_0(A_161,B_160) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_3087])).

tff(c_3585,plain,(
    ! [B_24,A_23] : k5_xboole_0(B_24,k4_xboole_0(A_23,B_24)) = k2_xboole_0(k4_xboole_0(A_23,B_24),B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_3502])).

tff(c_5237,plain,(
    ! [A_186,B_187] : k2_xboole_0(k4_xboole_0(A_186,B_187),B_187) = k2_xboole_0(B_187,A_186) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3585])).

tff(c_5298,plain,(
    ! [A_186,B_187] : k4_xboole_0(k4_xboole_0(A_186,B_187),k2_xboole_0(B_187,A_186)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5237,c_16])).

tff(c_1008,plain,(
    ! [A_91,B_92,C_93] : k4_xboole_0(k4_xboole_0(A_91,B_92),C_93) = k4_xboole_0(A_91,k2_xboole_0(B_92,C_93)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8497,plain,(
    ! [C_249,A_250,B_251] : k5_xboole_0(C_249,k4_xboole_0(A_250,k2_xboole_0(B_251,C_249))) = k2_xboole_0(C_249,k4_xboole_0(A_250,B_251)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1008,c_36])).

tff(c_8583,plain,(
    ! [A_186,B_187] : k2_xboole_0(A_186,k4_xboole_0(k4_xboole_0(A_186,B_187),B_187)) = k5_xboole_0(A_186,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5298,c_8497])).

tff(c_8658,plain,(
    ! [A_252,B_253] : k2_xboole_0(A_252,k4_xboole_0(A_252,B_253)) = A_252 ),
    inference(demodulation,[status(thm),theory(equality)],[c_700,c_14,c_24,c_8583])).

tff(c_642,plain,(
    ! [A_78] : k4_xboole_0(A_78,A_78) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_16])).

tff(c_3135,plain,(
    ! [C_153,A_154,B_155] : k4_xboole_0(C_153,k4_xboole_0(A_154,k2_xboole_0(B_155,C_153))) = C_153 ),
    inference(superposition,[status(thm),theory(equality)],[c_1008,c_226])).

tff(c_20,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3282,plain,(
    ! [A_156,B_157] : k3_xboole_0(A_156,k2_xboole_0(B_157,A_156)) = A_156 ),
    inference(superposition,[status(thm),theory(equality)],[c_3135,c_20])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3308,plain,(
    ! [A_156,B_157] : k4_xboole_0(A_156,k2_xboole_0(B_157,A_156)) = k4_xboole_0(A_156,A_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_3282,c_18])).

tff(c_3344,plain,(
    ! [A_156,B_157] : k4_xboole_0(A_156,k2_xboole_0(B_157,A_156)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_3308])).

tff(c_9065,plain,(
    ! [A_256,B_257] : k4_xboole_0(k4_xboole_0(A_256,B_257),A_256) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8658,c_3344])).

tff(c_318,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(A_60,B_61)
      | k4_xboole_0(A_60,B_61) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_326,plain,(
    ! [A_60,B_61] :
      ( k2_xboole_0(A_60,B_61) = B_61
      | k4_xboole_0(A_60,B_61) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_318,c_10])).

tff(c_9305,plain,(
    ! [A_256,B_257] : k2_xboole_0(k4_xboole_0(A_256,B_257),A_256) = A_256 ),
    inference(superposition,[status(thm),theory(equality)],[c_9065,c_326])).

tff(c_508,plain,(
    ! [A_17,B_18] : k5_xboole_0(k4_xboole_0(A_17,B_18),k3_xboole_0(A_17,B_18)) = k2_xboole_0(k4_xboole_0(A_17,B_18),A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_495])).

tff(c_10583,plain,(
    ! [A_17,B_18] : k5_xboole_0(k4_xboole_0(A_17,B_18),k3_xboole_0(A_17,B_18)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9305,c_508])).

tff(c_1981,plain,(
    ! [A_130,B_131] : k4_xboole_0(k4_xboole_0(A_130,B_131),B_131) = k4_xboole_0(A_130,B_131) ),
    inference(resolution,[status(thm)],[c_26,c_213])).

tff(c_2062,plain,(
    ! [A_17,B_18] : k4_xboole_0(k3_xboole_0(A_17,B_18),k4_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1981])).

tff(c_67691,plain,(
    ! [A_658,B_659] : k4_xboole_0(k3_xboole_0(A_658,B_659),k4_xboole_0(A_658,B_659)) = k3_xboole_0(A_658,B_659) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2062])).

tff(c_67960,plain,(
    ! [A_658,B_659] : k5_xboole_0(k4_xboole_0(A_658,B_659),k3_xboole_0(A_658,B_659)) = k2_xboole_0(k4_xboole_0(A_658,B_659),k3_xboole_0(A_658,B_659)) ),
    inference(superposition,[status(thm),theory(equality)],[c_67691,c_36])).

tff(c_68497,plain,(
    ! [A_660,B_661] : k2_xboole_0(k4_xboole_0(A_660,B_661),k3_xboole_0(A_660,B_661)) = A_660 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10583,c_67960])).

tff(c_34,plain,(
    ! [A_30] : k5_xboole_0(A_30,A_30) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_808,plain,(
    ! [A_30,C_83] : k5_xboole_0(A_30,k5_xboole_0(A_30,C_83)) = k5_xboole_0(k1_xboole_0,C_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_744])).

tff(c_943,plain,(
    ! [A_89,C_90] : k5_xboole_0(A_89,k5_xboole_0(A_89,C_90)) = C_90 ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_808])).

tff(c_2407,plain,(
    ! [A_140,B_141] : k5_xboole_0(A_140,k2_xboole_0(A_140,B_141)) = k4_xboole_0(B_141,A_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_943])).

tff(c_986,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_943])).

tff(c_2419,plain,(
    ! [A_140,B_141] : k5_xboole_0(k2_xboole_0(A_140,B_141),k4_xboole_0(B_141,A_140)) = A_140 ),
    inference(superposition,[status(thm),theory(equality)],[c_2407,c_986])).

tff(c_68682,plain,(
    ! [A_660,B_661] : k5_xboole_0(A_660,k4_xboole_0(k3_xboole_0(A_660,B_661),k4_xboole_0(A_660,B_661))) = k4_xboole_0(A_660,B_661) ),
    inference(superposition,[status(thm),theory(equality)],[c_68497,c_2419])).

tff(c_69085,plain,(
    ! [A_660,B_661] : k5_xboole_0(A_660,k3_xboole_0(A_660,B_661)) = k4_xboole_0(A_660,B_661) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_22,c_68682])).

tff(c_38,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_90152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69085,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.46/12.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.46/12.57  
% 21.46/12.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.46/12.58  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 21.46/12.58  
% 21.46/12.58  %Foreground sorts:
% 21.46/12.58  
% 21.46/12.58  
% 21.46/12.58  %Background operators:
% 21.46/12.58  
% 21.46/12.58  
% 21.46/12.58  %Foreground operators:
% 21.46/12.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.46/12.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 21.46/12.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 21.46/12.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 21.46/12.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.46/12.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 21.46/12.58  tff('#skF_2', type, '#skF_2': $i).
% 21.46/12.58  tff('#skF_1', type, '#skF_1': $i).
% 21.46/12.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.46/12.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.46/12.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 21.46/12.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 21.46/12.58  
% 21.46/12.59  tff(f_55, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 21.46/12.59  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 21.46/12.59  tff(f_59, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 21.46/12.59  tff(f_51, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 21.46/12.59  tff(f_53, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 21.46/12.59  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 21.46/12.59  tff(f_65, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 21.46/12.59  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 21.46/12.59  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 21.46/12.59  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 21.46/12.59  tff(f_61, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 21.46/12.59  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 21.46/12.59  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 21.46/12.59  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 21.46/12.59  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 21.46/12.59  tff(f_63, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 21.46/12.59  tff(f_68, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 21.46/12.59  tff(c_26, plain, (![A_23, B_24]: (r1_xboole_0(k4_xboole_0(A_23, B_24), B_24))), inference(cnfTransformation, [status(thm)], [f_55])).
% 21.46/12.59  tff(c_79, plain, (![B_39, A_40]: (r1_xboole_0(B_39, A_40) | ~r1_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 21.46/12.59  tff(c_85, plain, (![B_24, A_23]: (r1_xboole_0(B_24, k4_xboole_0(A_23, B_24)))), inference(resolution, [status(thm)], [c_26, c_79])).
% 21.46/12.59  tff(c_213, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=A_51 | ~r1_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_59])).
% 21.46/12.59  tff(c_226, plain, (![B_24, A_23]: (k4_xboole_0(B_24, k4_xboole_0(A_23, B_24))=B_24)), inference(resolution, [status(thm)], [c_85, c_213])).
% 21.46/12.59  tff(c_22, plain, (![A_19, B_20, C_21]: (k4_xboole_0(k3_xboole_0(A_19, B_20), C_21)=k3_xboole_0(A_19, k4_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 21.46/12.59  tff(c_24, plain, (![A_22]: (k5_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_53])).
% 21.46/12.59  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 21.46/12.59  tff(c_74, plain, (![A_36, B_37]: (r1_xboole_0(k4_xboole_0(A_36, B_37), B_37))), inference(cnfTransformation, [status(thm)], [f_55])).
% 21.46/12.59  tff(c_77, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_74])).
% 21.46/12.59  tff(c_84, plain, (![A_9]: (r1_xboole_0(k1_xboole_0, A_9))), inference(resolution, [status(thm)], [c_77, c_79])).
% 21.46/12.59  tff(c_227, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_84, c_213])).
% 21.46/12.59  tff(c_495, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k4_xboole_0(B_73, A_72))=k2_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_65])).
% 21.46/12.59  tff(c_517, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=k2_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_227, c_495])).
% 21.46/12.59  tff(c_632, plain, (![A_78]: (k2_xboole_0(A_78, k1_xboole_0)=A_78)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_517])).
% 21.46/12.59  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 21.46/12.59  tff(c_654, plain, (![A_79]: (k4_xboole_0(A_79, A_79)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_632, c_16])).
% 21.46/12.59  tff(c_36, plain, (![A_31, B_32]: (k5_xboole_0(A_31, k4_xboole_0(B_32, A_31))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_65])).
% 21.46/12.60  tff(c_663, plain, (![A_79]: (k5_xboole_0(A_79, k1_xboole_0)=k2_xboole_0(A_79, A_79))), inference(superposition, [status(thm), theory('equality')], [c_654, c_36])).
% 21.46/12.60  tff(c_700, plain, (![A_79]: (k2_xboole_0(A_79, A_79)=A_79)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_663])).
% 21.46/12.60  tff(c_14, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k4_xboole_0(A_10, B_11), C_12)=k4_xboole_0(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 21.46/12.60  tff(c_115, plain, (![B_46, A_47]: (k5_xboole_0(B_46, A_47)=k5_xboole_0(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_27])).
% 21.46/12.60  tff(c_131, plain, (![A_47]: (k5_xboole_0(k1_xboole_0, A_47)=A_47)), inference(superposition, [status(thm), theory('equality')], [c_115, c_24])).
% 21.46/12.60  tff(c_744, plain, (![A_81, B_82, C_83]: (k5_xboole_0(k5_xboole_0(A_81, B_82), C_83)=k5_xboole_0(A_81, k5_xboole_0(B_82, C_83)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 21.46/12.60  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 21.46/12.60  tff(c_2630, plain, (![C_146, A_147, B_148]: (k5_xboole_0(C_146, k5_xboole_0(A_147, B_148))=k5_xboole_0(A_147, k5_xboole_0(B_148, C_146)))), inference(superposition, [status(thm), theory('equality')], [c_744, c_2])).
% 21.46/12.60  tff(c_2994, plain, (![A_151, C_152]: (k5_xboole_0(k1_xboole_0, k5_xboole_0(A_151, C_152))=k5_xboole_0(C_152, A_151))), inference(superposition, [status(thm), theory('equality')], [c_131, c_2630])).
% 21.46/12.60  tff(c_3087, plain, (![B_32, A_31]: (k5_xboole_0(k4_xboole_0(B_32, A_31), A_31)=k5_xboole_0(k1_xboole_0, k2_xboole_0(A_31, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2994])).
% 21.46/12.60  tff(c_3502, plain, (![B_160, A_161]: (k5_xboole_0(k4_xboole_0(B_160, A_161), A_161)=k2_xboole_0(A_161, B_160))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_3087])).
% 21.46/12.60  tff(c_3585, plain, (![B_24, A_23]: (k5_xboole_0(B_24, k4_xboole_0(A_23, B_24))=k2_xboole_0(k4_xboole_0(A_23, B_24), B_24))), inference(superposition, [status(thm), theory('equality')], [c_226, c_3502])).
% 21.46/12.60  tff(c_5237, plain, (![A_186, B_187]: (k2_xboole_0(k4_xboole_0(A_186, B_187), B_187)=k2_xboole_0(B_187, A_186))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3585])).
% 21.46/12.60  tff(c_5298, plain, (![A_186, B_187]: (k4_xboole_0(k4_xboole_0(A_186, B_187), k2_xboole_0(B_187, A_186))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5237, c_16])).
% 21.46/12.60  tff(c_1008, plain, (![A_91, B_92, C_93]: (k4_xboole_0(k4_xboole_0(A_91, B_92), C_93)=k4_xboole_0(A_91, k2_xboole_0(B_92, C_93)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 21.46/12.60  tff(c_8497, plain, (![C_249, A_250, B_251]: (k5_xboole_0(C_249, k4_xboole_0(A_250, k2_xboole_0(B_251, C_249)))=k2_xboole_0(C_249, k4_xboole_0(A_250, B_251)))), inference(superposition, [status(thm), theory('equality')], [c_1008, c_36])).
% 21.46/12.60  tff(c_8583, plain, (![A_186, B_187]: (k2_xboole_0(A_186, k4_xboole_0(k4_xboole_0(A_186, B_187), B_187))=k5_xboole_0(A_186, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5298, c_8497])).
% 21.46/12.60  tff(c_8658, plain, (![A_252, B_253]: (k2_xboole_0(A_252, k4_xboole_0(A_252, B_253))=A_252)), inference(demodulation, [status(thm), theory('equality')], [c_700, c_14, c_24, c_8583])).
% 21.46/12.60  tff(c_642, plain, (![A_78]: (k4_xboole_0(A_78, A_78)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_632, c_16])).
% 21.46/12.60  tff(c_3135, plain, (![C_153, A_154, B_155]: (k4_xboole_0(C_153, k4_xboole_0(A_154, k2_xboole_0(B_155, C_153)))=C_153)), inference(superposition, [status(thm), theory('equality')], [c_1008, c_226])).
% 21.46/12.60  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 21.46/12.60  tff(c_3282, plain, (![A_156, B_157]: (k3_xboole_0(A_156, k2_xboole_0(B_157, A_156))=A_156)), inference(superposition, [status(thm), theory('equality')], [c_3135, c_20])).
% 21.46/12.60  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 21.46/12.60  tff(c_3308, plain, (![A_156, B_157]: (k4_xboole_0(A_156, k2_xboole_0(B_157, A_156))=k4_xboole_0(A_156, A_156))), inference(superposition, [status(thm), theory('equality')], [c_3282, c_18])).
% 21.46/12.60  tff(c_3344, plain, (![A_156, B_157]: (k4_xboole_0(A_156, k2_xboole_0(B_157, A_156))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_642, c_3308])).
% 21.46/12.60  tff(c_9065, plain, (![A_256, B_257]: (k4_xboole_0(k4_xboole_0(A_256, B_257), A_256)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8658, c_3344])).
% 21.46/12.60  tff(c_318, plain, (![A_60, B_61]: (r1_tarski(A_60, B_61) | k4_xboole_0(A_60, B_61)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 21.46/12.60  tff(c_10, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 21.46/12.60  tff(c_326, plain, (![A_60, B_61]: (k2_xboole_0(A_60, B_61)=B_61 | k4_xboole_0(A_60, B_61)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_318, c_10])).
% 21.46/12.60  tff(c_9305, plain, (![A_256, B_257]: (k2_xboole_0(k4_xboole_0(A_256, B_257), A_256)=A_256)), inference(superposition, [status(thm), theory('equality')], [c_9065, c_326])).
% 21.46/12.60  tff(c_508, plain, (![A_17, B_18]: (k5_xboole_0(k4_xboole_0(A_17, B_18), k3_xboole_0(A_17, B_18))=k2_xboole_0(k4_xboole_0(A_17, B_18), A_17))), inference(superposition, [status(thm), theory('equality')], [c_20, c_495])).
% 21.46/12.60  tff(c_10583, plain, (![A_17, B_18]: (k5_xboole_0(k4_xboole_0(A_17, B_18), k3_xboole_0(A_17, B_18))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_9305, c_508])).
% 21.46/12.60  tff(c_1981, plain, (![A_130, B_131]: (k4_xboole_0(k4_xboole_0(A_130, B_131), B_131)=k4_xboole_0(A_130, B_131))), inference(resolution, [status(thm)], [c_26, c_213])).
% 21.46/12.60  tff(c_2062, plain, (![A_17, B_18]: (k4_xboole_0(k3_xboole_0(A_17, B_18), k4_xboole_0(A_17, B_18))=k4_xboole_0(A_17, k4_xboole_0(A_17, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1981])).
% 21.46/12.60  tff(c_67691, plain, (![A_658, B_659]: (k4_xboole_0(k3_xboole_0(A_658, B_659), k4_xboole_0(A_658, B_659))=k3_xboole_0(A_658, B_659))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2062])).
% 21.46/12.60  tff(c_67960, plain, (![A_658, B_659]: (k5_xboole_0(k4_xboole_0(A_658, B_659), k3_xboole_0(A_658, B_659))=k2_xboole_0(k4_xboole_0(A_658, B_659), k3_xboole_0(A_658, B_659)))), inference(superposition, [status(thm), theory('equality')], [c_67691, c_36])).
% 21.46/12.60  tff(c_68497, plain, (![A_660, B_661]: (k2_xboole_0(k4_xboole_0(A_660, B_661), k3_xboole_0(A_660, B_661))=A_660)), inference(demodulation, [status(thm), theory('equality')], [c_10583, c_67960])).
% 21.46/12.60  tff(c_34, plain, (![A_30]: (k5_xboole_0(A_30, A_30)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 21.46/12.60  tff(c_808, plain, (![A_30, C_83]: (k5_xboole_0(A_30, k5_xboole_0(A_30, C_83))=k5_xboole_0(k1_xboole_0, C_83))), inference(superposition, [status(thm), theory('equality')], [c_34, c_744])).
% 21.46/12.60  tff(c_943, plain, (![A_89, C_90]: (k5_xboole_0(A_89, k5_xboole_0(A_89, C_90))=C_90)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_808])).
% 21.46/12.60  tff(c_2407, plain, (![A_140, B_141]: (k5_xboole_0(A_140, k2_xboole_0(A_140, B_141))=k4_xboole_0(B_141, A_140))), inference(superposition, [status(thm), theory('equality')], [c_36, c_943])).
% 21.46/12.60  tff(c_986, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_943])).
% 21.46/12.60  tff(c_2419, plain, (![A_140, B_141]: (k5_xboole_0(k2_xboole_0(A_140, B_141), k4_xboole_0(B_141, A_140))=A_140)), inference(superposition, [status(thm), theory('equality')], [c_2407, c_986])).
% 21.46/12.60  tff(c_68682, plain, (![A_660, B_661]: (k5_xboole_0(A_660, k4_xboole_0(k3_xboole_0(A_660, B_661), k4_xboole_0(A_660, B_661)))=k4_xboole_0(A_660, B_661))), inference(superposition, [status(thm), theory('equality')], [c_68497, c_2419])).
% 21.46/12.60  tff(c_69085, plain, (![A_660, B_661]: (k5_xboole_0(A_660, k3_xboole_0(A_660, B_661))=k4_xboole_0(A_660, B_661))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_22, c_68682])).
% 21.46/12.60  tff(c_38, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 21.46/12.60  tff(c_90152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69085, c_38])).
% 21.46/12.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.46/12.60  
% 21.46/12.60  Inference rules
% 21.46/12.60  ----------------------
% 21.46/12.60  #Ref     : 1
% 21.46/12.60  #Sup     : 23616
% 21.46/12.60  #Fact    : 0
% 21.46/12.60  #Define  : 0
% 21.46/12.60  #Split   : 5
% 21.46/12.60  #Chain   : 0
% 21.46/12.60  #Close   : 0
% 21.46/12.60  
% 21.46/12.60  Ordering : KBO
% 21.46/12.60  
% 21.46/12.60  Simplification rules
% 21.46/12.60  ----------------------
% 21.46/12.60  #Subsume      : 3894
% 21.46/12.60  #Demod        : 19553
% 21.46/12.60  #Tautology    : 12493
% 21.46/12.60  #SimpNegUnit  : 0
% 21.46/12.60  #BackRed      : 5
% 21.46/12.60  
% 21.46/12.60  #Partial instantiations: 0
% 21.46/12.60  #Strategies tried      : 1
% 21.46/12.60  
% 21.46/12.60  Timing (in seconds)
% 21.46/12.60  ----------------------
% 21.46/12.60  Preprocessing        : 0.29
% 21.46/12.60  Parsing              : 0.16
% 21.46/12.60  CNF conversion       : 0.02
% 21.46/12.60  Main loop            : 11.50
% 21.46/12.60  Inferencing          : 1.49
% 21.46/12.60  Reduction            : 7.22
% 21.46/12.60  Demodulation         : 6.56
% 21.46/12.60  BG Simplification    : 0.20
% 21.46/12.60  Subsumption          : 2.15
% 21.46/12.60  Abstraction          : 0.35
% 21.46/12.60  MUC search           : 0.00
% 21.46/12.60  Cooper               : 0.00
% 21.46/12.60  Total                : 11.83
% 21.46/12.60  Index Insertion      : 0.00
% 21.46/12.60  Index Deletion       : 0.00
% 21.46/12.60  Index Matching       : 0.00
% 21.46/12.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
