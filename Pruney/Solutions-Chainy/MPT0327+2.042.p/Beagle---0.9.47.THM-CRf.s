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
% DateTime   : Thu Dec  3 09:54:36 EST 2020

% Result     : Theorem 6.54s
% Output     : CNFRefutation 6.54s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 937 expanded)
%              Number of leaves         :   30 ( 331 expanded)
%              Depth                    :   17
%              Number of atoms          :   93 (1204 expanded)
%              Number of equality atoms :   74 ( 845 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_46,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_240,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(k1_tarski(A_61),B_62)
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_250,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(k1_tarski(A_61),B_62) = k1_xboole_0
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_240,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_299,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k3_xboole_0(A_64,B_65)) = k4_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_317,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_299])).

tff(c_26,plain,(
    ! [A_18,B_19,C_20] : k5_xboole_0(k5_xboole_0(A_18,B_19),C_20) = k5_xboole_0(A_18,k5_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1143,plain,(
    ! [A_102,B_103] : k5_xboole_0(k5_xboole_0(A_102,B_103),k3_xboole_0(A_102,B_103)) = k2_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1189,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k5_xboole_0(B_19,k3_xboole_0(A_18,B_19))) = k2_xboole_0(A_18,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1143])).

tff(c_1626,plain,(
    ! [A_119,B_120] : k5_xboole_0(A_119,k4_xboole_0(B_120,A_119)) = k2_xboole_0(A_119,B_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_1189])).

tff(c_1669,plain,(
    ! [B_62,A_61] :
      ( k2_xboole_0(B_62,k1_tarski(A_61)) = k5_xboole_0(B_62,k1_xboole_0)
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_1626])).

tff(c_1688,plain,(
    ! [B_62,A_61] :
      ( k2_xboole_0(B_62,k1_tarski(A_61)) = B_62
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1669])).

tff(c_22,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k3_xboole_0(A_14,B_15),C_16) = k3_xboole_0(A_14,k4_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_186,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,B_57) = k1_xboole_0
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_198,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_186])).

tff(c_152,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_164,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_152])).

tff(c_311,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_299])).

tff(c_324,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_311])).

tff(c_948,plain,(
    ! [A_95,B_96,C_97] : k4_xboole_0(k3_xboole_0(A_95,B_96),C_97) = k3_xboole_0(A_95,k4_xboole_0(B_96,C_97)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1075,plain,(
    ! [B_100,C_101] : k3_xboole_0(B_100,k4_xboole_0(B_100,C_101)) = k4_xboole_0(B_100,C_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_948])).

tff(c_1091,plain,(
    ! [B_100,C_101] : k5_xboole_0(k4_xboole_0(B_100,C_101),k4_xboole_0(B_100,C_101)) = k4_xboole_0(k4_xboole_0(B_100,C_101),B_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_1075,c_317])).

tff(c_1300,plain,(
    ! [B_106,C_107] : k4_xboole_0(k4_xboole_0(B_106,C_107),B_106) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_1091])).

tff(c_1413,plain,(
    ! [A_114,B_115] : k4_xboole_0(k3_xboole_0(A_114,B_115),A_114) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1300])).

tff(c_1446,plain,(
    ! [C_16,B_15] : k3_xboole_0(C_16,k4_xboole_0(B_15,C_16)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1413])).

tff(c_1223,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_1189])).

tff(c_2660,plain,(
    ! [A_147,B_148] : k5_xboole_0(k5_xboole_0(A_147,B_148),k3_xboole_0(B_148,A_147)) = k2_xboole_0(A_147,B_148) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1143])).

tff(c_2706,plain,(
    ! [A_18,B_19] : k5_xboole_0(k2_xboole_0(A_18,B_19),k3_xboole_0(k4_xboole_0(B_19,A_18),A_18)) = k2_xboole_0(A_18,k4_xboole_0(B_19,A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1223,c_2660])).

tff(c_2766,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1446,c_2,c_2706])).

tff(c_589,plain,(
    ! [A_86,B_87,C_88] : k5_xboole_0(k5_xboole_0(A_86,B_87),C_88) = k5_xboole_0(A_86,k5_xboole_0(B_87,C_88)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_631,plain,(
    ! [A_86,B_87] : k5_xboole_0(A_86,k5_xboole_0(B_87,k5_xboole_0(A_86,B_87))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_589])).

tff(c_1678,plain,(
    ! [B_4] : k5_xboole_0(B_4,k1_xboole_0) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_1626])).

tff(c_1690,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1678])).

tff(c_1204,plain,(
    ! [B_4] : k5_xboole_0(k5_xboole_0(B_4,B_4),B_4) = k2_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_1143])).

tff(c_1226,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = k2_xboole_0(B_4,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_1204])).

tff(c_1694,plain,(
    ! [B_4] : k5_xboole_0(k1_xboole_0,B_4) = B_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1690,c_1226])).

tff(c_627,plain,(
    ! [B_4,C_88] : k5_xboole_0(B_4,k5_xboole_0(B_4,C_88)) = k5_xboole_0(k1_xboole_0,C_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_589])).

tff(c_2892,plain,(
    ! [B_151,C_152] : k5_xboole_0(B_151,k5_xboole_0(B_151,C_152)) = C_152 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1694,c_627])).

tff(c_2954,plain,(
    ! [B_87,A_86] : k5_xboole_0(B_87,k5_xboole_0(A_86,B_87)) = k5_xboole_0(A_86,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_631,c_2892])).

tff(c_2992,plain,(
    ! [B_87,A_86] : k5_xboole_0(B_87,k5_xboole_0(A_86,B_87)) = A_86 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2954])).

tff(c_1131,plain,(
    ! [B_100,C_101] : k4_xboole_0(k4_xboole_0(B_100,C_101),B_100) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_1091])).

tff(c_1659,plain,(
    ! [B_100,C_101] : k2_xboole_0(B_100,k4_xboole_0(B_100,C_101)) = k5_xboole_0(B_100,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1131,c_1626])).

tff(c_1687,plain,(
    ! [B_100,C_101] : k2_xboole_0(B_100,k4_xboole_0(B_100,C_101)) = B_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1659])).

tff(c_990,plain,(
    ! [B_4,C_97] : k3_xboole_0(B_4,k4_xboole_0(B_4,C_97)) = k4_xboole_0(B_4,C_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_948])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1094,plain,(
    ! [B_100,C_101] : k5_xboole_0(B_100,k4_xboole_0(B_100,C_101)) = k4_xboole_0(B_100,k4_xboole_0(B_100,C_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1075,c_14])).

tff(c_1132,plain,(
    ! [B_100,C_101] : k5_xboole_0(B_100,k4_xboole_0(B_100,C_101)) = k3_xboole_0(B_100,C_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1094])).

tff(c_2691,plain,(
    ! [B_100,C_101] : k5_xboole_0(k3_xboole_0(B_100,C_101),k3_xboole_0(k4_xboole_0(B_100,C_101),B_100)) = k2_xboole_0(B_100,k4_xboole_0(B_100,C_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1132,c_2660])).

tff(c_2762,plain,(
    ! [B_100,C_101] : k5_xboole_0(k3_xboole_0(B_100,C_101),k4_xboole_0(B_100,C_101)) = B_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1687,c_990,c_2,c_2691])).

tff(c_10170,plain,(
    ! [A_245,B_246,C_247] : k5_xboole_0(k5_xboole_0(A_245,B_246),k5_xboole_0(k3_xboole_0(A_245,B_246),C_247)) = k5_xboole_0(k2_xboole_0(A_245,B_246),C_247) ),
    inference(superposition,[status(thm),theory(equality)],[c_1143,c_26])).

tff(c_10305,plain,(
    ! [B_100,C_101] : k5_xboole_0(k2_xboole_0(B_100,C_101),k4_xboole_0(B_100,C_101)) = k5_xboole_0(k5_xboole_0(B_100,C_101),B_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_2762,c_10170])).

tff(c_10509,plain,(
    ! [B_248,C_249] : k5_xboole_0(k2_xboole_0(B_248,C_249),k4_xboole_0(B_248,C_249)) = C_249 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2992,c_26,c_10305])).

tff(c_2891,plain,(
    ! [B_4,C_88] : k5_xboole_0(B_4,k5_xboole_0(B_4,C_88)) = C_88 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1694,c_627])).

tff(c_3000,plain,(
    ! [B_153,A_154] : k5_xboole_0(B_153,k5_xboole_0(A_154,B_153)) = A_154 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2954])).

tff(c_3039,plain,(
    ! [B_4,C_88] : k5_xboole_0(k5_xboole_0(B_4,C_88),C_88) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_2891,c_3000])).

tff(c_11006,plain,(
    ! [C_256,B_257] : k5_xboole_0(C_256,k4_xboole_0(B_257,C_256)) = k2_xboole_0(B_257,C_256) ),
    inference(superposition,[status(thm),theory(equality)],[c_10509,c_3039])).

tff(c_1210,plain,(
    ! [A_1,B_2] : k5_xboole_0(k5_xboole_0(A_1,B_2),k3_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1143])).

tff(c_11042,plain,(
    ! [B_257,C_256] : k5_xboole_0(k2_xboole_0(B_257,C_256),k3_xboole_0(k4_xboole_0(B_257,C_256),C_256)) = k2_xboole_0(C_256,k4_xboole_0(B_257,C_256)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11006,c_1210])).

tff(c_11138,plain,(
    ! [C_256,B_257] : k2_xboole_0(C_256,B_257) = k2_xboole_0(B_257,C_256) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2766,c_24,c_1446,c_2,c_11042])).

tff(c_44,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_11158,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11138,c_44])).

tff(c_11159,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11138,c_2766,c_11158])).

tff(c_11348,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1688,c_11159])).

tff(c_11352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_11348])).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 17:58:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.54/2.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.54/2.57  
% 6.54/2.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.54/2.58  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 6.54/2.58  
% 6.54/2.58  %Foreground sorts:
% 6.54/2.58  
% 6.54/2.58  
% 6.54/2.58  %Background operators:
% 6.54/2.58  
% 6.54/2.58  
% 6.54/2.58  %Foreground operators:
% 6.54/2.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.54/2.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.54/2.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.54/2.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.54/2.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.54/2.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.54/2.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.54/2.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.54/2.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.54/2.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.54/2.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.54/2.58  tff('#skF_2', type, '#skF_2': $i).
% 6.54/2.58  tff('#skF_1', type, '#skF_1': $i).
% 6.54/2.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.54/2.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.54/2.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.54/2.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.54/2.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.54/2.58  
% 6.54/2.59  tff(f_74, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 6.54/2.59  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.54/2.59  tff(f_67, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.54/2.59  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.54/2.59  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.54/2.59  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.54/2.59  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.54/2.59  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 6.54/2.59  tff(f_49, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 6.54/2.59  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.54/2.59  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.54/2.59  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.54/2.59  tff(c_46, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.54/2.59  tff(c_24, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.54/2.59  tff(c_240, plain, (![A_61, B_62]: (r1_tarski(k1_tarski(A_61), B_62) | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.54/2.59  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.54/2.59  tff(c_250, plain, (![A_61, B_62]: (k4_xboole_0(k1_tarski(A_61), B_62)=k1_xboole_0 | ~r2_hidden(A_61, B_62))), inference(resolution, [status(thm)], [c_240, c_12])).
% 6.54/2.59  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.54/2.59  tff(c_299, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k3_xboole_0(A_64, B_65))=k4_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.54/2.59  tff(c_317, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_299])).
% 6.54/2.59  tff(c_26, plain, (![A_18, B_19, C_20]: (k5_xboole_0(k5_xboole_0(A_18, B_19), C_20)=k5_xboole_0(A_18, k5_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.54/2.59  tff(c_1143, plain, (![A_102, B_103]: (k5_xboole_0(k5_xboole_0(A_102, B_103), k3_xboole_0(A_102, B_103))=k2_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.54/2.59  tff(c_1189, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k5_xboole_0(B_19, k3_xboole_0(A_18, B_19)))=k2_xboole_0(A_18, B_19))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1143])).
% 6.54/2.59  tff(c_1626, plain, (![A_119, B_120]: (k5_xboole_0(A_119, k4_xboole_0(B_120, A_119))=k2_xboole_0(A_119, B_120))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_1189])).
% 6.54/2.59  tff(c_1669, plain, (![B_62, A_61]: (k2_xboole_0(B_62, k1_tarski(A_61))=k5_xboole_0(B_62, k1_xboole_0) | ~r2_hidden(A_61, B_62))), inference(superposition, [status(thm), theory('equality')], [c_250, c_1626])).
% 6.54/2.59  tff(c_1688, plain, (![B_62, A_61]: (k2_xboole_0(B_62, k1_tarski(A_61))=B_62 | ~r2_hidden(A_61, B_62))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1669])).
% 6.54/2.59  tff(c_22, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k3_xboole_0(A_14, B_15), C_16)=k3_xboole_0(A_14, k4_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.54/2.59  tff(c_20, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.54/2.59  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.54/2.59  tff(c_186, plain, (![A_56, B_57]: (k4_xboole_0(A_56, B_57)=k1_xboole_0 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.54/2.59  tff(c_198, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_186])).
% 6.54/2.59  tff(c_152, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.54/2.59  tff(c_164, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_152])).
% 6.54/2.59  tff(c_311, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_164, c_299])).
% 6.54/2.59  tff(c_324, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_198, c_311])).
% 6.54/2.59  tff(c_948, plain, (![A_95, B_96, C_97]: (k4_xboole_0(k3_xboole_0(A_95, B_96), C_97)=k3_xboole_0(A_95, k4_xboole_0(B_96, C_97)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.54/2.59  tff(c_1075, plain, (![B_100, C_101]: (k3_xboole_0(B_100, k4_xboole_0(B_100, C_101))=k4_xboole_0(B_100, C_101))), inference(superposition, [status(thm), theory('equality')], [c_164, c_948])).
% 6.54/2.59  tff(c_1091, plain, (![B_100, C_101]: (k5_xboole_0(k4_xboole_0(B_100, C_101), k4_xboole_0(B_100, C_101))=k4_xboole_0(k4_xboole_0(B_100, C_101), B_100))), inference(superposition, [status(thm), theory('equality')], [c_1075, c_317])).
% 6.54/2.59  tff(c_1300, plain, (![B_106, C_107]: (k4_xboole_0(k4_xboole_0(B_106, C_107), B_106)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_324, c_1091])).
% 6.54/2.59  tff(c_1413, plain, (![A_114, B_115]: (k4_xboole_0(k3_xboole_0(A_114, B_115), A_114)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_1300])).
% 6.54/2.59  tff(c_1446, plain, (![C_16, B_15]: (k3_xboole_0(C_16, k4_xboole_0(B_15, C_16))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_1413])).
% 6.54/2.59  tff(c_1223, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_1189])).
% 6.54/2.59  tff(c_2660, plain, (![A_147, B_148]: (k5_xboole_0(k5_xboole_0(A_147, B_148), k3_xboole_0(B_148, A_147))=k2_xboole_0(A_147, B_148))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1143])).
% 6.54/2.59  tff(c_2706, plain, (![A_18, B_19]: (k5_xboole_0(k2_xboole_0(A_18, B_19), k3_xboole_0(k4_xboole_0(B_19, A_18), A_18))=k2_xboole_0(A_18, k4_xboole_0(B_19, A_18)))), inference(superposition, [status(thm), theory('equality')], [c_1223, c_2660])).
% 6.54/2.59  tff(c_2766, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1446, c_2, c_2706])).
% 6.54/2.59  tff(c_589, plain, (![A_86, B_87, C_88]: (k5_xboole_0(k5_xboole_0(A_86, B_87), C_88)=k5_xboole_0(A_86, k5_xboole_0(B_87, C_88)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.54/2.59  tff(c_631, plain, (![A_86, B_87]: (k5_xboole_0(A_86, k5_xboole_0(B_87, k5_xboole_0(A_86, B_87)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_324, c_589])).
% 6.54/2.59  tff(c_1678, plain, (![B_4]: (k5_xboole_0(B_4, k1_xboole_0)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_198, c_1626])).
% 6.54/2.59  tff(c_1690, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1678])).
% 6.54/2.59  tff(c_1204, plain, (![B_4]: (k5_xboole_0(k5_xboole_0(B_4, B_4), B_4)=k2_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_164, c_1143])).
% 6.54/2.59  tff(c_1226, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=k2_xboole_0(B_4, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_1204])).
% 6.54/2.59  tff(c_1694, plain, (![B_4]: (k5_xboole_0(k1_xboole_0, B_4)=B_4)), inference(demodulation, [status(thm), theory('equality')], [c_1690, c_1226])).
% 6.54/2.59  tff(c_627, plain, (![B_4, C_88]: (k5_xboole_0(B_4, k5_xboole_0(B_4, C_88))=k5_xboole_0(k1_xboole_0, C_88))), inference(superposition, [status(thm), theory('equality')], [c_324, c_589])).
% 6.54/2.59  tff(c_2892, plain, (![B_151, C_152]: (k5_xboole_0(B_151, k5_xboole_0(B_151, C_152))=C_152)), inference(demodulation, [status(thm), theory('equality')], [c_1694, c_627])).
% 6.54/2.59  tff(c_2954, plain, (![B_87, A_86]: (k5_xboole_0(B_87, k5_xboole_0(A_86, B_87))=k5_xboole_0(A_86, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_631, c_2892])).
% 6.54/2.59  tff(c_2992, plain, (![B_87, A_86]: (k5_xboole_0(B_87, k5_xboole_0(A_86, B_87))=A_86)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2954])).
% 6.54/2.59  tff(c_1131, plain, (![B_100, C_101]: (k4_xboole_0(k4_xboole_0(B_100, C_101), B_100)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_324, c_1091])).
% 6.54/2.59  tff(c_1659, plain, (![B_100, C_101]: (k2_xboole_0(B_100, k4_xboole_0(B_100, C_101))=k5_xboole_0(B_100, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1131, c_1626])).
% 6.54/2.59  tff(c_1687, plain, (![B_100, C_101]: (k2_xboole_0(B_100, k4_xboole_0(B_100, C_101))=B_100)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1659])).
% 6.54/2.59  tff(c_990, plain, (![B_4, C_97]: (k3_xboole_0(B_4, k4_xboole_0(B_4, C_97))=k4_xboole_0(B_4, C_97))), inference(superposition, [status(thm), theory('equality')], [c_164, c_948])).
% 6.54/2.59  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.54/2.59  tff(c_1094, plain, (![B_100, C_101]: (k5_xboole_0(B_100, k4_xboole_0(B_100, C_101))=k4_xboole_0(B_100, k4_xboole_0(B_100, C_101)))), inference(superposition, [status(thm), theory('equality')], [c_1075, c_14])).
% 6.54/2.60  tff(c_1132, plain, (![B_100, C_101]: (k5_xboole_0(B_100, k4_xboole_0(B_100, C_101))=k3_xboole_0(B_100, C_101))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1094])).
% 6.54/2.60  tff(c_2691, plain, (![B_100, C_101]: (k5_xboole_0(k3_xboole_0(B_100, C_101), k3_xboole_0(k4_xboole_0(B_100, C_101), B_100))=k2_xboole_0(B_100, k4_xboole_0(B_100, C_101)))), inference(superposition, [status(thm), theory('equality')], [c_1132, c_2660])).
% 6.54/2.60  tff(c_2762, plain, (![B_100, C_101]: (k5_xboole_0(k3_xboole_0(B_100, C_101), k4_xboole_0(B_100, C_101))=B_100)), inference(demodulation, [status(thm), theory('equality')], [c_1687, c_990, c_2, c_2691])).
% 6.54/2.60  tff(c_10170, plain, (![A_245, B_246, C_247]: (k5_xboole_0(k5_xboole_0(A_245, B_246), k5_xboole_0(k3_xboole_0(A_245, B_246), C_247))=k5_xboole_0(k2_xboole_0(A_245, B_246), C_247))), inference(superposition, [status(thm), theory('equality')], [c_1143, c_26])).
% 6.54/2.60  tff(c_10305, plain, (![B_100, C_101]: (k5_xboole_0(k2_xboole_0(B_100, C_101), k4_xboole_0(B_100, C_101))=k5_xboole_0(k5_xboole_0(B_100, C_101), B_100))), inference(superposition, [status(thm), theory('equality')], [c_2762, c_10170])).
% 6.54/2.60  tff(c_10509, plain, (![B_248, C_249]: (k5_xboole_0(k2_xboole_0(B_248, C_249), k4_xboole_0(B_248, C_249))=C_249)), inference(demodulation, [status(thm), theory('equality')], [c_2992, c_26, c_10305])).
% 6.54/2.60  tff(c_2891, plain, (![B_4, C_88]: (k5_xboole_0(B_4, k5_xboole_0(B_4, C_88))=C_88)), inference(demodulation, [status(thm), theory('equality')], [c_1694, c_627])).
% 6.54/2.60  tff(c_3000, plain, (![B_153, A_154]: (k5_xboole_0(B_153, k5_xboole_0(A_154, B_153))=A_154)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2954])).
% 6.54/2.60  tff(c_3039, plain, (![B_4, C_88]: (k5_xboole_0(k5_xboole_0(B_4, C_88), C_88)=B_4)), inference(superposition, [status(thm), theory('equality')], [c_2891, c_3000])).
% 6.54/2.60  tff(c_11006, plain, (![C_256, B_257]: (k5_xboole_0(C_256, k4_xboole_0(B_257, C_256))=k2_xboole_0(B_257, C_256))), inference(superposition, [status(thm), theory('equality')], [c_10509, c_3039])).
% 6.54/2.60  tff(c_1210, plain, (![A_1, B_2]: (k5_xboole_0(k5_xboole_0(A_1, B_2), k3_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1143])).
% 6.54/2.60  tff(c_11042, plain, (![B_257, C_256]: (k5_xboole_0(k2_xboole_0(B_257, C_256), k3_xboole_0(k4_xboole_0(B_257, C_256), C_256))=k2_xboole_0(C_256, k4_xboole_0(B_257, C_256)))), inference(superposition, [status(thm), theory('equality')], [c_11006, c_1210])).
% 6.54/2.60  tff(c_11138, plain, (![C_256, B_257]: (k2_xboole_0(C_256, B_257)=k2_xboole_0(B_257, C_256))), inference(demodulation, [status(thm), theory('equality')], [c_2766, c_24, c_1446, c_2, c_11042])).
% 6.54/2.60  tff(c_44, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.54/2.60  tff(c_11158, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11138, c_44])).
% 6.54/2.60  tff(c_11159, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11138, c_2766, c_11158])).
% 6.54/2.60  tff(c_11348, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1688, c_11159])).
% 6.54/2.60  tff(c_11352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_11348])).
% 6.54/2.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.54/2.60  
% 6.54/2.60  Inference rules
% 6.54/2.60  ----------------------
% 6.54/2.60  #Ref     : 0
% 6.54/2.60  #Sup     : 2791
% 6.54/2.60  #Fact    : 0
% 6.54/2.60  #Define  : 0
% 6.54/2.60  #Split   : 1
% 6.54/2.60  #Chain   : 0
% 6.54/2.60  #Close   : 0
% 6.54/2.60  
% 6.54/2.60  Ordering : KBO
% 6.54/2.60  
% 6.54/2.60  Simplification rules
% 6.54/2.60  ----------------------
% 6.54/2.60  #Subsume      : 113
% 6.54/2.60  #Demod        : 3542
% 6.54/2.60  #Tautology    : 1814
% 6.54/2.60  #SimpNegUnit  : 0
% 6.54/2.60  #BackRed      : 17
% 6.54/2.60  
% 6.54/2.60  #Partial instantiations: 0
% 6.54/2.60  #Strategies tried      : 1
% 6.54/2.60  
% 6.54/2.60  Timing (in seconds)
% 6.54/2.60  ----------------------
% 6.54/2.60  Preprocessing        : 0.33
% 6.54/2.60  Parsing              : 0.18
% 6.54/2.60  CNF conversion       : 0.02
% 6.54/2.60  Main loop            : 1.44
% 6.54/2.60  Inferencing          : 0.40
% 6.54/2.60  Reduction            : 0.73
% 6.54/2.60  Demodulation         : 0.63
% 6.54/2.60  BG Simplification    : 0.05
% 6.54/2.60  Subsumption          : 0.18
% 6.54/2.60  Abstraction          : 0.08
% 6.54/2.60  MUC search           : 0.00
% 6.54/2.60  Cooper               : 0.00
% 6.54/2.60  Total                : 1.81
% 6.54/2.60  Index Insertion      : 0.00
% 6.54/2.60  Index Deletion       : 0.00
% 6.54/2.60  Index Matching       : 0.00
% 6.54/2.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
