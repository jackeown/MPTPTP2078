%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:06 EST 2020

% Result     : Theorem 8.06s
% Output     : CNFRefutation 8.06s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 283 expanded)
%              Number of leaves         :   31 ( 109 expanded)
%              Depth                    :   15
%              Number of atoms          :   66 ( 298 expanded)
%              Number of equality atoms :   56 ( 241 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_243,plain,(
    ! [A_67,B_68] : k5_xboole_0(A_67,k4_xboole_0(B_68,A_67)) = k2_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_255,plain,(
    ! [A_69] : k5_xboole_0(k1_xboole_0,A_69) = k2_xboole_0(k1_xboole_0,A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_243])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_265,plain,(
    ! [A_69] : k5_xboole_0(A_69,k1_xboole_0) = k2_xboole_0(k1_xboole_0,A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_4])).

tff(c_16,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_135,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_157,plain,(
    ! [A_63] : k3_xboole_0(k1_xboole_0,A_63) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_135])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_166,plain,(
    ! [A_63] : k3_xboole_0(A_63,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_2])).

tff(c_376,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k4_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_393,plain,(
    ! [A_63] : k5_xboole_0(A_63,k1_xboole_0) = k4_xboole_0(A_63,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_376])).

tff(c_410,plain,(
    ! [A_63] : k2_xboole_0(k1_xboole_0,A_63) = A_63 ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_18,c_393])).

tff(c_252,plain,(
    ! [A_12] : k5_xboole_0(k1_xboole_0,A_12) = k2_xboole_0(k1_xboole_0,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_243])).

tff(c_437,plain,(
    ! [A_12] : k5_xboole_0(k1_xboole_0,A_12) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_252])).

tff(c_354,plain,(
    ! [A_74,B_75] : k4_xboole_0(A_74,k4_xboole_0(A_74,B_75)) = k3_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_372,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_354])).

tff(c_375,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_372])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_146,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_135])).

tff(c_399,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_376])).

tff(c_689,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_399])).

tff(c_40,plain,(
    ! [A_48,B_49] : r1_tarski(k1_tarski(A_48),k2_tarski(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1160,plain,(
    ! [A_122,B_123] : k3_xboole_0(k1_tarski(A_122),k2_tarski(A_122,B_123)) = k1_tarski(A_122) ),
    inference(resolution,[status(thm)],[c_40,c_135])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1166,plain,(
    ! [A_122,B_123] : k5_xboole_0(k1_tarski(A_122),k1_tarski(A_122)) = k4_xboole_0(k1_tarski(A_122),k2_tarski(A_122,B_123)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1160,c_12])).

tff(c_1174,plain,(
    ! [A_122,B_123] : k4_xboole_0(k1_tarski(A_122),k2_tarski(A_122,B_123)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_1166])).

tff(c_1196,plain,(
    ! [A_126,B_127] : k5_xboole_0(A_126,k3_xboole_0(B_127,A_126)) = k4_xboole_0(A_126,B_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_376])).

tff(c_690,plain,(
    ! [B_94] : k5_xboole_0(B_94,B_94) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_399])).

tff(c_22,plain,(
    ! [A_15,B_16,C_17] : k5_xboole_0(k5_xboole_0(A_15,B_16),C_17) = k5_xboole_0(A_15,k5_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_695,plain,(
    ! [B_94,C_17] : k5_xboole_0(B_94,k5_xboole_0(B_94,C_17)) = k5_xboole_0(k1_xboole_0,C_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_690,c_22])).

tff(c_723,plain,(
    ! [B_94,C_17] : k5_xboole_0(B_94,k5_xboole_0(B_94,C_17)) = C_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_695])).

tff(c_1604,plain,(
    ! [A_135,B_136] : k5_xboole_0(A_135,k4_xboole_0(A_135,B_136)) = k3_xboole_0(B_136,A_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_1196,c_723])).

tff(c_1657,plain,(
    ! [A_122,B_123] : k3_xboole_0(k2_tarski(A_122,B_123),k1_tarski(A_122)) = k5_xboole_0(k1_tarski(A_122),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1174,c_1604])).

tff(c_1687,plain,(
    ! [A_122,B_123] : k3_xboole_0(k2_tarski(A_122,B_123),k1_tarski(A_122)) = k1_tarski(A_122) ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_4,c_1657])).

tff(c_771,plain,(
    ! [B_101,C_102] : k5_xboole_0(B_101,k5_xboole_0(B_101,C_102)) = C_102 ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_695])).

tff(c_839,plain,(
    ! [A_103,B_104] : k5_xboole_0(A_103,k5_xboole_0(B_104,A_103)) = B_104 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_771])).

tff(c_899,plain,(
    ! [A_7,B_8] : k5_xboole_0(k3_xboole_0(A_7,B_8),k4_xboole_0(A_7,B_8)) = A_7 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_839])).

tff(c_20,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1329,plain,(
    ! [A_130,B_131] : k5_xboole_0(A_130,k4_xboole_0(A_130,B_131)) = k3_xboole_0(A_130,B_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_771])).

tff(c_1382,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,k4_xboole_0(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1329])).

tff(c_1399,plain,(
    ! [A_13,B_14] : k3_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1382])).

tff(c_366,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,k4_xboole_0(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_354])).

tff(c_3128,plain,(
    ! [A_166,B_167] : k4_xboole_0(A_166,k3_xboole_0(A_166,B_167)) = k4_xboole_0(A_166,B_167) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1399,c_366])).

tff(c_24,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3168,plain,(
    ! [A_166,B_167] : k5_xboole_0(k3_xboole_0(A_166,B_167),k4_xboole_0(A_166,B_167)) = k2_xboole_0(k3_xboole_0(A_166,B_167),A_166) ),
    inference(superposition,[status(thm),theory(equality)],[c_3128,c_24])).

tff(c_3218,plain,(
    ! [A_168,B_169] : k2_xboole_0(k3_xboole_0(A_168,B_169),A_168) = A_168 ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_3168])).

tff(c_3240,plain,(
    ! [A_122,B_123] : k2_xboole_0(k1_tarski(A_122),k2_tarski(A_122,B_123)) = k2_tarski(A_122,B_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_1687,c_3218])).

tff(c_42,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3240,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:40:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.06/3.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.06/3.25  
% 8.06/3.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.06/3.25  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 8.06/3.25  
% 8.06/3.25  %Foreground sorts:
% 8.06/3.25  
% 8.06/3.25  
% 8.06/3.25  %Background operators:
% 8.06/3.25  
% 8.06/3.25  
% 8.06/3.25  %Foreground operators:
% 8.06/3.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.06/3.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.06/3.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.06/3.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.06/3.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.06/3.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.06/3.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.06/3.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.06/3.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.06/3.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.06/3.25  tff('#skF_2', type, '#skF_2': $i).
% 8.06/3.25  tff('#skF_1', type, '#skF_1': $i).
% 8.06/3.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.06/3.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.06/3.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.06/3.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.06/3.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.06/3.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.06/3.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.06/3.25  
% 8.06/3.26  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.06/3.26  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.06/3.26  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 8.06/3.26  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.06/3.26  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.06/3.26  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.06/3.26  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.06/3.26  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.06/3.26  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.06/3.26  tff(f_67, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 8.06/3.26  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.06/3.26  tff(f_70, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 8.06/3.26  tff(c_18, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.06/3.26  tff(c_243, plain, (![A_67, B_68]: (k5_xboole_0(A_67, k4_xboole_0(B_68, A_67))=k2_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.06/3.26  tff(c_255, plain, (![A_69]: (k5_xboole_0(k1_xboole_0, A_69)=k2_xboole_0(k1_xboole_0, A_69))), inference(superposition, [status(thm), theory('equality')], [c_18, c_243])).
% 8.06/3.26  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.06/3.26  tff(c_265, plain, (![A_69]: (k5_xboole_0(A_69, k1_xboole_0)=k2_xboole_0(k1_xboole_0, A_69))), inference(superposition, [status(thm), theory('equality')], [c_255, c_4])).
% 8.06/3.26  tff(c_16, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.06/3.26  tff(c_135, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.06/3.26  tff(c_157, plain, (![A_63]: (k3_xboole_0(k1_xboole_0, A_63)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_135])).
% 8.06/3.26  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.06/3.26  tff(c_166, plain, (![A_63]: (k3_xboole_0(A_63, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_157, c_2])).
% 8.06/3.26  tff(c_376, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k4_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.06/3.26  tff(c_393, plain, (![A_63]: (k5_xboole_0(A_63, k1_xboole_0)=k4_xboole_0(A_63, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_166, c_376])).
% 8.06/3.26  tff(c_410, plain, (![A_63]: (k2_xboole_0(k1_xboole_0, A_63)=A_63)), inference(demodulation, [status(thm), theory('equality')], [c_265, c_18, c_393])).
% 8.06/3.26  tff(c_252, plain, (![A_12]: (k5_xboole_0(k1_xboole_0, A_12)=k2_xboole_0(k1_xboole_0, A_12))), inference(superposition, [status(thm), theory('equality')], [c_18, c_243])).
% 8.06/3.26  tff(c_437, plain, (![A_12]: (k5_xboole_0(k1_xboole_0, A_12)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_410, c_252])).
% 8.06/3.26  tff(c_354, plain, (![A_74, B_75]: (k4_xboole_0(A_74, k4_xboole_0(A_74, B_75))=k3_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.06/3.26  tff(c_372, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_354])).
% 8.06/3.26  tff(c_375, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_166, c_372])).
% 8.06/3.26  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.06/3.26  tff(c_146, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_135])).
% 8.06/3.26  tff(c_399, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_146, c_376])).
% 8.06/3.26  tff(c_689, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_375, c_399])).
% 8.06/3.26  tff(c_40, plain, (![A_48, B_49]: (r1_tarski(k1_tarski(A_48), k2_tarski(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.06/3.26  tff(c_1160, plain, (![A_122, B_123]: (k3_xboole_0(k1_tarski(A_122), k2_tarski(A_122, B_123))=k1_tarski(A_122))), inference(resolution, [status(thm)], [c_40, c_135])).
% 8.06/3.26  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.06/3.26  tff(c_1166, plain, (![A_122, B_123]: (k5_xboole_0(k1_tarski(A_122), k1_tarski(A_122))=k4_xboole_0(k1_tarski(A_122), k2_tarski(A_122, B_123)))), inference(superposition, [status(thm), theory('equality')], [c_1160, c_12])).
% 8.06/3.26  tff(c_1174, plain, (![A_122, B_123]: (k4_xboole_0(k1_tarski(A_122), k2_tarski(A_122, B_123))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_689, c_1166])).
% 8.06/3.26  tff(c_1196, plain, (![A_126, B_127]: (k5_xboole_0(A_126, k3_xboole_0(B_127, A_126))=k4_xboole_0(A_126, B_127))), inference(superposition, [status(thm), theory('equality')], [c_2, c_376])).
% 8.06/3.26  tff(c_690, plain, (![B_94]: (k5_xboole_0(B_94, B_94)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_375, c_399])).
% 8.06/3.26  tff(c_22, plain, (![A_15, B_16, C_17]: (k5_xboole_0(k5_xboole_0(A_15, B_16), C_17)=k5_xboole_0(A_15, k5_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.06/3.26  tff(c_695, plain, (![B_94, C_17]: (k5_xboole_0(B_94, k5_xboole_0(B_94, C_17))=k5_xboole_0(k1_xboole_0, C_17))), inference(superposition, [status(thm), theory('equality')], [c_690, c_22])).
% 8.06/3.26  tff(c_723, plain, (![B_94, C_17]: (k5_xboole_0(B_94, k5_xboole_0(B_94, C_17))=C_17)), inference(demodulation, [status(thm), theory('equality')], [c_437, c_695])).
% 8.06/3.26  tff(c_1604, plain, (![A_135, B_136]: (k5_xboole_0(A_135, k4_xboole_0(A_135, B_136))=k3_xboole_0(B_136, A_135))), inference(superposition, [status(thm), theory('equality')], [c_1196, c_723])).
% 8.06/3.26  tff(c_1657, plain, (![A_122, B_123]: (k3_xboole_0(k2_tarski(A_122, B_123), k1_tarski(A_122))=k5_xboole_0(k1_tarski(A_122), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1174, c_1604])).
% 8.06/3.26  tff(c_1687, plain, (![A_122, B_123]: (k3_xboole_0(k2_tarski(A_122, B_123), k1_tarski(A_122))=k1_tarski(A_122))), inference(demodulation, [status(thm), theory('equality')], [c_437, c_4, c_1657])).
% 8.06/3.26  tff(c_771, plain, (![B_101, C_102]: (k5_xboole_0(B_101, k5_xboole_0(B_101, C_102))=C_102)), inference(demodulation, [status(thm), theory('equality')], [c_437, c_695])).
% 8.06/3.26  tff(c_839, plain, (![A_103, B_104]: (k5_xboole_0(A_103, k5_xboole_0(B_104, A_103))=B_104)), inference(superposition, [status(thm), theory('equality')], [c_4, c_771])).
% 8.06/3.26  tff(c_899, plain, (![A_7, B_8]: (k5_xboole_0(k3_xboole_0(A_7, B_8), k4_xboole_0(A_7, B_8))=A_7)), inference(superposition, [status(thm), theory('equality')], [c_12, c_839])).
% 8.06/3.26  tff(c_20, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.06/3.26  tff(c_1329, plain, (![A_130, B_131]: (k5_xboole_0(A_130, k4_xboole_0(A_130, B_131))=k3_xboole_0(A_130, B_131))), inference(superposition, [status(thm), theory('equality')], [c_12, c_771])).
% 8.06/3.26  tff(c_1382, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k3_xboole_0(A_13, k4_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1329])).
% 8.06/3.26  tff(c_1399, plain, (![A_13, B_14]: (k3_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1382])).
% 8.06/3.26  tff(c_366, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k3_xboole_0(A_13, k4_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_354])).
% 8.06/3.26  tff(c_3128, plain, (![A_166, B_167]: (k4_xboole_0(A_166, k3_xboole_0(A_166, B_167))=k4_xboole_0(A_166, B_167))), inference(demodulation, [status(thm), theory('equality')], [c_1399, c_366])).
% 8.06/3.26  tff(c_24, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.06/3.26  tff(c_3168, plain, (![A_166, B_167]: (k5_xboole_0(k3_xboole_0(A_166, B_167), k4_xboole_0(A_166, B_167))=k2_xboole_0(k3_xboole_0(A_166, B_167), A_166))), inference(superposition, [status(thm), theory('equality')], [c_3128, c_24])).
% 8.06/3.26  tff(c_3218, plain, (![A_168, B_169]: (k2_xboole_0(k3_xboole_0(A_168, B_169), A_168)=A_168)), inference(demodulation, [status(thm), theory('equality')], [c_899, c_3168])).
% 8.06/3.26  tff(c_3240, plain, (![A_122, B_123]: (k2_xboole_0(k1_tarski(A_122), k2_tarski(A_122, B_123))=k2_tarski(A_122, B_123))), inference(superposition, [status(thm), theory('equality')], [c_1687, c_3218])).
% 8.06/3.26  tff(c_42, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.06/3.26  tff(c_12842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3240, c_42])).
% 8.06/3.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.06/3.26  
% 8.06/3.26  Inference rules
% 8.06/3.26  ----------------------
% 8.06/3.26  #Ref     : 0
% 8.06/3.26  #Sup     : 3188
% 8.06/3.26  #Fact    : 0
% 8.06/3.26  #Define  : 0
% 8.06/3.26  #Split   : 0
% 8.06/3.26  #Chain   : 0
% 8.06/3.26  #Close   : 0
% 8.06/3.26  
% 8.06/3.26  Ordering : KBO
% 8.06/3.26  
% 8.06/3.26  Simplification rules
% 8.06/3.26  ----------------------
% 8.06/3.26  #Subsume      : 183
% 8.06/3.26  #Demod        : 3708
% 8.06/3.26  #Tautology    : 1869
% 8.06/3.26  #SimpNegUnit  : 0
% 8.06/3.26  #BackRed      : 3
% 8.06/3.26  
% 8.06/3.26  #Partial instantiations: 0
% 8.06/3.26  #Strategies tried      : 1
% 8.06/3.26  
% 8.06/3.26  Timing (in seconds)
% 8.06/3.26  ----------------------
% 8.06/3.27  Preprocessing        : 0.31
% 8.06/3.27  Parsing              : 0.17
% 8.06/3.27  CNF conversion       : 0.02
% 8.06/3.27  Main loop            : 2.08
% 8.06/3.27  Inferencing          : 0.48
% 8.06/3.27  Reduction            : 1.22
% 8.06/3.27  Demodulation         : 1.11
% 8.06/3.27  BG Simplification    : 0.06
% 8.06/3.27  Subsumption          : 0.24
% 8.06/3.27  Abstraction          : 0.10
% 8.06/3.27  MUC search           : 0.00
% 8.06/3.27  Cooper               : 0.00
% 8.06/3.27  Total                : 2.42
% 8.06/3.27  Index Insertion      : 0.00
% 8.06/3.27  Index Deletion       : 0.00
% 8.06/3.27  Index Matching       : 0.00
% 8.06/3.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
