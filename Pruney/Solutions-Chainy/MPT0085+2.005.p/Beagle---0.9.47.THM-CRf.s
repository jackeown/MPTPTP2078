%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:11 EST 2020

% Result     : Theorem 11.67s
% Output     : CNFRefutation 11.67s
% Verified   : 
% Statistics : Number of formulae       :  109 (9488 expanded)
%              Number of leaves         :   21 (3158 expanded)
%              Depth                    :   29
%              Number of atoms          :  107 (10904 expanded)
%              Number of equality atoms :   97 (9393 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

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

tff(c_20,plain,(
    ! [A_16,B_17] : k2_xboole_0(k3_xboole_0(A_16,B_17),k4_xboole_0(A_16,B_17)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_118,plain,(
    ! [A_34,B_35] : k2_xboole_0(A_34,k4_xboole_0(B_35,A_34)) = k2_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_127,plain,(
    ! [A_14,B_15] : k2_xboole_0(k4_xboole_0(A_14,B_15),k3_xboole_0(A_14,B_15)) = k2_xboole_0(k4_xboole_0(A_14,B_15),A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_118])).

tff(c_307,plain,(
    ! [A_47,B_48] : k2_xboole_0(k4_xboole_0(A_47,B_48),k3_xboole_0(A_47,B_48)) = k2_xboole_0(A_47,k4_xboole_0(A_47,B_48)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_127])).

tff(c_313,plain,(
    ! [A_47,B_48] : k2_xboole_0(k3_xboole_0(A_47,B_48),k4_xboole_0(A_47,B_48)) = k2_xboole_0(A_47,k4_xboole_0(A_47,B_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_2])).

tff(c_342,plain,(
    ! [A_47,B_48] : k2_xboole_0(A_47,k4_xboole_0(A_47,B_48)) = A_47 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_313])).

tff(c_24,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_60,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = k1_xboole_0
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_60])).

tff(c_99,plain,(
    ! [A_32,B_33] : k2_xboole_0(k3_xboole_0(A_32,B_33),k4_xboole_0(A_32,B_33)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_111,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_99])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] : k4_xboole_0(k4_xboole_0(A_11,B_12),C_13) = k4_xboole_0(A_11,k2_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_334,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = k2_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_307])).

tff(c_478,plain,(
    k2_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_334])).

tff(c_135,plain,(
    ! [A_38,B_39,C_40] : k4_xboole_0(k4_xboole_0(A_38,B_39),C_40) = k4_xboole_0(A_38,k2_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_166,plain,(
    ! [A_14,B_15,C_40] : k4_xboole_0(A_14,k2_xboole_0(k4_xboole_0(A_14,B_15),C_40)) = k4_xboole_0(k3_xboole_0(A_14,B_15),C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_135])).

tff(c_482,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_166])).

tff(c_497,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_482])).

tff(c_543,plain,(
    ! [C_13] : k4_xboole_0(k4_xboole_0('#skF_1','#skF_1'),C_13) = k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,C_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_16])).

tff(c_3248,plain,(
    ! [C_107] : k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,C_107)) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_1',C_107)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_543])).

tff(c_3393,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2'))) = k4_xboole_0(k1_xboole_0,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_3248])).

tff(c_3433,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_1') = k4_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_3393])).

tff(c_3502,plain,(
    k4_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_1')) = k3_xboole_0(k1_xboole_0,'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3433,c_18])).

tff(c_555,plain,(
    k4_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_1')) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_18])).

tff(c_3576,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3502,c_555])).

tff(c_429,plain,(
    ! [A_52,B_53] : k2_xboole_0(A_52,k4_xboole_0(A_52,B_53)) = A_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_313])).

tff(c_14,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_440,plain,(
    ! [B_53] : k2_xboole_0(B_53,B_53) = B_53 ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_14])).

tff(c_549,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_1')) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_497,c_14])).

tff(c_560,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_549])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = B_27
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_78,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_74])).

tff(c_1178,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_1')) = k4_xboole_0('#skF_1','#skF_1')
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_78])).

tff(c_1192,plain,
    ( k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_1178])).

tff(c_1587,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1192])).

tff(c_3640,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3576,c_1587])).

tff(c_3499,plain,(
    k2_xboole_0(k3_xboole_0(k1_xboole_0,'#skF_1'),k4_xboole_0('#skF_1','#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3433,c_20])).

tff(c_130,plain,(
    ! [A_14,B_15] : k2_xboole_0(k4_xboole_0(A_14,B_15),k3_xboole_0(A_14,B_15)) = k2_xboole_0(A_14,k4_xboole_0(A_14,B_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_127])).

tff(c_698,plain,(
    ! [A_61,B_62] : k2_xboole_0(k4_xboole_0(A_61,B_62),k3_xboole_0(A_61,B_62)) = A_61 ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_130])).

tff(c_2285,plain,(
    ! [A_97,B_98] : k4_xboole_0(k3_xboole_0(A_97,B_98),k3_xboole_0(A_97,B_98)) = k4_xboole_0(A_97,A_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_698,c_166])).

tff(c_3978,plain,(
    ! [A_111,B_112] : k2_xboole_0(k3_xboole_0(A_111,B_112),k4_xboole_0(A_111,A_111)) = k3_xboole_0(A_111,B_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_2285,c_342])).

tff(c_4018,plain,(
    k2_xboole_0(k3_xboole_0(k1_xboole_0,'#skF_1'),k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3576,c_3978])).

tff(c_4080,plain,(
    k3_xboole_0(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3576,c_3499,c_497,c_4018])).

tff(c_4082,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3640,c_4080])).

tff(c_4083,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1192])).

tff(c_428,plain,(
    ! [A_14,B_15] : k2_xboole_0(k4_xboole_0(A_14,B_15),k3_xboole_0(A_14,B_15)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_130])).

tff(c_4101,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1','#skF_1')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4083,c_428])).

tff(c_170,plain,(
    ! [A_38,B_39,B_15] : k4_xboole_0(A_38,k2_xboole_0(B_39,k4_xboole_0(k4_xboole_0(A_38,B_39),B_15))) = k3_xboole_0(k4_xboole_0(A_38,B_39),B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_135])).

tff(c_878,plain,(
    ! [A_68,B_69,B_70] : k4_xboole_0(A_68,k2_xboole_0(B_69,k4_xboole_0(A_68,k2_xboole_0(B_69,B_70)))) = k3_xboole_0(k4_xboole_0(A_68,B_69),B_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_170])).

tff(c_988,plain,(
    ! [A_47,B_70] : k3_xboole_0(k4_xboole_0(A_47,A_47),B_70) = k4_xboole_0(A_47,A_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_878])).

tff(c_4095,plain,(
    ! [B_70] : k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0(k1_xboole_0,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_4083,c_988])).

tff(c_4131,plain,(
    ! [B_70] : k3_xboole_0(k1_xboole_0,B_70) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4083,c_4095])).

tff(c_4128,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4083,c_18])).

tff(c_147,plain,(
    ! [C_40,A_38,B_39] : k2_xboole_0(C_40,k4_xboole_0(A_38,k2_xboole_0(B_39,C_40))) = k2_xboole_0(C_40,k4_xboole_0(A_38,B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_14])).

tff(c_972,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k2_xboole_0(B_39,k4_xboole_0(A_38,B_39))) = k3_xboole_0(k4_xboole_0(A_38,B_39),B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_878])).

tff(c_5853,plain,(
    ! [A_131,B_132] : k4_xboole_0(A_131,k2_xboole_0(B_132,A_131)) = k3_xboole_0(k4_xboole_0(A_131,B_132),B_132) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_972])).

tff(c_4739,plain,(
    ! [A_120,B_121,C_122] : k2_xboole_0(k3_xboole_0(k4_xboole_0(A_120,B_121),C_122),k4_xboole_0(A_120,k2_xboole_0(B_121,C_122))) = k4_xboole_0(A_120,B_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_20])).

tff(c_4787,plain,(
    ! [C_122] : k2_xboole_0(k3_xboole_0(k1_xboole_0,C_122),k4_xboole_0('#skF_1',k2_xboole_0('#skF_1',C_122))) = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4083,c_4739])).

tff(c_4887,plain,(
    ! [C_122] : k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',k2_xboole_0('#skF_1',C_122))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4131,c_4083,c_4787])).

tff(c_4138,plain,(
    ! [A_113,B_114,C_115] : k4_xboole_0(k4_xboole_0(A_113,B_114),k4_xboole_0(A_113,k2_xboole_0(B_114,C_115))) = k3_xboole_0(k4_xboole_0(A_113,B_114),C_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_18])).

tff(c_4189,plain,(
    ! [C_115] : k4_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',k2_xboole_0('#skF_1',C_115))) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_1'),C_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_4083,c_4138])).

tff(c_5162,plain,(
    ! [C_125] : k4_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',k2_xboole_0('#skF_1',C_125))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4083,c_988,c_4189])).

tff(c_5200,plain,(
    ! [C_125] : k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1',k2_xboole_0('#skF_1',C_125))) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_1',C_125)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5162,c_78])).

tff(c_5297,plain,(
    ! [C_126] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_1',C_126)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4887,c_5200])).

tff(c_5402,plain,(
    ! [B_2] : k4_xboole_0('#skF_1',k2_xboole_0(B_2,'#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_5297])).

tff(c_6151,plain,(
    ! [B_133] : k3_xboole_0(k4_xboole_0('#skF_1',B_133),B_133) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5853,c_5402])).

tff(c_6213,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_1'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4128,c_6151])).

tff(c_754,plain,(
    ! [A_63,B_64,C_65] : k2_xboole_0(A_63,k4_xboole_0(k3_xboole_0(A_63,B_64),C_65)) = A_63 ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_429])).

tff(c_806,plain,(
    ! [A_63,B_64,B_15] : k2_xboole_0(A_63,k3_xboole_0(k3_xboole_0(A_63,B_64),B_15)) = A_63 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_754])).

tff(c_6264,plain,(
    ! [B_15] : k2_xboole_0(k3_xboole_0('#skF_1','#skF_1'),k3_xboole_0(k1_xboole_0,B_15)) = k3_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6213,c_806])).

tff(c_6291,plain,(
    k3_xboole_0('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4101,c_2,c_4131,c_6264])).

tff(c_6464,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6291,c_6213])).

tff(c_6471,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6291,c_4128])).

tff(c_351,plain,(
    ! [A_49,B_50,C_51] : k4_xboole_0(A_49,k2_xboole_0(k4_xboole_0(A_49,B_50),C_51)) = k4_xboole_0(k3_xboole_0(A_49,B_50),C_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_135])).

tff(c_6629,plain,(
    ! [A_135,A_136,B_137] : k4_xboole_0(A_135,k2_xboole_0(A_136,k4_xboole_0(A_135,B_137))) = k4_xboole_0(k3_xboole_0(A_135,B_137),A_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_351])).

tff(c_6742,plain,(
    ! [A_136] : k4_xboole_0(k3_xboole_0('#skF_1',k1_xboole_0),A_136) = k4_xboole_0('#skF_1',k2_xboole_0(A_136,'#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6471,c_6629])).

tff(c_6972,plain,(
    ! [A_139] : k4_xboole_0(k1_xboole_0,A_139) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6464,c_5402,c_6742])).

tff(c_7160,plain,(
    ! [A_140] : k2_xboole_0(k1_xboole_0,A_140) = A_140 ),
    inference(superposition,[status(thm),theory(equality)],[c_6972,c_78])).

tff(c_7228,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_7160,c_111])).

tff(c_18790,plain,(
    ! [A_252,B_253,A_254] : k4_xboole_0(k4_xboole_0(A_252,B_253),k4_xboole_0(A_252,k2_xboole_0(A_254,B_253))) = k3_xboole_0(k4_xboole_0(A_252,B_253),A_254) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4138])).

tff(c_19050,plain,(
    ! [A_254] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_1',k2_xboole_0(A_254,'#skF_2'))) = k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),A_254) ),
    inference(superposition,[status(thm),theory(equality)],[c_7228,c_18790])).

tff(c_19222,plain,(
    ! [A_254] : k3_xboole_0('#skF_1',k2_xboole_0(A_254,'#skF_2')) = k3_xboole_0('#skF_1',A_254) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7228,c_18,c_19050])).

tff(c_22,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) != k3_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_25,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) != k3_xboole_0('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_22568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19222,c_25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.67/4.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.67/4.21  
% 11.67/4.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.67/4.22  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.67/4.22  
% 11.67/4.22  %Foreground sorts:
% 11.67/4.22  
% 11.67/4.22  
% 11.67/4.22  %Background operators:
% 11.67/4.22  
% 11.67/4.22  
% 11.67/4.22  %Foreground operators:
% 11.67/4.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.67/4.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.67/4.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.67/4.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.67/4.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.67/4.22  tff('#skF_2', type, '#skF_2': $i).
% 11.67/4.22  tff('#skF_3', type, '#skF_3': $i).
% 11.67/4.22  tff('#skF_1', type, '#skF_1': $i).
% 11.67/4.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.67/4.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.67/4.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.67/4.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.67/4.22  
% 11.67/4.24  tff(f_47, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 11.67/4.24  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 11.67/4.24  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.67/4.24  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 11.67/4.24  tff(f_52, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 11.67/4.24  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 11.67/4.24  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 11.67/4.24  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 11.67/4.24  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.67/4.24  tff(c_20, plain, (![A_16, B_17]: (k2_xboole_0(k3_xboole_0(A_16, B_17), k4_xboole_0(A_16, B_17))=A_16)), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.67/4.24  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.67/4.24  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.67/4.24  tff(c_118, plain, (![A_34, B_35]: (k2_xboole_0(A_34, k4_xboole_0(B_35, A_34))=k2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.67/4.24  tff(c_127, plain, (![A_14, B_15]: (k2_xboole_0(k4_xboole_0(A_14, B_15), k3_xboole_0(A_14, B_15))=k2_xboole_0(k4_xboole_0(A_14, B_15), A_14))), inference(superposition, [status(thm), theory('equality')], [c_18, c_118])).
% 11.67/4.24  tff(c_307, plain, (![A_47, B_48]: (k2_xboole_0(k4_xboole_0(A_47, B_48), k3_xboole_0(A_47, B_48))=k2_xboole_0(A_47, k4_xboole_0(A_47, B_48)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_127])).
% 11.67/4.24  tff(c_313, plain, (![A_47, B_48]: (k2_xboole_0(k3_xboole_0(A_47, B_48), k4_xboole_0(A_47, B_48))=k2_xboole_0(A_47, k4_xboole_0(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_307, c_2])).
% 11.67/4.24  tff(c_342, plain, (![A_47, B_48]: (k2_xboole_0(A_47, k4_xboole_0(A_47, B_48))=A_47)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_313])).
% 11.67/4.24  tff(c_24, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.67/4.24  tff(c_60, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=k1_xboole_0 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.67/4.24  tff(c_68, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_60])).
% 11.67/4.24  tff(c_99, plain, (![A_32, B_33]: (k2_xboole_0(k3_xboole_0(A_32, B_33), k4_xboole_0(A_32, B_33))=A_32)), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.67/4.24  tff(c_111, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_68, c_99])).
% 11.67/4.24  tff(c_16, plain, (![A_11, B_12, C_13]: (k4_xboole_0(k4_xboole_0(A_11, B_12), C_13)=k4_xboole_0(A_11, k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.67/4.24  tff(c_334, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)=k2_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_307])).
% 11.67/4.24  tff(c_478, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_342, c_334])).
% 11.67/4.24  tff(c_135, plain, (![A_38, B_39, C_40]: (k4_xboole_0(k4_xboole_0(A_38, B_39), C_40)=k4_xboole_0(A_38, k2_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.67/4.24  tff(c_166, plain, (![A_14, B_15, C_40]: (k4_xboole_0(A_14, k2_xboole_0(k4_xboole_0(A_14, B_15), C_40))=k4_xboole_0(k3_xboole_0(A_14, B_15), C_40))), inference(superposition, [status(thm), theory('equality')], [c_18, c_135])).
% 11.67/4.24  tff(c_482, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_478, c_166])).
% 11.67/4.24  tff(c_497, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_482])).
% 11.67/4.24  tff(c_543, plain, (![C_13]: (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_1'), C_13)=k4_xboole_0(k1_xboole_0, k2_xboole_0(k1_xboole_0, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_497, c_16])).
% 11.67/4.24  tff(c_3248, plain, (![C_107]: (k4_xboole_0(k1_xboole_0, k2_xboole_0(k1_xboole_0, C_107))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', C_107)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_543])).
% 11.67/4.24  tff(c_3393, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2')))=k4_xboole_0(k1_xboole_0, '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_111, c_3248])).
% 11.67/4.24  tff(c_3433, plain, (k4_xboole_0(k1_xboole_0, '#skF_1')=k4_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_342, c_3393])).
% 11.67/4.24  tff(c_3502, plain, (k4_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_1'))=k3_xboole_0(k1_xboole_0, '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3433, c_18])).
% 11.67/4.24  tff(c_555, plain, (k4_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_1'))=k3_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_497, c_18])).
% 11.67/4.24  tff(c_3576, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3502, c_555])).
% 11.67/4.24  tff(c_429, plain, (![A_52, B_53]: (k2_xboole_0(A_52, k4_xboole_0(A_52, B_53))=A_52)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_313])).
% 11.67/4.24  tff(c_14, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.67/4.24  tff(c_440, plain, (![B_53]: (k2_xboole_0(B_53, B_53)=B_53)), inference(superposition, [status(thm), theory('equality')], [c_429, c_14])).
% 11.67/4.24  tff(c_549, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_1'))=k2_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_497, c_14])).
% 11.67/4.24  tff(c_560, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_440, c_549])).
% 11.67/4.24  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.67/4.24  tff(c_74, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=B_27 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.67/4.24  tff(c_78, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_74])).
% 11.67/4.24  tff(c_1178, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_1'))=k4_xboole_0('#skF_1', '#skF_1') | k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_555, c_78])).
% 11.67/4.24  tff(c_1192, plain, (k4_xboole_0('#skF_1', '#skF_1')=k1_xboole_0 | k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_560, c_1178])).
% 11.67/4.24  tff(c_1587, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1192])).
% 11.67/4.24  tff(c_3640, plain, (k3_xboole_0(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3576, c_1587])).
% 11.67/4.24  tff(c_3499, plain, (k2_xboole_0(k3_xboole_0(k1_xboole_0, '#skF_1'), k4_xboole_0('#skF_1', '#skF_1'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3433, c_20])).
% 11.67/4.24  tff(c_130, plain, (![A_14, B_15]: (k2_xboole_0(k4_xboole_0(A_14, B_15), k3_xboole_0(A_14, B_15))=k2_xboole_0(A_14, k4_xboole_0(A_14, B_15)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_127])).
% 11.67/4.24  tff(c_698, plain, (![A_61, B_62]: (k2_xboole_0(k4_xboole_0(A_61, B_62), k3_xboole_0(A_61, B_62))=A_61)), inference(demodulation, [status(thm), theory('equality')], [c_342, c_130])).
% 11.67/4.24  tff(c_2285, plain, (![A_97, B_98]: (k4_xboole_0(k3_xboole_0(A_97, B_98), k3_xboole_0(A_97, B_98))=k4_xboole_0(A_97, A_97))), inference(superposition, [status(thm), theory('equality')], [c_698, c_166])).
% 11.67/4.24  tff(c_3978, plain, (![A_111, B_112]: (k2_xboole_0(k3_xboole_0(A_111, B_112), k4_xboole_0(A_111, A_111))=k3_xboole_0(A_111, B_112))), inference(superposition, [status(thm), theory('equality')], [c_2285, c_342])).
% 11.67/4.24  tff(c_4018, plain, (k2_xboole_0(k3_xboole_0(k1_xboole_0, '#skF_1'), k4_xboole_0(k1_xboole_0, k1_xboole_0))=k3_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3576, c_3978])).
% 11.67/4.24  tff(c_4080, plain, (k3_xboole_0(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3576, c_3499, c_497, c_4018])).
% 11.67/4.24  tff(c_4082, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3640, c_4080])).
% 11.67/4.24  tff(c_4083, plain, (k4_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1192])).
% 11.67/4.24  tff(c_428, plain, (![A_14, B_15]: (k2_xboole_0(k4_xboole_0(A_14, B_15), k3_xboole_0(A_14, B_15))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_342, c_130])).
% 11.67/4.24  tff(c_4101, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', '#skF_1'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_4083, c_428])).
% 11.67/4.24  tff(c_170, plain, (![A_38, B_39, B_15]: (k4_xboole_0(A_38, k2_xboole_0(B_39, k4_xboole_0(k4_xboole_0(A_38, B_39), B_15)))=k3_xboole_0(k4_xboole_0(A_38, B_39), B_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_135])).
% 11.67/4.24  tff(c_878, plain, (![A_68, B_69, B_70]: (k4_xboole_0(A_68, k2_xboole_0(B_69, k4_xboole_0(A_68, k2_xboole_0(B_69, B_70))))=k3_xboole_0(k4_xboole_0(A_68, B_69), B_70))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_170])).
% 11.67/4.24  tff(c_988, plain, (![A_47, B_70]: (k3_xboole_0(k4_xboole_0(A_47, A_47), B_70)=k4_xboole_0(A_47, A_47))), inference(superposition, [status(thm), theory('equality')], [c_342, c_878])).
% 11.67/4.24  tff(c_4095, plain, (![B_70]: (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0(k1_xboole_0, B_70))), inference(superposition, [status(thm), theory('equality')], [c_4083, c_988])).
% 11.67/4.24  tff(c_4131, plain, (![B_70]: (k3_xboole_0(k1_xboole_0, B_70)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4083, c_4095])).
% 11.67/4.24  tff(c_4128, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4083, c_18])).
% 11.67/4.24  tff(c_147, plain, (![C_40, A_38, B_39]: (k2_xboole_0(C_40, k4_xboole_0(A_38, k2_xboole_0(B_39, C_40)))=k2_xboole_0(C_40, k4_xboole_0(A_38, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_14])).
% 11.67/4.24  tff(c_972, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k2_xboole_0(B_39, k4_xboole_0(A_38, B_39)))=k3_xboole_0(k4_xboole_0(A_38, B_39), B_39))), inference(superposition, [status(thm), theory('equality')], [c_147, c_878])).
% 11.67/4.24  tff(c_5853, plain, (![A_131, B_132]: (k4_xboole_0(A_131, k2_xboole_0(B_132, A_131))=k3_xboole_0(k4_xboole_0(A_131, B_132), B_132))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_972])).
% 11.67/4.24  tff(c_4739, plain, (![A_120, B_121, C_122]: (k2_xboole_0(k3_xboole_0(k4_xboole_0(A_120, B_121), C_122), k4_xboole_0(A_120, k2_xboole_0(B_121, C_122)))=k4_xboole_0(A_120, B_121))), inference(superposition, [status(thm), theory('equality')], [c_135, c_20])).
% 11.67/4.24  tff(c_4787, plain, (![C_122]: (k2_xboole_0(k3_xboole_0(k1_xboole_0, C_122), k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', C_122)))=k4_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4083, c_4739])).
% 11.67/4.24  tff(c_4887, plain, (![C_122]: (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', C_122)))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4131, c_4083, c_4787])).
% 11.67/4.24  tff(c_4138, plain, (![A_113, B_114, C_115]: (k4_xboole_0(k4_xboole_0(A_113, B_114), k4_xboole_0(A_113, k2_xboole_0(B_114, C_115)))=k3_xboole_0(k4_xboole_0(A_113, B_114), C_115))), inference(superposition, [status(thm), theory('equality')], [c_135, c_18])).
% 11.67/4.24  tff(c_4189, plain, (![C_115]: (k4_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', C_115)))=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_1'), C_115))), inference(superposition, [status(thm), theory('equality')], [c_4083, c_4138])).
% 11.67/4.24  tff(c_5162, plain, (![C_125]: (k4_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', C_125)))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4083, c_988, c_4189])).
% 11.67/4.24  tff(c_5200, plain, (![C_125]: (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', C_125)))=k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', C_125)))), inference(superposition, [status(thm), theory('equality')], [c_5162, c_78])).
% 11.67/4.24  tff(c_5297, plain, (![C_126]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', C_126))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4887, c_5200])).
% 11.67/4.24  tff(c_5402, plain, (![B_2]: (k4_xboole_0('#skF_1', k2_xboole_0(B_2, '#skF_1'))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_5297])).
% 11.67/4.24  tff(c_6151, plain, (![B_133]: (k3_xboole_0(k4_xboole_0('#skF_1', B_133), B_133)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5853, c_5402])).
% 11.67/4.24  tff(c_6213, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_1'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_4128, c_6151])).
% 11.67/4.24  tff(c_754, plain, (![A_63, B_64, C_65]: (k2_xboole_0(A_63, k4_xboole_0(k3_xboole_0(A_63, B_64), C_65))=A_63)), inference(superposition, [status(thm), theory('equality')], [c_166, c_429])).
% 11.67/4.24  tff(c_806, plain, (![A_63, B_64, B_15]: (k2_xboole_0(A_63, k3_xboole_0(k3_xboole_0(A_63, B_64), B_15))=A_63)), inference(superposition, [status(thm), theory('equality')], [c_18, c_754])).
% 11.67/4.24  tff(c_6264, plain, (![B_15]: (k2_xboole_0(k3_xboole_0('#skF_1', '#skF_1'), k3_xboole_0(k1_xboole_0, B_15))=k3_xboole_0('#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6213, c_806])).
% 11.67/4.24  tff(c_6291, plain, (k3_xboole_0('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4101, c_2, c_4131, c_6264])).
% 11.67/4.24  tff(c_6464, plain, (k3_xboole_0('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6291, c_6213])).
% 11.67/4.24  tff(c_6471, plain, (k4_xboole_0('#skF_1', k1_xboole_0)='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6291, c_4128])).
% 11.67/4.24  tff(c_351, plain, (![A_49, B_50, C_51]: (k4_xboole_0(A_49, k2_xboole_0(k4_xboole_0(A_49, B_50), C_51))=k4_xboole_0(k3_xboole_0(A_49, B_50), C_51))), inference(superposition, [status(thm), theory('equality')], [c_18, c_135])).
% 11.67/4.24  tff(c_6629, plain, (![A_135, A_136, B_137]: (k4_xboole_0(A_135, k2_xboole_0(A_136, k4_xboole_0(A_135, B_137)))=k4_xboole_0(k3_xboole_0(A_135, B_137), A_136))), inference(superposition, [status(thm), theory('equality')], [c_2, c_351])).
% 11.67/4.24  tff(c_6742, plain, (![A_136]: (k4_xboole_0(k3_xboole_0('#skF_1', k1_xboole_0), A_136)=k4_xboole_0('#skF_1', k2_xboole_0(A_136, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_6471, c_6629])).
% 11.67/4.24  tff(c_6972, plain, (![A_139]: (k4_xboole_0(k1_xboole_0, A_139)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6464, c_5402, c_6742])).
% 11.67/4.24  tff(c_7160, plain, (![A_140]: (k2_xboole_0(k1_xboole_0, A_140)=A_140)), inference(superposition, [status(thm), theory('equality')], [c_6972, c_78])).
% 11.67/4.24  tff(c_7228, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_7160, c_111])).
% 11.67/4.24  tff(c_18790, plain, (![A_252, B_253, A_254]: (k4_xboole_0(k4_xboole_0(A_252, B_253), k4_xboole_0(A_252, k2_xboole_0(A_254, B_253)))=k3_xboole_0(k4_xboole_0(A_252, B_253), A_254))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4138])).
% 11.67/4.24  tff(c_19050, plain, (![A_254]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_1', k2_xboole_0(A_254, '#skF_2')))=k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), A_254))), inference(superposition, [status(thm), theory('equality')], [c_7228, c_18790])).
% 11.67/4.24  tff(c_19222, plain, (![A_254]: (k3_xboole_0('#skF_1', k2_xboole_0(A_254, '#skF_2'))=k3_xboole_0('#skF_1', A_254))), inference(demodulation, [status(thm), theory('equality')], [c_7228, c_18, c_19050])).
% 11.67/4.24  tff(c_22, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))!=k3_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.67/4.24  tff(c_25, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 11.67/4.24  tff(c_22568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19222, c_25])).
% 11.67/4.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.67/4.24  
% 11.67/4.24  Inference rules
% 11.67/4.24  ----------------------
% 11.67/4.24  #Ref     : 0
% 11.67/4.24  #Sup     : 5728
% 11.67/4.24  #Fact    : 0
% 11.67/4.24  #Define  : 0
% 11.67/4.24  #Split   : 2
% 11.67/4.24  #Chain   : 0
% 11.67/4.24  #Close   : 0
% 11.67/4.24  
% 11.67/4.24  Ordering : KBO
% 11.67/4.24  
% 11.67/4.24  Simplification rules
% 11.67/4.24  ----------------------
% 11.67/4.24  #Subsume      : 151
% 11.67/4.24  #Demod        : 6722
% 11.67/4.24  #Tautology    : 3031
% 11.67/4.24  #SimpNegUnit  : 21
% 11.67/4.24  #BackRed      : 46
% 11.67/4.24  
% 11.67/4.24  #Partial instantiations: 0
% 11.67/4.24  #Strategies tried      : 1
% 11.67/4.24  
% 11.67/4.24  Timing (in seconds)
% 11.67/4.24  ----------------------
% 11.67/4.24  Preprocessing        : 0.25
% 11.67/4.24  Parsing              : 0.14
% 11.67/4.24  CNF conversion       : 0.02
% 11.67/4.24  Main loop            : 3.15
% 11.67/4.24  Inferencing          : 0.67
% 11.67/4.24  Reduction            : 1.79
% 11.67/4.24  Demodulation         : 1.58
% 11.67/4.24  BG Simplification    : 0.11
% 11.67/4.24  Subsumption          : 0.41
% 11.67/4.24  Abstraction          : 0.16
% 11.67/4.24  MUC search           : 0.00
% 11.67/4.24  Cooper               : 0.00
% 11.67/4.24  Total                : 3.45
% 11.67/4.24  Index Insertion      : 0.00
% 11.67/4.24  Index Deletion       : 0.00
% 11.67/4.24  Index Matching       : 0.00
% 11.67/4.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
