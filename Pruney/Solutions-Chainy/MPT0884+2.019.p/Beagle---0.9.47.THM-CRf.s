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
% DateTime   : Thu Dec  3 10:09:34 EST 2020

% Result     : Theorem 16.31s
% Output     : CNFRefutation 16.48s
% Verified   : 
% Statistics : Number of formulae       :   67 (  95 expanded)
%              Number of leaves         :   31 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   48 (  76 expanded)
%              Number of equality atoms :   47 (  75 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_zfmisc_1(k2_tarski(A,B),k1_tarski(C),k2_tarski(D,E)) = k2_enumset1(k3_mcart_1(A,C,D),k3_mcart_1(B,C,D),k3_mcart_1(A,C,E),k3_mcart_1(B,C,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).

tff(c_6,plain,(
    ! [A_7,B_8] : k2_xboole_0(k1_tarski(A_7),k1_tarski(B_8)) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_334,plain,(
    ! [A_80,B_81,C_82] : k2_xboole_0(k1_tarski(A_80),k2_tarski(B_81,C_82)) = k1_enumset1(A_80,B_81,C_82) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_361,plain,(
    ! [A_80,A_33] : k2_xboole_0(k1_tarski(A_80),k1_tarski(A_33)) = k1_enumset1(A_80,A_33,A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_334])).

tff(c_364,plain,(
    ! [A_80,A_33] : k1_enumset1(A_80,A_33,A_33) = k2_tarski(A_80,A_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_361])).

tff(c_24,plain,(
    ! [A_36,B_37,C_38] : k2_enumset1(A_36,A_36,B_37,C_38) = k1_enumset1(A_36,B_37,C_38) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1472,plain,(
    ! [A_130,C_131,D_132,B_133] : k2_enumset1(k4_tarski(A_130,C_131),k4_tarski(A_130,D_132),k4_tarski(B_133,C_131),k4_tarski(B_133,D_132)) = k2_zfmisc_1(k2_tarski(A_130,B_133),k2_tarski(C_131,D_132)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1489,plain,(
    ! [A_130,C_131,B_133] : k1_enumset1(k4_tarski(A_130,C_131),k4_tarski(B_133,C_131),k4_tarski(B_133,C_131)) = k2_zfmisc_1(k2_tarski(A_130,B_133),k2_tarski(C_131,C_131)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1472])).

tff(c_15314,plain,(
    ! [A_322,B_323,C_324] : k2_zfmisc_1(k2_tarski(A_322,B_323),k1_tarski(C_324)) = k2_tarski(k4_tarski(A_322,C_324),k4_tarski(B_323,C_324)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_20,c_1489])).

tff(c_32,plain,(
    ! [A_48,B_49,C_50] : k2_zfmisc_1(k2_zfmisc_1(A_48,B_49),C_50) = k3_zfmisc_1(A_48,B_49,C_50) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_15374,plain,(
    ! [A_322,C_324,B_323,C_50] : k2_zfmisc_1(k2_tarski(k4_tarski(A_322,C_324),k4_tarski(B_323,C_324)),C_50) = k3_zfmisc_1(k2_tarski(A_322,B_323),k1_tarski(C_324),C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_15314,c_32])).

tff(c_30,plain,(
    ! [A_45,B_46,C_47] : k4_tarski(k4_tarski(A_45,B_46),C_47) = k3_mcart_1(A_45,B_46,C_47) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1498,plain,(
    ! [A_130,C_47,A_45,D_132,B_46] : k2_enumset1(k4_tarski(A_130,C_47),k4_tarski(A_130,D_132),k3_mcart_1(A_45,B_46,C_47),k4_tarski(k4_tarski(A_45,B_46),D_132)) = k2_zfmisc_1(k2_tarski(A_130,k4_tarski(A_45,B_46)),k2_tarski(C_47,D_132)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1472])).

tff(c_27585,plain,(
    ! [B_397,A_396,D_400,A_398,C_399] : k2_enumset1(k4_tarski(A_396,C_399),k4_tarski(A_396,D_400),k3_mcart_1(A_398,B_397,C_399),k3_mcart_1(A_398,B_397,D_400)) = k2_zfmisc_1(k2_tarski(A_396,k4_tarski(A_398,B_397)),k2_tarski(C_399,D_400)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1498])).

tff(c_27853,plain,(
    ! [B_397,C_47,A_45,B_46,A_398,C_399] : k2_enumset1(k4_tarski(k4_tarski(A_45,B_46),C_399),k3_mcart_1(A_45,B_46,C_47),k3_mcart_1(A_398,B_397,C_399),k3_mcart_1(A_398,B_397,C_47)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_45,B_46),k4_tarski(A_398,B_397)),k2_tarski(C_399,C_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_27585])).

tff(c_27887,plain,(
    ! [B_397,C_47,A_45,B_46,A_398,C_399] : k2_enumset1(k3_mcart_1(A_45,B_46,C_399),k3_mcart_1(A_45,B_46,C_47),k3_mcart_1(A_398,B_397,C_399),k3_mcart_1(A_398,B_397,C_47)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_45,B_46),k4_tarski(A_398,B_397)),k2_tarski(C_399,C_47)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_27853])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_384,plain,(
    ! [B_85,C_86,A_87] : k2_xboole_0(k2_tarski(B_85,C_86),k1_tarski(A_87)) = k1_enumset1(A_87,B_85,C_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_334])).

tff(c_10,plain,(
    ! [A_12,B_13,C_14] : k2_xboole_0(k2_tarski(A_12,B_13),k1_tarski(C_14)) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_390,plain,(
    ! [B_85,C_86,A_87] : k1_enumset1(B_85,C_86,A_87) = k1_enumset1(A_87,B_85,C_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_10])).

tff(c_818,plain,(
    ! [A_107,B_108,C_109,D_110] : k2_xboole_0(k1_enumset1(A_107,B_108,C_109),k1_tarski(D_110)) = k2_enumset1(A_107,B_108,C_109,D_110) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18781,plain,(
    ! [B_351,C_352,A_353,D_354] : k2_xboole_0(k1_enumset1(B_351,C_352,A_353),k1_tarski(D_354)) = k2_enumset1(A_353,B_351,C_352,D_354) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_818])).

tff(c_14,plain,(
    ! [A_19,B_20,C_21,D_22] : k2_xboole_0(k1_enumset1(A_19,B_20,C_21),k1_tarski(D_22)) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18876,plain,(
    ! [B_355,C_356,A_357,D_358] : k2_enumset1(B_355,C_356,A_357,D_358) = k2_enumset1(A_357,B_355,C_356,D_358) ),
    inference(superposition,[status(thm),theory(equality)],[c_18781,c_14])).

tff(c_630,plain,(
    ! [A_99,B_100,C_101,D_102] : k2_xboole_0(k1_tarski(A_99),k1_enumset1(B_100,C_101,D_102)) = k2_enumset1(A_99,B_100,C_101,D_102) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4655,plain,(
    ! [B_224,C_225,D_226,A_227] : k2_xboole_0(k1_enumset1(B_224,C_225,D_226),k1_tarski(A_227)) = k2_enumset1(A_227,B_224,C_225,D_226) ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_2])).

tff(c_4661,plain,(
    ! [B_224,C_225,D_226,A_227] : k2_enumset1(B_224,C_225,D_226,A_227) = k2_enumset1(A_227,B_224,C_225,D_226) ),
    inference(superposition,[status(thm),theory(equality)],[c_4655,c_14])).

tff(c_19136,plain,(
    ! [B_355,C_356,D_358,A_357] : k2_enumset1(B_355,C_356,D_358,A_357) = k2_enumset1(B_355,C_356,A_357,D_358) ),
    inference(superposition,[status(thm),theory(equality)],[c_18876,c_4661])).

tff(c_23102,plain,(
    ! [A_376,A_377,B_378,C_379] : k2_xboole_0(k1_tarski(A_376),k1_enumset1(A_377,B_378,C_379)) = k2_enumset1(A_376,B_378,C_379,A_377) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_630])).

tff(c_12,plain,(
    ! [A_15,B_16,C_17,D_18] : k2_xboole_0(k1_tarski(A_15),k1_enumset1(B_16,C_17,D_18)) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_23111,plain,(
    ! [A_376,B_378,C_379,A_377] : k2_enumset1(A_376,B_378,C_379,A_377) = k2_enumset1(A_376,A_377,B_378,C_379) ),
    inference(superposition,[status(thm),theory(equality)],[c_23102,c_12])).

tff(c_34,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_23188,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_4')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23111,c_34])).

tff(c_30146,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19136,c_23188])).

tff(c_52723,plain,(
    k2_zfmisc_1(k2_tarski(k4_tarski('#skF_1','#skF_3'),k4_tarski('#skF_2','#skF_3')),k2_tarski('#skF_4','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27887,c_30146])).

tff(c_52726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15374,c_52723])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:30:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.31/8.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.31/8.05  
% 16.31/8.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.31/8.05  %$ k3_enumset1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 16.31/8.05  
% 16.31/8.05  %Foreground sorts:
% 16.31/8.05  
% 16.31/8.05  
% 16.31/8.05  %Background operators:
% 16.31/8.05  
% 16.31/8.05  
% 16.31/8.05  %Foreground operators:
% 16.31/8.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.31/8.05  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.31/8.05  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 16.31/8.05  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 16.31/8.05  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 16.31/8.05  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.31/8.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.31/8.05  tff('#skF_5', type, '#skF_5': $i).
% 16.31/8.05  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.31/8.05  tff('#skF_2', type, '#skF_2': $i).
% 16.31/8.05  tff('#skF_3', type, '#skF_3': $i).
% 16.31/8.05  tff('#skF_1', type, '#skF_1': $i).
% 16.31/8.05  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 16.31/8.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.31/8.05  tff(k3_tarski, type, k3_tarski: $i > $i).
% 16.31/8.05  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.31/8.05  tff('#skF_4', type, '#skF_4': $i).
% 16.31/8.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.31/8.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.31/8.05  
% 16.48/8.07  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 16.48/8.07  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 16.48/8.07  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 16.48/8.07  tff(f_49, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 16.48/8.07  tff(f_53, axiom, (![A, B, C, D]: (k2_zfmisc_1(k2_tarski(A, B), k2_tarski(C, D)) = k2_enumset1(k4_tarski(A, C), k4_tarski(A, D), k4_tarski(B, C), k4_tarski(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 16.48/8.07  tff(f_57, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 16.48/8.07  tff(f_55, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 16.48/8.07  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 16.48/8.07  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 16.48/8.07  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 16.48/8.07  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 16.48/8.07  tff(f_60, negated_conjecture, ~(![A, B, C, D, E]: (k3_zfmisc_1(k2_tarski(A, B), k1_tarski(C), k2_tarski(D, E)) = k2_enumset1(k3_mcart_1(A, C, D), k3_mcart_1(B, C, D), k3_mcart_1(A, C, E), k3_mcart_1(B, C, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_mcart_1)).
% 16.48/8.07  tff(c_6, plain, (![A_7, B_8]: (k2_xboole_0(k1_tarski(A_7), k1_tarski(B_8))=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.48/8.07  tff(c_20, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_45])).
% 16.48/8.07  tff(c_334, plain, (![A_80, B_81, C_82]: (k2_xboole_0(k1_tarski(A_80), k2_tarski(B_81, C_82))=k1_enumset1(A_80, B_81, C_82))), inference(cnfTransformation, [status(thm)], [f_33])).
% 16.48/8.07  tff(c_361, plain, (![A_80, A_33]: (k2_xboole_0(k1_tarski(A_80), k1_tarski(A_33))=k1_enumset1(A_80, A_33, A_33))), inference(superposition, [status(thm), theory('equality')], [c_20, c_334])).
% 16.48/8.07  tff(c_364, plain, (![A_80, A_33]: (k1_enumset1(A_80, A_33, A_33)=k2_tarski(A_80, A_33))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_361])).
% 16.48/8.07  tff(c_24, plain, (![A_36, B_37, C_38]: (k2_enumset1(A_36, A_36, B_37, C_38)=k1_enumset1(A_36, B_37, C_38))), inference(cnfTransformation, [status(thm)], [f_49])).
% 16.48/8.07  tff(c_1472, plain, (![A_130, C_131, D_132, B_133]: (k2_enumset1(k4_tarski(A_130, C_131), k4_tarski(A_130, D_132), k4_tarski(B_133, C_131), k4_tarski(B_133, D_132))=k2_zfmisc_1(k2_tarski(A_130, B_133), k2_tarski(C_131, D_132)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 16.48/8.07  tff(c_1489, plain, (![A_130, C_131, B_133]: (k1_enumset1(k4_tarski(A_130, C_131), k4_tarski(B_133, C_131), k4_tarski(B_133, C_131))=k2_zfmisc_1(k2_tarski(A_130, B_133), k2_tarski(C_131, C_131)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1472])).
% 16.48/8.07  tff(c_15314, plain, (![A_322, B_323, C_324]: (k2_zfmisc_1(k2_tarski(A_322, B_323), k1_tarski(C_324))=k2_tarski(k4_tarski(A_322, C_324), k4_tarski(B_323, C_324)))), inference(demodulation, [status(thm), theory('equality')], [c_364, c_20, c_1489])).
% 16.48/8.07  tff(c_32, plain, (![A_48, B_49, C_50]: (k2_zfmisc_1(k2_zfmisc_1(A_48, B_49), C_50)=k3_zfmisc_1(A_48, B_49, C_50))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.48/8.07  tff(c_15374, plain, (![A_322, C_324, B_323, C_50]: (k2_zfmisc_1(k2_tarski(k4_tarski(A_322, C_324), k4_tarski(B_323, C_324)), C_50)=k3_zfmisc_1(k2_tarski(A_322, B_323), k1_tarski(C_324), C_50))), inference(superposition, [status(thm), theory('equality')], [c_15314, c_32])).
% 16.48/8.07  tff(c_30, plain, (![A_45, B_46, C_47]: (k4_tarski(k4_tarski(A_45, B_46), C_47)=k3_mcart_1(A_45, B_46, C_47))), inference(cnfTransformation, [status(thm)], [f_55])).
% 16.48/8.07  tff(c_1498, plain, (![A_130, C_47, A_45, D_132, B_46]: (k2_enumset1(k4_tarski(A_130, C_47), k4_tarski(A_130, D_132), k3_mcart_1(A_45, B_46, C_47), k4_tarski(k4_tarski(A_45, B_46), D_132))=k2_zfmisc_1(k2_tarski(A_130, k4_tarski(A_45, B_46)), k2_tarski(C_47, D_132)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1472])).
% 16.48/8.07  tff(c_27585, plain, (![B_397, A_396, D_400, A_398, C_399]: (k2_enumset1(k4_tarski(A_396, C_399), k4_tarski(A_396, D_400), k3_mcart_1(A_398, B_397, C_399), k3_mcart_1(A_398, B_397, D_400))=k2_zfmisc_1(k2_tarski(A_396, k4_tarski(A_398, B_397)), k2_tarski(C_399, D_400)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1498])).
% 16.48/8.07  tff(c_27853, plain, (![B_397, C_47, A_45, B_46, A_398, C_399]: (k2_enumset1(k4_tarski(k4_tarski(A_45, B_46), C_399), k3_mcart_1(A_45, B_46, C_47), k3_mcart_1(A_398, B_397, C_399), k3_mcart_1(A_398, B_397, C_47))=k2_zfmisc_1(k2_tarski(k4_tarski(A_45, B_46), k4_tarski(A_398, B_397)), k2_tarski(C_399, C_47)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_27585])).
% 16.48/8.07  tff(c_27887, plain, (![B_397, C_47, A_45, B_46, A_398, C_399]: (k2_enumset1(k3_mcart_1(A_45, B_46, C_399), k3_mcart_1(A_45, B_46, C_47), k3_mcart_1(A_398, B_397, C_399), k3_mcart_1(A_398, B_397, C_47))=k2_zfmisc_1(k2_tarski(k4_tarski(A_45, B_46), k4_tarski(A_398, B_397)), k2_tarski(C_399, C_47)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_27853])).
% 16.48/8.07  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.48/8.07  tff(c_384, plain, (![B_85, C_86, A_87]: (k2_xboole_0(k2_tarski(B_85, C_86), k1_tarski(A_87))=k1_enumset1(A_87, B_85, C_86))), inference(superposition, [status(thm), theory('equality')], [c_2, c_334])).
% 16.48/8.07  tff(c_10, plain, (![A_12, B_13, C_14]: (k2_xboole_0(k2_tarski(A_12, B_13), k1_tarski(C_14))=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.48/8.07  tff(c_390, plain, (![B_85, C_86, A_87]: (k1_enumset1(B_85, C_86, A_87)=k1_enumset1(A_87, B_85, C_86))), inference(superposition, [status(thm), theory('equality')], [c_384, c_10])).
% 16.48/8.07  tff(c_818, plain, (![A_107, B_108, C_109, D_110]: (k2_xboole_0(k1_enumset1(A_107, B_108, C_109), k1_tarski(D_110))=k2_enumset1(A_107, B_108, C_109, D_110))), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.48/8.07  tff(c_18781, plain, (![B_351, C_352, A_353, D_354]: (k2_xboole_0(k1_enumset1(B_351, C_352, A_353), k1_tarski(D_354))=k2_enumset1(A_353, B_351, C_352, D_354))), inference(superposition, [status(thm), theory('equality')], [c_390, c_818])).
% 16.48/8.07  tff(c_14, plain, (![A_19, B_20, C_21, D_22]: (k2_xboole_0(k1_enumset1(A_19, B_20, C_21), k1_tarski(D_22))=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.48/8.07  tff(c_18876, plain, (![B_355, C_356, A_357, D_358]: (k2_enumset1(B_355, C_356, A_357, D_358)=k2_enumset1(A_357, B_355, C_356, D_358))), inference(superposition, [status(thm), theory('equality')], [c_18781, c_14])).
% 16.48/8.07  tff(c_630, plain, (![A_99, B_100, C_101, D_102]: (k2_xboole_0(k1_tarski(A_99), k1_enumset1(B_100, C_101, D_102))=k2_enumset1(A_99, B_100, C_101, D_102))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.48/8.07  tff(c_4655, plain, (![B_224, C_225, D_226, A_227]: (k2_xboole_0(k1_enumset1(B_224, C_225, D_226), k1_tarski(A_227))=k2_enumset1(A_227, B_224, C_225, D_226))), inference(superposition, [status(thm), theory('equality')], [c_630, c_2])).
% 16.48/8.07  tff(c_4661, plain, (![B_224, C_225, D_226, A_227]: (k2_enumset1(B_224, C_225, D_226, A_227)=k2_enumset1(A_227, B_224, C_225, D_226))), inference(superposition, [status(thm), theory('equality')], [c_4655, c_14])).
% 16.48/8.07  tff(c_19136, plain, (![B_355, C_356, D_358, A_357]: (k2_enumset1(B_355, C_356, D_358, A_357)=k2_enumset1(B_355, C_356, A_357, D_358))), inference(superposition, [status(thm), theory('equality')], [c_18876, c_4661])).
% 16.48/8.07  tff(c_23102, plain, (![A_376, A_377, B_378, C_379]: (k2_xboole_0(k1_tarski(A_376), k1_enumset1(A_377, B_378, C_379))=k2_enumset1(A_376, B_378, C_379, A_377))), inference(superposition, [status(thm), theory('equality')], [c_390, c_630])).
% 16.48/8.07  tff(c_12, plain, (![A_15, B_16, C_17, D_18]: (k2_xboole_0(k1_tarski(A_15), k1_enumset1(B_16, C_17, D_18))=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.48/8.07  tff(c_23111, plain, (![A_376, B_378, C_379, A_377]: (k2_enumset1(A_376, B_378, C_379, A_377)=k2_enumset1(A_376, A_377, B_378, C_379))), inference(superposition, [status(thm), theory('equality')], [c_23102, c_12])).
% 16.48/8.07  tff(c_34, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.48/8.07  tff(c_23188, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_23111, c_34])).
% 16.48/8.07  tff(c_30146, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'), k3_mcart_1('#skF_2', '#skF_3', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_19136, c_23188])).
% 16.48/8.07  tff(c_52723, plain, (k2_zfmisc_1(k2_tarski(k4_tarski('#skF_1', '#skF_3'), k4_tarski('#skF_2', '#skF_3')), k2_tarski('#skF_4', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_27887, c_30146])).
% 16.48/8.07  tff(c_52726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15374, c_52723])).
% 16.48/8.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.48/8.07  
% 16.48/8.07  Inference rules
% 16.48/8.07  ----------------------
% 16.48/8.07  #Ref     : 0
% 16.48/8.07  #Sup     : 12241
% 16.48/8.07  #Fact    : 0
% 16.48/8.07  #Define  : 0
% 16.48/8.07  #Split   : 0
% 16.48/8.07  #Chain   : 0
% 16.48/8.07  #Close   : 0
% 16.48/8.07  
% 16.48/8.07  Ordering : KBO
% 16.48/8.07  
% 16.48/8.07  Simplification rules
% 16.48/8.07  ----------------------
% 16.48/8.07  #Subsume      : 3276
% 16.48/8.07  #Demod        : 13951
% 16.48/8.07  #Tautology    : 6987
% 16.48/8.07  #SimpNegUnit  : 0
% 16.48/8.07  #BackRed      : 3
% 16.48/8.07  
% 16.48/8.07  #Partial instantiations: 0
% 16.48/8.07  #Strategies tried      : 1
% 16.48/8.07  
% 16.48/8.07  Timing (in seconds)
% 16.48/8.07  ----------------------
% 16.48/8.07  Preprocessing        : 0.33
% 16.48/8.07  Parsing              : 0.17
% 16.48/8.07  CNF conversion       : 0.02
% 16.48/8.07  Main loop            : 6.96
% 16.48/8.07  Inferencing          : 1.38
% 16.48/8.07  Reduction            : 4.48
% 16.48/8.07  Demodulation         : 4.18
% 16.48/8.07  BG Simplification    : 0.12
% 16.48/8.07  Subsumption          : 0.81
% 16.48/8.07  Abstraction          : 0.29
% 16.48/8.07  MUC search           : 0.00
% 16.48/8.07  Cooper               : 0.00
% 16.48/8.07  Total                : 7.32
% 16.48/8.07  Index Insertion      : 0.00
% 16.48/8.07  Index Deletion       : 0.00
% 16.48/8.07  Index Matching       : 0.00
% 16.48/8.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
