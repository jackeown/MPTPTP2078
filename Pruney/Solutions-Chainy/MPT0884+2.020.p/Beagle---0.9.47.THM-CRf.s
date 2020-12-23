%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:34 EST 2020

% Result     : Theorem 11.73s
% Output     : CNFRefutation 11.86s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 200 expanded)
%              Number of leaves         :   32 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :   62 ( 181 expanded)
%              Number of equality atoms :   61 ( 180 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k2_tarski(A,B),k2_tarski(C,D)) = k2_enumset1(k4_tarski(A,C),k4_tarski(A,D),k4_tarski(B,C),k4_tarski(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_zfmisc_1(k2_tarski(A,B),k1_tarski(C),k2_tarski(D,E)) = k2_enumset1(k3_mcart_1(A,C,D),k3_mcart_1(B,C,D),k3_mcart_1(A,C,E),k3_mcart_1(B,C,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).

tff(c_16,plain,(
    ! [A_26,B_27] : k1_enumset1(A_26,A_26,B_27) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k2_tarski(A_13,B_14),k1_tarski(C_15)) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_25] : k2_tarski(A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_220,plain,(
    ! [A_70,B_71,C_72,D_73] : k2_xboole_0(k2_tarski(A_70,B_71),k2_tarski(C_72,D_73)) = k2_enumset1(A_70,B_71,C_72,D_73) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_247,plain,(
    ! [A_70,B_71,A_25] : k2_xboole_0(k2_tarski(A_70,B_71),k1_tarski(A_25)) = k2_enumset1(A_70,B_71,A_25,A_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_220])).

tff(c_309,plain,(
    ! [A_83,B_84,A_85] : k2_enumset1(A_83,B_84,A_85,A_85) = k1_enumset1(A_83,B_84,A_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_247])).

tff(c_18,plain,(
    ! [A_28,B_29,C_30] : k2_enumset1(A_28,A_28,B_29,C_30) = k1_enumset1(A_28,B_29,C_30) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_320,plain,(
    ! [B_84,A_85] : k1_enumset1(B_84,B_84,A_85) = k1_enumset1(B_84,A_85,A_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_18])).

tff(c_371,plain,(
    ! [B_88,A_89] : k1_enumset1(B_88,A_89,A_89) = k2_tarski(B_88,A_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_320])).

tff(c_6,plain,(
    ! [B_11,A_10,C_12] : k2_xboole_0(k2_tarski(B_11,A_10),k2_tarski(C_12,A_10)) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_252,plain,(
    ! [A_74,D_75,C_76] : k2_enumset1(A_74,D_75,C_76,D_75) = k1_enumset1(D_75,A_74,C_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_6])).

tff(c_259,plain,(
    ! [D_75,C_76] : k1_enumset1(D_75,D_75,C_76) = k1_enumset1(D_75,C_76,D_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_18])).

tff(c_268,plain,(
    ! [D_75,C_76] : k1_enumset1(D_75,C_76,D_75) = k2_tarski(D_75,C_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_259])).

tff(c_227,plain,(
    ! [A_70,D_73,C_72] : k2_enumset1(A_70,D_73,C_72,D_73) = k1_enumset1(D_73,A_70,C_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_6])).

tff(c_316,plain,(
    ! [A_85,A_83] : k1_enumset1(A_85,A_83,A_85) = k1_enumset1(A_83,A_85,A_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_227])).

tff(c_333,plain,(
    ! [A_83,A_85] : k1_enumset1(A_83,A_85,A_85) = k2_tarski(A_85,A_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_316])).

tff(c_377,plain,(
    ! [B_88,A_89] : k2_tarski(B_88,A_89) = k2_tarski(A_89,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_333])).

tff(c_750,plain,(
    ! [A_108,C_109,D_110,B_111] : k2_enumset1(k4_tarski(A_108,C_109),k4_tarski(A_108,D_110),k4_tarski(B_111,C_109),k4_tarski(B_111,D_110)) = k2_zfmisc_1(k2_tarski(A_108,B_111),k2_tarski(C_109,D_110)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_765,plain,(
    ! [A_108,D_110,B_111] : k1_enumset1(k4_tarski(A_108,D_110),k4_tarski(B_111,D_110),k4_tarski(B_111,D_110)) = k2_zfmisc_1(k2_tarski(A_108,B_111),k2_tarski(D_110,D_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_18])).

tff(c_5201,plain,(
    ! [A_250,B_251,D_252] : k2_zfmisc_1(k2_tarski(A_250,B_251),k1_tarski(D_252)) = k2_tarski(k4_tarski(B_251,D_252),k4_tarski(A_250,D_252)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_14,c_765])).

tff(c_26,plain,(
    ! [A_40,B_41,C_42] : k2_zfmisc_1(k2_zfmisc_1(A_40,B_41),C_42) = k3_zfmisc_1(A_40,B_41,C_42) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5297,plain,(
    ! [B_251,D_252,A_250,C_42] : k2_zfmisc_1(k2_tarski(k4_tarski(B_251,D_252),k4_tarski(A_250,D_252)),C_42) = k3_zfmisc_1(k2_tarski(A_250,B_251),k1_tarski(D_252),C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_5201,c_26])).

tff(c_24,plain,(
    ! [A_37,B_38,C_39] : k4_tarski(k4_tarski(A_37,B_38),C_39) = k3_mcart_1(A_37,B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_779,plain,(
    ! [B_111,C_39,B_38,A_37,D_110] : k2_enumset1(k3_mcart_1(A_37,B_38,C_39),k4_tarski(k4_tarski(A_37,B_38),D_110),k4_tarski(B_111,C_39),k4_tarski(B_111,D_110)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_37,B_38),B_111),k2_tarski(C_39,D_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_750])).

tff(c_3535,plain,(
    ! [B_219,D_220,A_218,B_222,C_221] : k2_enumset1(k3_mcart_1(A_218,B_219,C_221),k3_mcart_1(A_218,B_219,D_220),k4_tarski(B_222,C_221),k4_tarski(B_222,D_220)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_218,B_219),B_222),k2_tarski(C_221,D_220)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_779])).

tff(c_3574,plain,(
    ! [C_39,B_219,B_38,D_220,A_218,A_37] : k2_enumset1(k3_mcart_1(A_218,B_219,C_39),k3_mcart_1(A_218,B_219,D_220),k3_mcart_1(A_37,B_38,C_39),k4_tarski(k4_tarski(A_37,B_38),D_220)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_218,B_219),k4_tarski(A_37,B_38)),k2_tarski(C_39,D_220)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3535])).

tff(c_3589,plain,(
    ! [C_39,B_219,B_38,D_220,A_218,A_37] : k2_enumset1(k3_mcart_1(A_218,B_219,C_39),k3_mcart_1(A_218,B_219,D_220),k3_mcart_1(A_37,B_38,C_39),k3_mcart_1(A_37,B_38,D_220)) = k2_zfmisc_1(k2_tarski(k4_tarski(A_218,B_219),k4_tarski(A_37,B_38)),k2_tarski(C_39,D_220)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3574])).

tff(c_338,plain,(
    ! [A_86,A_87] : k1_enumset1(A_86,A_87,A_87) = k2_tarski(A_87,A_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_316])).

tff(c_10,plain,(
    ! [A_16,B_17,C_18,D_19] : k2_xboole_0(k1_enumset1(A_16,B_17,C_18),k1_tarski(D_19)) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_344,plain,(
    ! [A_87,A_86,D_19] : k2_xboole_0(k2_tarski(A_87,A_86),k1_tarski(D_19)) = k2_enumset1(A_86,A_87,A_87,D_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_10])).

tff(c_1010,plain,(
    ! [A_124,A_125,D_126] : k2_enumset1(A_124,A_125,A_125,D_126) = k1_enumset1(A_125,A_124,D_126) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_344])).

tff(c_380,plain,(
    ! [B_88,A_89,D_19] : k2_xboole_0(k2_tarski(B_88,A_89),k1_tarski(D_19)) = k2_enumset1(B_88,A_89,A_89,D_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_10])).

tff(c_404,plain,(
    ! [B_88,A_89,D_19] : k2_enumset1(B_88,A_89,A_89,D_19) = k1_enumset1(B_88,A_89,D_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_380])).

tff(c_1020,plain,(
    ! [A_125,A_124,D_126] : k1_enumset1(A_125,A_124,D_126) = k1_enumset1(A_124,A_125,D_126) ),
    inference(superposition,[status(thm),theory(equality)],[c_1010,c_404])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_xboole_0(k2_tarski(A_1,B_2),k2_tarski(C_3,D_4)) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_485,plain,(
    ! [D_92,A_95,C_94,E_96,B_93] : k2_xboole_0(k1_enumset1(A_95,B_93,C_94),k2_tarski(D_92,E_96)) = k3_enumset1(A_95,B_93,C_94,D_92,E_96) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_509,plain,(
    ! [A_26,B_27,D_92,E_96] : k3_enumset1(A_26,A_26,B_27,D_92,E_96) = k2_xboole_0(k2_tarski(A_26,B_27),k2_tarski(D_92,E_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_485])).

tff(c_518,plain,(
    ! [A_26,B_27,D_92,E_96] : k3_enumset1(A_26,A_26,B_27,D_92,E_96) = k2_enumset1(A_26,B_27,D_92,E_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_509])).

tff(c_522,plain,(
    ! [B_98,E_100,D_99,A_101,C_97] : k2_xboole_0(k2_tarski(A_101,B_98),k1_enumset1(C_97,D_99,E_100)) = k3_enumset1(A_101,B_98,C_97,D_99,E_100) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_549,plain,(
    ! [A_25,C_97,D_99,E_100] : k3_enumset1(A_25,A_25,C_97,D_99,E_100) = k2_xboole_0(k1_tarski(A_25),k1_enumset1(C_97,D_99,E_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_522])).

tff(c_2966,plain,(
    ! [A_203,C_204,D_205,E_206] : k2_xboole_0(k1_tarski(A_203),k1_enumset1(C_204,D_205,E_206)) = k2_enumset1(A_203,C_204,D_205,E_206) ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_549])).

tff(c_10520,plain,(
    ! [A_358,A_359,A_360,D_361] : k2_xboole_0(k1_tarski(A_358),k1_enumset1(A_359,A_360,D_361)) = k2_enumset1(A_358,A_360,A_359,D_361) ),
    inference(superposition,[status(thm),theory(equality)],[c_1020,c_2966])).

tff(c_2965,plain,(
    ! [A_25,C_97,D_99,E_100] : k2_xboole_0(k1_tarski(A_25),k1_enumset1(C_97,D_99,E_100)) = k2_enumset1(A_25,C_97,D_99,E_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_549])).

tff(c_10526,plain,(
    ! [A_358,A_360,A_359,D_361] : k2_enumset1(A_358,A_360,A_359,D_361) = k2_enumset1(A_358,A_359,A_360,D_361) ),
    inference(superposition,[status(thm),theory(equality)],[c_10520,c_2965])).

tff(c_28,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10601,plain,(
    k2_enumset1(k3_mcart_1('#skF_1','#skF_3','#skF_4'),k3_mcart_1('#skF_1','#skF_3','#skF_5'),k3_mcart_1('#skF_2','#skF_3','#skF_4'),k3_mcart_1('#skF_2','#skF_3','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10526,c_28])).

tff(c_13304,plain,(
    k2_zfmisc_1(k2_tarski(k4_tarski('#skF_1','#skF_3'),k4_tarski('#skF_2','#skF_3')),k2_tarski('#skF_4','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3589,c_10601])).

tff(c_26264,plain,(
    k3_zfmisc_1(k2_tarski('#skF_2','#skF_1'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) != k3_zfmisc_1(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5297,c_13304])).

tff(c_26267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_26264])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:45:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.73/4.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.73/4.53  
% 11.73/4.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.73/4.54  %$ k3_enumset1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.73/4.54  
% 11.73/4.54  %Foreground sorts:
% 11.73/4.54  
% 11.73/4.54  
% 11.73/4.54  %Background operators:
% 11.73/4.54  
% 11.73/4.54  
% 11.73/4.54  %Foreground operators:
% 11.73/4.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.73/4.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.73/4.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.73/4.54  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 11.73/4.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.73/4.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.73/4.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.73/4.54  tff('#skF_5', type, '#skF_5': $i).
% 11.73/4.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.73/4.54  tff('#skF_2', type, '#skF_2': $i).
% 11.73/4.54  tff('#skF_3', type, '#skF_3': $i).
% 11.73/4.54  tff('#skF_1', type, '#skF_1': $i).
% 11.73/4.54  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 11.73/4.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.73/4.54  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.73/4.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.73/4.54  tff('#skF_4', type, '#skF_4': $i).
% 11.73/4.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.73/4.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.73/4.54  
% 11.86/4.55  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 11.86/4.55  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 11.86/4.55  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 11.86/4.55  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 11.86/4.55  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 11.86/4.55  tff(f_31, axiom, (![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 11.86/4.55  tff(f_47, axiom, (![A, B, C, D]: (k2_zfmisc_1(k2_tarski(A, B), k2_tarski(C, D)) = k2_enumset1(k4_tarski(A, C), k4_tarski(A, D), k4_tarski(B, C), k4_tarski(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_zfmisc_1)).
% 11.86/4.55  tff(f_51, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 11.86/4.55  tff(f_49, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 11.86/4.55  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 11.86/4.55  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 11.86/4.55  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 11.86/4.55  tff(f_54, negated_conjecture, ~(![A, B, C, D, E]: (k3_zfmisc_1(k2_tarski(A, B), k1_tarski(C), k2_tarski(D, E)) = k2_enumset1(k3_mcart_1(A, C, D), k3_mcart_1(B, C, D), k3_mcart_1(A, C, E), k3_mcart_1(B, C, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_mcart_1)).
% 11.86/4.55  tff(c_16, plain, (![A_26, B_27]: (k1_enumset1(A_26, A_26, B_27)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.86/4.55  tff(c_8, plain, (![A_13, B_14, C_15]: (k2_xboole_0(k2_tarski(A_13, B_14), k1_tarski(C_15))=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.86/4.55  tff(c_14, plain, (![A_25]: (k2_tarski(A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.86/4.55  tff(c_220, plain, (![A_70, B_71, C_72, D_73]: (k2_xboole_0(k2_tarski(A_70, B_71), k2_tarski(C_72, D_73))=k2_enumset1(A_70, B_71, C_72, D_73))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.86/4.55  tff(c_247, plain, (![A_70, B_71, A_25]: (k2_xboole_0(k2_tarski(A_70, B_71), k1_tarski(A_25))=k2_enumset1(A_70, B_71, A_25, A_25))), inference(superposition, [status(thm), theory('equality')], [c_14, c_220])).
% 11.86/4.55  tff(c_309, plain, (![A_83, B_84, A_85]: (k2_enumset1(A_83, B_84, A_85, A_85)=k1_enumset1(A_83, B_84, A_85))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_247])).
% 11.86/4.55  tff(c_18, plain, (![A_28, B_29, C_30]: (k2_enumset1(A_28, A_28, B_29, C_30)=k1_enumset1(A_28, B_29, C_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.86/4.55  tff(c_320, plain, (![B_84, A_85]: (k1_enumset1(B_84, B_84, A_85)=k1_enumset1(B_84, A_85, A_85))), inference(superposition, [status(thm), theory('equality')], [c_309, c_18])).
% 11.86/4.55  tff(c_371, plain, (![B_88, A_89]: (k1_enumset1(B_88, A_89, A_89)=k2_tarski(B_88, A_89))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_320])).
% 11.86/4.55  tff(c_6, plain, (![B_11, A_10, C_12]: (k2_xboole_0(k2_tarski(B_11, A_10), k2_tarski(C_12, A_10))=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.86/4.55  tff(c_252, plain, (![A_74, D_75, C_76]: (k2_enumset1(A_74, D_75, C_76, D_75)=k1_enumset1(D_75, A_74, C_76))), inference(superposition, [status(thm), theory('equality')], [c_220, c_6])).
% 11.86/4.55  tff(c_259, plain, (![D_75, C_76]: (k1_enumset1(D_75, D_75, C_76)=k1_enumset1(D_75, C_76, D_75))), inference(superposition, [status(thm), theory('equality')], [c_252, c_18])).
% 11.86/4.55  tff(c_268, plain, (![D_75, C_76]: (k1_enumset1(D_75, C_76, D_75)=k2_tarski(D_75, C_76))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_259])).
% 11.86/4.55  tff(c_227, plain, (![A_70, D_73, C_72]: (k2_enumset1(A_70, D_73, C_72, D_73)=k1_enumset1(D_73, A_70, C_72))), inference(superposition, [status(thm), theory('equality')], [c_220, c_6])).
% 11.86/4.55  tff(c_316, plain, (![A_85, A_83]: (k1_enumset1(A_85, A_83, A_85)=k1_enumset1(A_83, A_85, A_85))), inference(superposition, [status(thm), theory('equality')], [c_309, c_227])).
% 11.86/4.55  tff(c_333, plain, (![A_83, A_85]: (k1_enumset1(A_83, A_85, A_85)=k2_tarski(A_85, A_83))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_316])).
% 11.86/4.55  tff(c_377, plain, (![B_88, A_89]: (k2_tarski(B_88, A_89)=k2_tarski(A_89, B_88))), inference(superposition, [status(thm), theory('equality')], [c_371, c_333])).
% 11.86/4.55  tff(c_750, plain, (![A_108, C_109, D_110, B_111]: (k2_enumset1(k4_tarski(A_108, C_109), k4_tarski(A_108, D_110), k4_tarski(B_111, C_109), k4_tarski(B_111, D_110))=k2_zfmisc_1(k2_tarski(A_108, B_111), k2_tarski(C_109, D_110)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.86/4.55  tff(c_765, plain, (![A_108, D_110, B_111]: (k1_enumset1(k4_tarski(A_108, D_110), k4_tarski(B_111, D_110), k4_tarski(B_111, D_110))=k2_zfmisc_1(k2_tarski(A_108, B_111), k2_tarski(D_110, D_110)))), inference(superposition, [status(thm), theory('equality')], [c_750, c_18])).
% 11.86/4.55  tff(c_5201, plain, (![A_250, B_251, D_252]: (k2_zfmisc_1(k2_tarski(A_250, B_251), k1_tarski(D_252))=k2_tarski(k4_tarski(B_251, D_252), k4_tarski(A_250, D_252)))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_14, c_765])).
% 11.86/4.55  tff(c_26, plain, (![A_40, B_41, C_42]: (k2_zfmisc_1(k2_zfmisc_1(A_40, B_41), C_42)=k3_zfmisc_1(A_40, B_41, C_42))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.86/4.55  tff(c_5297, plain, (![B_251, D_252, A_250, C_42]: (k2_zfmisc_1(k2_tarski(k4_tarski(B_251, D_252), k4_tarski(A_250, D_252)), C_42)=k3_zfmisc_1(k2_tarski(A_250, B_251), k1_tarski(D_252), C_42))), inference(superposition, [status(thm), theory('equality')], [c_5201, c_26])).
% 11.86/4.55  tff(c_24, plain, (![A_37, B_38, C_39]: (k4_tarski(k4_tarski(A_37, B_38), C_39)=k3_mcart_1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.86/4.55  tff(c_779, plain, (![B_111, C_39, B_38, A_37, D_110]: (k2_enumset1(k3_mcart_1(A_37, B_38, C_39), k4_tarski(k4_tarski(A_37, B_38), D_110), k4_tarski(B_111, C_39), k4_tarski(B_111, D_110))=k2_zfmisc_1(k2_tarski(k4_tarski(A_37, B_38), B_111), k2_tarski(C_39, D_110)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_750])).
% 11.86/4.55  tff(c_3535, plain, (![B_219, D_220, A_218, B_222, C_221]: (k2_enumset1(k3_mcart_1(A_218, B_219, C_221), k3_mcart_1(A_218, B_219, D_220), k4_tarski(B_222, C_221), k4_tarski(B_222, D_220))=k2_zfmisc_1(k2_tarski(k4_tarski(A_218, B_219), B_222), k2_tarski(C_221, D_220)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_779])).
% 11.86/4.55  tff(c_3574, plain, (![C_39, B_219, B_38, D_220, A_218, A_37]: (k2_enumset1(k3_mcart_1(A_218, B_219, C_39), k3_mcart_1(A_218, B_219, D_220), k3_mcart_1(A_37, B_38, C_39), k4_tarski(k4_tarski(A_37, B_38), D_220))=k2_zfmisc_1(k2_tarski(k4_tarski(A_218, B_219), k4_tarski(A_37, B_38)), k2_tarski(C_39, D_220)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_3535])).
% 11.86/4.55  tff(c_3589, plain, (![C_39, B_219, B_38, D_220, A_218, A_37]: (k2_enumset1(k3_mcart_1(A_218, B_219, C_39), k3_mcart_1(A_218, B_219, D_220), k3_mcart_1(A_37, B_38, C_39), k3_mcart_1(A_37, B_38, D_220))=k2_zfmisc_1(k2_tarski(k4_tarski(A_218, B_219), k4_tarski(A_37, B_38)), k2_tarski(C_39, D_220)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3574])).
% 11.86/4.55  tff(c_338, plain, (![A_86, A_87]: (k1_enumset1(A_86, A_87, A_87)=k2_tarski(A_87, A_86))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_316])).
% 11.86/4.55  tff(c_10, plain, (![A_16, B_17, C_18, D_19]: (k2_xboole_0(k1_enumset1(A_16, B_17, C_18), k1_tarski(D_19))=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.86/4.55  tff(c_344, plain, (![A_87, A_86, D_19]: (k2_xboole_0(k2_tarski(A_87, A_86), k1_tarski(D_19))=k2_enumset1(A_86, A_87, A_87, D_19))), inference(superposition, [status(thm), theory('equality')], [c_338, c_10])).
% 11.86/4.55  tff(c_1010, plain, (![A_124, A_125, D_126]: (k2_enumset1(A_124, A_125, A_125, D_126)=k1_enumset1(A_125, A_124, D_126))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_344])).
% 11.86/4.55  tff(c_380, plain, (![B_88, A_89, D_19]: (k2_xboole_0(k2_tarski(B_88, A_89), k1_tarski(D_19))=k2_enumset1(B_88, A_89, A_89, D_19))), inference(superposition, [status(thm), theory('equality')], [c_371, c_10])).
% 11.86/4.55  tff(c_404, plain, (![B_88, A_89, D_19]: (k2_enumset1(B_88, A_89, A_89, D_19)=k1_enumset1(B_88, A_89, D_19))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_380])).
% 11.86/4.55  tff(c_1020, plain, (![A_125, A_124, D_126]: (k1_enumset1(A_125, A_124, D_126)=k1_enumset1(A_124, A_125, D_126))), inference(superposition, [status(thm), theory('equality')], [c_1010, c_404])).
% 11.86/4.55  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k2_xboole_0(k2_tarski(A_1, B_2), k2_tarski(C_3, D_4))=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.86/4.55  tff(c_485, plain, (![D_92, A_95, C_94, E_96, B_93]: (k2_xboole_0(k1_enumset1(A_95, B_93, C_94), k2_tarski(D_92, E_96))=k3_enumset1(A_95, B_93, C_94, D_92, E_96))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.86/4.55  tff(c_509, plain, (![A_26, B_27, D_92, E_96]: (k3_enumset1(A_26, A_26, B_27, D_92, E_96)=k2_xboole_0(k2_tarski(A_26, B_27), k2_tarski(D_92, E_96)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_485])).
% 11.86/4.55  tff(c_518, plain, (![A_26, B_27, D_92, E_96]: (k3_enumset1(A_26, A_26, B_27, D_92, E_96)=k2_enumset1(A_26, B_27, D_92, E_96))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_509])).
% 11.86/4.55  tff(c_522, plain, (![B_98, E_100, D_99, A_101, C_97]: (k2_xboole_0(k2_tarski(A_101, B_98), k1_enumset1(C_97, D_99, E_100))=k3_enumset1(A_101, B_98, C_97, D_99, E_100))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.86/4.55  tff(c_549, plain, (![A_25, C_97, D_99, E_100]: (k3_enumset1(A_25, A_25, C_97, D_99, E_100)=k2_xboole_0(k1_tarski(A_25), k1_enumset1(C_97, D_99, E_100)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_522])).
% 11.86/4.55  tff(c_2966, plain, (![A_203, C_204, D_205, E_206]: (k2_xboole_0(k1_tarski(A_203), k1_enumset1(C_204, D_205, E_206))=k2_enumset1(A_203, C_204, D_205, E_206))), inference(demodulation, [status(thm), theory('equality')], [c_518, c_549])).
% 11.86/4.55  tff(c_10520, plain, (![A_358, A_359, A_360, D_361]: (k2_xboole_0(k1_tarski(A_358), k1_enumset1(A_359, A_360, D_361))=k2_enumset1(A_358, A_360, A_359, D_361))), inference(superposition, [status(thm), theory('equality')], [c_1020, c_2966])).
% 11.86/4.55  tff(c_2965, plain, (![A_25, C_97, D_99, E_100]: (k2_xboole_0(k1_tarski(A_25), k1_enumset1(C_97, D_99, E_100))=k2_enumset1(A_25, C_97, D_99, E_100))), inference(demodulation, [status(thm), theory('equality')], [c_518, c_549])).
% 11.86/4.55  tff(c_10526, plain, (![A_358, A_360, A_359, D_361]: (k2_enumset1(A_358, A_360, A_359, D_361)=k2_enumset1(A_358, A_359, A_360, D_361))), inference(superposition, [status(thm), theory('equality')], [c_10520, c_2965])).
% 11.86/4.55  tff(c_28, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.86/4.55  tff(c_10601, plain, (k2_enumset1(k3_mcart_1('#skF_1', '#skF_3', '#skF_4'), k3_mcart_1('#skF_1', '#skF_3', '#skF_5'), k3_mcart_1('#skF_2', '#skF_3', '#skF_4'), k3_mcart_1('#skF_2', '#skF_3', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_10526, c_28])).
% 11.86/4.55  tff(c_13304, plain, (k2_zfmisc_1(k2_tarski(k4_tarski('#skF_1', '#skF_3'), k4_tarski('#skF_2', '#skF_3')), k2_tarski('#skF_4', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3589, c_10601])).
% 11.86/4.55  tff(c_26264, plain, (k3_zfmisc_1(k2_tarski('#skF_2', '#skF_1'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))!=k3_zfmisc_1(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5297, c_13304])).
% 11.86/4.55  tff(c_26267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_377, c_26264])).
% 11.86/4.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.86/4.55  
% 11.86/4.55  Inference rules
% 11.86/4.55  ----------------------
% 11.86/4.55  #Ref     : 0
% 11.86/4.55  #Sup     : 6110
% 11.86/4.55  #Fact    : 0
% 11.86/4.55  #Define  : 0
% 11.86/4.55  #Split   : 0
% 11.86/4.55  #Chain   : 0
% 11.86/4.55  #Close   : 0
% 11.86/4.55  
% 11.86/4.55  Ordering : KBO
% 11.86/4.55  
% 11.86/4.55  Simplification rules
% 11.86/4.55  ----------------------
% 11.86/4.55  #Subsume      : 796
% 11.86/4.55  #Demod        : 6982
% 11.86/4.55  #Tautology    : 4009
% 11.86/4.55  #SimpNegUnit  : 0
% 11.86/4.55  #BackRed      : 3
% 11.86/4.55  
% 11.86/4.55  #Partial instantiations: 0
% 11.86/4.55  #Strategies tried      : 1
% 11.86/4.55  
% 11.86/4.55  Timing (in seconds)
% 11.86/4.55  ----------------------
% 11.86/4.56  Preprocessing        : 0.30
% 11.86/4.56  Parsing              : 0.16
% 11.86/4.56  CNF conversion       : 0.02
% 11.86/4.56  Main loop            : 3.46
% 11.86/4.56  Inferencing          : 0.85
% 11.86/4.56  Reduction            : 1.93
% 11.86/4.56  Demodulation         : 1.74
% 11.86/4.56  BG Simplification    : 0.09
% 11.86/4.56  Subsumption          : 0.46
% 11.86/4.56  Abstraction          : 0.19
% 11.86/4.56  MUC search           : 0.00
% 11.86/4.56  Cooper               : 0.00
% 11.86/4.56  Total                : 3.79
% 11.86/4.56  Index Insertion      : 0.00
% 11.86/4.56  Index Deletion       : 0.00
% 11.86/4.56  Index Matching       : 0.00
% 11.86/4.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
