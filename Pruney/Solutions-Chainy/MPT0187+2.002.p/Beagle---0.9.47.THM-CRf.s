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
% DateTime   : Thu Dec  3 09:46:49 EST 2020

% Result     : Theorem 8.41s
% Output     : CNFRefutation 8.41s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 289 expanded)
%              Number of leaves         :   27 ( 110 expanded)
%              Depth                    :   13
%              Number of atoms          :   50 ( 271 expanded)
%              Number of equality atoms :   49 ( 270 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_tarski(A,B),k2_enumset1(C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

tff(c_8,plain,(
    ! [B_12,C_13,A_11] : k1_enumset1(B_12,C_13,A_11) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [A_50,B_51,C_52,D_53] : k3_enumset1(A_50,A_50,B_51,C_52,D_53) = k2_enumset1(A_50,B_51,C_52,D_53) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_47,B_48,C_49] : k2_enumset1(A_47,A_47,B_48,C_49) = k1_enumset1(A_47,B_48,C_49) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_299,plain,(
    ! [A_85,B_84,E_81,C_83,D_82] : k2_xboole_0(k2_enumset1(A_85,B_84,C_83,D_82),k1_tarski(E_81)) = k3_enumset1(A_85,B_84,C_83,D_82,E_81) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_311,plain,(
    ! [A_47,B_48,C_49,E_81] : k3_enumset1(A_47,A_47,B_48,C_49,E_81) = k2_xboole_0(k1_enumset1(A_47,B_48,C_49),k1_tarski(E_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_299])).

tff(c_628,plain,(
    ! [A_124,B_125,C_126,E_127] : k2_xboole_0(k1_enumset1(A_124,B_125,C_126),k1_tarski(E_127)) = k2_enumset1(A_124,B_125,C_126,E_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_311])).

tff(c_952,plain,(
    ! [B_154,C_155,A_156,E_157] : k2_xboole_0(k1_enumset1(B_154,C_155,A_156),k1_tarski(E_157)) = k2_enumset1(A_156,B_154,C_155,E_157) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_628])).

tff(c_314,plain,(
    ! [A_47,B_48,C_49,E_81] : k2_xboole_0(k1_enumset1(A_47,B_48,C_49),k1_tarski(E_81)) = k2_enumset1(A_47,B_48,C_49,E_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_311])).

tff(c_958,plain,(
    ! [B_154,C_155,A_156,E_157] : k2_enumset1(B_154,C_155,A_156,E_157) = k2_enumset1(A_156,B_154,C_155,E_157) ),
    inference(superposition,[status(thm),theory(equality)],[c_952,c_314])).

tff(c_20,plain,(
    ! [A_45,B_46] : k1_enumset1(A_45,A_45,B_46) = k2_tarski(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_652,plain,(
    ! [A_45,B_46,E_127] : k2_xboole_0(k2_tarski(A_45,B_46),k1_tarski(E_127)) = k2_enumset1(A_45,A_45,B_46,E_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_628])).

tff(c_656,plain,(
    ! [A_45,B_46,E_127] : k2_xboole_0(k2_tarski(A_45,B_46),k1_tarski(E_127)) = k1_enumset1(A_45,B_46,E_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_652])).

tff(c_47,plain,(
    ! [B_58,C_59,A_60] : k1_enumset1(B_58,C_59,A_60) = k1_enumset1(A_60,B_58,C_59) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_67,plain,(
    ! [A_60,C_59] : k1_enumset1(A_60,C_59,C_59) = k2_tarski(C_59,A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_20])).

tff(c_640,plain,(
    ! [C_59,A_60,E_127] : k2_xboole_0(k2_tarski(C_59,A_60),k1_tarski(E_127)) = k2_enumset1(A_60,C_59,C_59,E_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_628])).

tff(c_712,plain,(
    ! [A_138,C_139,E_140] : k2_enumset1(A_138,C_139,C_139,E_140) = k1_enumset1(C_139,A_138,E_140) ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_640])).

tff(c_10,plain,(
    ! [E_18,C_16,D_17,A_14,B_15] : k2_xboole_0(k2_enumset1(A_14,B_15,C_16,D_17),k1_tarski(E_18)) = k3_enumset1(A_14,B_15,C_16,D_17,E_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_728,plain,(
    ! [A_138,C_139,E_140,E_18] : k3_enumset1(A_138,C_139,C_139,E_140,E_18) = k2_xboole_0(k1_enumset1(C_139,A_138,E_140),k1_tarski(E_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_712,c_10])).

tff(c_753,plain,(
    ! [A_138,C_139,E_140,E_18] : k3_enumset1(A_138,C_139,C_139,E_140,E_18) = k2_enumset1(C_139,A_138,E_140,E_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_728])).

tff(c_398,plain,(
    ! [B_98,F_97,A_95,E_99,C_96,D_94] : k2_xboole_0(k3_enumset1(A_95,B_98,C_96,D_94,E_99),k1_tarski(F_97)) = k4_enumset1(A_95,B_98,C_96,D_94,E_99,F_97) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_410,plain,(
    ! [A_50,F_97,B_51,C_52,D_53] : k4_enumset1(A_50,A_50,B_51,C_52,D_53,F_97) = k2_xboole_0(k2_enumset1(A_50,B_51,C_52,D_53),k1_tarski(F_97)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_398])).

tff(c_416,plain,(
    ! [A_50,F_97,B_51,C_52,D_53] : k4_enumset1(A_50,A_50,B_51,C_52,D_53,F_97) = k3_enumset1(A_50,B_51,C_52,D_53,F_97) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_410])).

tff(c_320,plain,(
    ! [C_89,B_88,E_91,D_86,F_87,A_90] : k2_xboole_0(k1_enumset1(A_90,B_88,C_89),k1_enumset1(D_86,E_91,F_87)) = k4_enumset1(A_90,B_88,C_89,D_86,E_91,F_87) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_359,plain,(
    ! [A_45,E_91,D_86,B_46,F_87] : k4_enumset1(A_45,A_45,B_46,D_86,E_91,F_87) = k2_xboole_0(k2_tarski(A_45,B_46),k1_enumset1(D_86,E_91,F_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_320])).

tff(c_3307,plain,(
    ! [A_45,E_91,D_86,B_46,F_87] : k2_xboole_0(k2_tarski(A_45,B_46),k1_enumset1(D_86,E_91,F_87)) = k3_enumset1(A_45,B_46,D_86,E_91,F_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_359])).

tff(c_512,plain,(
    ! [A_108,B_107,C_105,F_109,E_106,D_110] : k2_xboole_0(k2_tarski(A_108,B_107),k2_enumset1(C_105,D_110,E_106,F_109)) = k4_enumset1(A_108,B_107,C_105,D_110,E_106,F_109) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_527,plain,(
    ! [A_108,A_47,B_107,C_49,B_48] : k4_enumset1(A_108,B_107,A_47,A_47,B_48,C_49) = k2_xboole_0(k2_tarski(A_108,B_107),k1_enumset1(A_47,B_48,C_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_512])).

tff(c_3497,plain,(
    ! [A_256,B_255,A_254,C_258,B_257] : k4_enumset1(A_256,B_257,A_254,A_254,B_255,C_258) = k3_enumset1(A_256,B_257,A_254,B_255,C_258) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3307,c_527])).

tff(c_3520,plain,(
    ! [B_257,A_254,B_255,C_258] : k3_enumset1(B_257,B_257,A_254,B_255,C_258) = k3_enumset1(B_257,A_254,A_254,B_255,C_258) ),
    inference(superposition,[status(thm),theory(equality)],[c_3497,c_416])).

tff(c_3794,plain,(
    ! [B_272,A_273,B_274,C_275] : k2_enumset1(B_272,A_273,B_274,C_275) = k2_enumset1(A_273,B_272,B_274,C_275) ),
    inference(demodulation,[status(thm),theory(equality)],[c_753,c_24,c_3520])).

tff(c_3937,plain,(
    ! [B_154,C_155,A_156,E_157] : k2_enumset1(B_154,C_155,A_156,E_157) = k2_enumset1(B_154,A_156,C_155,E_157) ),
    inference(superposition,[status(thm),theory(equality)],[c_958,c_3794])).

tff(c_4673,plain,(
    ! [C_296,A_300,B_298,C_295,A_297,B_299] : k2_xboole_0(k1_enumset1(A_300,B_299,C_296),k1_enumset1(B_298,C_295,A_297)) = k4_enumset1(A_300,B_299,C_296,A_297,B_298,C_295) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_320])).

tff(c_4772,plain,(
    ! [A_45,B_46,B_298,C_295,A_297] : k4_enumset1(A_45,A_45,B_46,A_297,B_298,C_295) = k2_xboole_0(k2_tarski(A_45,B_46),k1_enumset1(B_298,C_295,A_297)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4673])).

tff(c_9245,plain,(
    ! [C_402,B_398,A_399,A_400,B_401] : k3_enumset1(A_399,B_398,B_401,C_402,A_400) = k3_enumset1(A_399,B_398,A_400,B_401,C_402) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3307,c_416,c_4772])).

tff(c_10462,plain,(
    ! [A_411,C_412,D_413,B_414] : k3_enumset1(A_411,A_411,C_412,D_413,B_414) = k2_enumset1(A_411,B_414,C_412,D_413) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_9245])).

tff(c_10597,plain,(
    ! [A_50,D_53,B_51,C_52] : k2_enumset1(A_50,D_53,B_51,C_52) = k2_enumset1(A_50,B_51,C_52,D_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_10462])).

tff(c_28,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_990,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_28])).

tff(c_8320,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3937,c_990])).

tff(c_10777,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10597,c_8320])).

tff(c_10780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3937,c_958,c_10777])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:41:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.41/2.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.41/2.88  
% 8.41/2.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.41/2.88  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.41/2.88  
% 8.41/2.88  %Foreground sorts:
% 8.41/2.88  
% 8.41/2.88  
% 8.41/2.88  %Background operators:
% 8.41/2.88  
% 8.41/2.88  
% 8.41/2.88  %Foreground operators:
% 8.41/2.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.41/2.88  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.41/2.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.41/2.88  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.41/2.88  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.41/2.88  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.41/2.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.41/2.88  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.41/2.88  tff('#skF_2', type, '#skF_2': $i).
% 8.41/2.88  tff('#skF_3', type, '#skF_3': $i).
% 8.41/2.88  tff('#skF_1', type, '#skF_1': $i).
% 8.41/2.88  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.41/2.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.41/2.88  tff('#skF_4', type, '#skF_4': $i).
% 8.41/2.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.41/2.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.41/2.88  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.41/2.88  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.41/2.88  
% 8.41/2.89  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 8.41/2.89  tff(f_49, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 8.41/2.89  tff(f_47, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 8.41/2.89  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 8.41/2.89  tff(f_45, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 8.41/2.89  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 8.41/2.89  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 8.41/2.89  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_tarski(A, B), k2_enumset1(C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_enumset1)).
% 8.41/2.89  tff(f_54, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 8.41/2.89  tff(c_8, plain, (![B_12, C_13, A_11]: (k1_enumset1(B_12, C_13, A_11)=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.41/2.89  tff(c_24, plain, (![A_50, B_51, C_52, D_53]: (k3_enumset1(A_50, A_50, B_51, C_52, D_53)=k2_enumset1(A_50, B_51, C_52, D_53))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.41/2.89  tff(c_22, plain, (![A_47, B_48, C_49]: (k2_enumset1(A_47, A_47, B_48, C_49)=k1_enumset1(A_47, B_48, C_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.41/2.89  tff(c_299, plain, (![A_85, B_84, E_81, C_83, D_82]: (k2_xboole_0(k2_enumset1(A_85, B_84, C_83, D_82), k1_tarski(E_81))=k3_enumset1(A_85, B_84, C_83, D_82, E_81))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.41/2.89  tff(c_311, plain, (![A_47, B_48, C_49, E_81]: (k3_enumset1(A_47, A_47, B_48, C_49, E_81)=k2_xboole_0(k1_enumset1(A_47, B_48, C_49), k1_tarski(E_81)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_299])).
% 8.41/2.89  tff(c_628, plain, (![A_124, B_125, C_126, E_127]: (k2_xboole_0(k1_enumset1(A_124, B_125, C_126), k1_tarski(E_127))=k2_enumset1(A_124, B_125, C_126, E_127))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_311])).
% 8.41/2.89  tff(c_952, plain, (![B_154, C_155, A_156, E_157]: (k2_xboole_0(k1_enumset1(B_154, C_155, A_156), k1_tarski(E_157))=k2_enumset1(A_156, B_154, C_155, E_157))), inference(superposition, [status(thm), theory('equality')], [c_8, c_628])).
% 8.41/2.89  tff(c_314, plain, (![A_47, B_48, C_49, E_81]: (k2_xboole_0(k1_enumset1(A_47, B_48, C_49), k1_tarski(E_81))=k2_enumset1(A_47, B_48, C_49, E_81))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_311])).
% 8.41/2.89  tff(c_958, plain, (![B_154, C_155, A_156, E_157]: (k2_enumset1(B_154, C_155, A_156, E_157)=k2_enumset1(A_156, B_154, C_155, E_157))), inference(superposition, [status(thm), theory('equality')], [c_952, c_314])).
% 8.41/2.89  tff(c_20, plain, (![A_45, B_46]: (k1_enumset1(A_45, A_45, B_46)=k2_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.41/2.89  tff(c_652, plain, (![A_45, B_46, E_127]: (k2_xboole_0(k2_tarski(A_45, B_46), k1_tarski(E_127))=k2_enumset1(A_45, A_45, B_46, E_127))), inference(superposition, [status(thm), theory('equality')], [c_20, c_628])).
% 8.41/2.89  tff(c_656, plain, (![A_45, B_46, E_127]: (k2_xboole_0(k2_tarski(A_45, B_46), k1_tarski(E_127))=k1_enumset1(A_45, B_46, E_127))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_652])).
% 8.41/2.89  tff(c_47, plain, (![B_58, C_59, A_60]: (k1_enumset1(B_58, C_59, A_60)=k1_enumset1(A_60, B_58, C_59))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.41/2.89  tff(c_67, plain, (![A_60, C_59]: (k1_enumset1(A_60, C_59, C_59)=k2_tarski(C_59, A_60))), inference(superposition, [status(thm), theory('equality')], [c_47, c_20])).
% 8.41/2.89  tff(c_640, plain, (![C_59, A_60, E_127]: (k2_xboole_0(k2_tarski(C_59, A_60), k1_tarski(E_127))=k2_enumset1(A_60, C_59, C_59, E_127))), inference(superposition, [status(thm), theory('equality')], [c_67, c_628])).
% 8.41/2.89  tff(c_712, plain, (![A_138, C_139, E_140]: (k2_enumset1(A_138, C_139, C_139, E_140)=k1_enumset1(C_139, A_138, E_140))), inference(demodulation, [status(thm), theory('equality')], [c_656, c_640])).
% 8.41/2.89  tff(c_10, plain, (![E_18, C_16, D_17, A_14, B_15]: (k2_xboole_0(k2_enumset1(A_14, B_15, C_16, D_17), k1_tarski(E_18))=k3_enumset1(A_14, B_15, C_16, D_17, E_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.41/2.89  tff(c_728, plain, (![A_138, C_139, E_140, E_18]: (k3_enumset1(A_138, C_139, C_139, E_140, E_18)=k2_xboole_0(k1_enumset1(C_139, A_138, E_140), k1_tarski(E_18)))), inference(superposition, [status(thm), theory('equality')], [c_712, c_10])).
% 8.41/2.89  tff(c_753, plain, (![A_138, C_139, E_140, E_18]: (k3_enumset1(A_138, C_139, C_139, E_140, E_18)=k2_enumset1(C_139, A_138, E_140, E_18))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_728])).
% 8.41/2.89  tff(c_398, plain, (![B_98, F_97, A_95, E_99, C_96, D_94]: (k2_xboole_0(k3_enumset1(A_95, B_98, C_96, D_94, E_99), k1_tarski(F_97))=k4_enumset1(A_95, B_98, C_96, D_94, E_99, F_97))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.41/2.89  tff(c_410, plain, (![A_50, F_97, B_51, C_52, D_53]: (k4_enumset1(A_50, A_50, B_51, C_52, D_53, F_97)=k2_xboole_0(k2_enumset1(A_50, B_51, C_52, D_53), k1_tarski(F_97)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_398])).
% 8.41/2.89  tff(c_416, plain, (![A_50, F_97, B_51, C_52, D_53]: (k4_enumset1(A_50, A_50, B_51, C_52, D_53, F_97)=k3_enumset1(A_50, B_51, C_52, D_53, F_97))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_410])).
% 8.41/2.89  tff(c_320, plain, (![C_89, B_88, E_91, D_86, F_87, A_90]: (k2_xboole_0(k1_enumset1(A_90, B_88, C_89), k1_enumset1(D_86, E_91, F_87))=k4_enumset1(A_90, B_88, C_89, D_86, E_91, F_87))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.41/2.89  tff(c_359, plain, (![A_45, E_91, D_86, B_46, F_87]: (k4_enumset1(A_45, A_45, B_46, D_86, E_91, F_87)=k2_xboole_0(k2_tarski(A_45, B_46), k1_enumset1(D_86, E_91, F_87)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_320])).
% 8.41/2.89  tff(c_3307, plain, (![A_45, E_91, D_86, B_46, F_87]: (k2_xboole_0(k2_tarski(A_45, B_46), k1_enumset1(D_86, E_91, F_87))=k3_enumset1(A_45, B_46, D_86, E_91, F_87))), inference(demodulation, [status(thm), theory('equality')], [c_416, c_359])).
% 8.41/2.89  tff(c_512, plain, (![A_108, B_107, C_105, F_109, E_106, D_110]: (k2_xboole_0(k2_tarski(A_108, B_107), k2_enumset1(C_105, D_110, E_106, F_109))=k4_enumset1(A_108, B_107, C_105, D_110, E_106, F_109))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.41/2.89  tff(c_527, plain, (![A_108, A_47, B_107, C_49, B_48]: (k4_enumset1(A_108, B_107, A_47, A_47, B_48, C_49)=k2_xboole_0(k2_tarski(A_108, B_107), k1_enumset1(A_47, B_48, C_49)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_512])).
% 8.41/2.89  tff(c_3497, plain, (![A_256, B_255, A_254, C_258, B_257]: (k4_enumset1(A_256, B_257, A_254, A_254, B_255, C_258)=k3_enumset1(A_256, B_257, A_254, B_255, C_258))), inference(demodulation, [status(thm), theory('equality')], [c_3307, c_527])).
% 8.41/2.89  tff(c_3520, plain, (![B_257, A_254, B_255, C_258]: (k3_enumset1(B_257, B_257, A_254, B_255, C_258)=k3_enumset1(B_257, A_254, A_254, B_255, C_258))), inference(superposition, [status(thm), theory('equality')], [c_3497, c_416])).
% 8.41/2.89  tff(c_3794, plain, (![B_272, A_273, B_274, C_275]: (k2_enumset1(B_272, A_273, B_274, C_275)=k2_enumset1(A_273, B_272, B_274, C_275))), inference(demodulation, [status(thm), theory('equality')], [c_753, c_24, c_3520])).
% 8.41/2.89  tff(c_3937, plain, (![B_154, C_155, A_156, E_157]: (k2_enumset1(B_154, C_155, A_156, E_157)=k2_enumset1(B_154, A_156, C_155, E_157))), inference(superposition, [status(thm), theory('equality')], [c_958, c_3794])).
% 8.41/2.89  tff(c_4673, plain, (![C_296, A_300, B_298, C_295, A_297, B_299]: (k2_xboole_0(k1_enumset1(A_300, B_299, C_296), k1_enumset1(B_298, C_295, A_297))=k4_enumset1(A_300, B_299, C_296, A_297, B_298, C_295))), inference(superposition, [status(thm), theory('equality')], [c_8, c_320])).
% 8.41/2.89  tff(c_4772, plain, (![A_45, B_46, B_298, C_295, A_297]: (k4_enumset1(A_45, A_45, B_46, A_297, B_298, C_295)=k2_xboole_0(k2_tarski(A_45, B_46), k1_enumset1(B_298, C_295, A_297)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4673])).
% 8.41/2.89  tff(c_9245, plain, (![C_402, B_398, A_399, A_400, B_401]: (k3_enumset1(A_399, B_398, B_401, C_402, A_400)=k3_enumset1(A_399, B_398, A_400, B_401, C_402))), inference(demodulation, [status(thm), theory('equality')], [c_3307, c_416, c_4772])).
% 8.41/2.89  tff(c_10462, plain, (![A_411, C_412, D_413, B_414]: (k3_enumset1(A_411, A_411, C_412, D_413, B_414)=k2_enumset1(A_411, B_414, C_412, D_413))), inference(superposition, [status(thm), theory('equality')], [c_24, c_9245])).
% 8.41/2.89  tff(c_10597, plain, (![A_50, D_53, B_51, C_52]: (k2_enumset1(A_50, D_53, B_51, C_52)=k2_enumset1(A_50, B_51, C_52, D_53))), inference(superposition, [status(thm), theory('equality')], [c_24, c_10462])).
% 8.41/2.89  tff(c_28, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.41/2.89  tff(c_990, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_958, c_28])).
% 8.41/2.89  tff(c_8320, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3937, c_990])).
% 8.41/2.89  tff(c_10777, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10597, c_8320])).
% 8.41/2.89  tff(c_10780, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3937, c_958, c_10777])).
% 8.41/2.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.41/2.89  
% 8.41/2.89  Inference rules
% 8.41/2.89  ----------------------
% 8.41/2.89  #Ref     : 0
% 8.41/2.89  #Sup     : 2571
% 8.41/2.89  #Fact    : 0
% 8.41/2.89  #Define  : 0
% 8.41/2.89  #Split   : 0
% 8.41/2.89  #Chain   : 0
% 8.41/2.89  #Close   : 0
% 8.41/2.89  
% 8.41/2.89  Ordering : KBO
% 8.41/2.89  
% 8.41/2.89  Simplification rules
% 8.41/2.89  ----------------------
% 8.41/2.89  #Subsume      : 251
% 8.41/2.89  #Demod        : 2209
% 8.41/2.89  #Tautology    : 1545
% 8.41/2.89  #SimpNegUnit  : 0
% 8.41/2.89  #BackRed      : 6
% 8.41/2.89  
% 8.41/2.89  #Partial instantiations: 0
% 8.41/2.89  #Strategies tried      : 1
% 8.41/2.89  
% 8.41/2.89  Timing (in seconds)
% 8.41/2.89  ----------------------
% 8.54/2.90  Preprocessing        : 0.32
% 8.54/2.90  Parsing              : 0.17
% 8.54/2.90  CNF conversion       : 0.02
% 8.54/2.90  Main loop            : 1.80
% 8.54/2.90  Inferencing          : 0.57
% 8.54/2.90  Reduction            : 0.87
% 8.54/2.90  Demodulation         : 0.76
% 8.54/2.90  BG Simplification    : 0.07
% 8.54/2.90  Subsumption          : 0.21
% 8.54/2.90  Abstraction          : 0.11
% 8.54/2.90  MUC search           : 0.00
% 8.54/2.90  Cooper               : 0.00
% 8.54/2.90  Total                : 2.16
% 8.54/2.90  Index Insertion      : 0.00
% 8.54/2.90  Index Deletion       : 0.00
% 8.54/2.90  Index Matching       : 0.00
% 8.54/2.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
