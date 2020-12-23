%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:25 EST 2020

% Result     : Theorem 12.25s
% Output     : CNFRefutation 12.33s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 368 expanded)
%              Number of leaves         :   28 ( 138 expanded)
%              Depth                    :   12
%              Number of atoms          :   50 ( 350 expanded)
%              Number of equality atoms :   49 ( 349 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_343,plain,(
    ! [D_105,C_106,B_107,A_108] : k2_enumset1(D_105,C_106,B_107,A_108) = k2_enumset1(A_108,B_107,C_106,D_105) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_210,plain,(
    ! [B_98,D_99,C_100,A_101] : k2_enumset1(B_98,D_99,C_100,A_101) = k2_enumset1(A_101,B_98,C_100,D_99) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [A_60,B_61,C_62] : k2_enumset1(A_60,A_60,B_61,C_62) = k1_enumset1(A_60,B_61,C_62) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_250,plain,(
    ! [A_101,D_99,C_100] : k2_enumset1(A_101,D_99,C_100,D_99) = k1_enumset1(D_99,C_100,A_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_30])).

tff(c_852,plain,(
    ! [A_133,B_134,D_135] : k2_enumset1(A_133,B_134,A_133,D_135) = k1_enumset1(A_133,B_134,D_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_250])).

tff(c_12,plain,(
    ! [B_15,D_17,C_16,A_14] : k2_enumset1(B_15,D_17,C_16,A_14) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_466,plain,(
    ! [D_109,C_110,B_111] : k2_enumset1(D_109,C_110,B_111,B_111) = k1_enumset1(B_111,C_110,D_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_30])).

tff(c_522,plain,(
    ! [A_14,B_15,D_17] : k2_enumset1(A_14,B_15,A_14,D_17) = k1_enumset1(A_14,D_17,B_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_466])).

tff(c_858,plain,(
    ! [A_133,D_135,B_134] : k1_enumset1(A_133,D_135,B_134) = k1_enumset1(A_133,B_134,D_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_522])).

tff(c_10,plain,(
    ! [A_10,D_13,C_12,B_11] : k2_enumset1(A_10,D_13,C_12,B_11) = k2_enumset1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ! [A_63,B_64,C_65,D_66] : k3_enumset1(A_63,A_63,B_64,C_65,D_66) = k2_enumset1(A_63,B_64,C_65,D_66) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    ! [A_58,B_59] : k1_enumset1(A_58,A_58,B_59) = k2_tarski(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    ! [D_70,B_68,A_67,C_69,E_71] : k4_enumset1(A_67,A_67,B_68,C_69,D_70,E_71) = k3_enumset1(A_67,B_68,C_69,D_70,E_71) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1506,plain,(
    ! [B_166,F_170,D_168,A_165,E_169,C_167] : k2_xboole_0(k2_enumset1(A_165,B_166,C_167,D_168),k2_tarski(E_169,F_170)) = k4_enumset1(A_165,B_166,C_167,D_168,E_169,F_170) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1560,plain,(
    ! [F_170,A_60,C_62,E_169,B_61] : k4_enumset1(A_60,A_60,B_61,C_62,E_169,F_170) = k2_xboole_0(k1_enumset1(A_60,B_61,C_62),k2_tarski(E_169,F_170)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1506])).

tff(c_8973,plain,(
    ! [A_296,F_293,C_292,E_294,B_295] : k2_xboole_0(k1_enumset1(A_296,B_295,C_292),k2_tarski(E_294,F_293)) = k3_enumset1(A_296,B_295,C_292,E_294,F_293) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1560])).

tff(c_9000,plain,(
    ! [A_58,B_59,E_294,F_293] : k3_enumset1(A_58,A_58,B_59,E_294,F_293) = k2_xboole_0(k2_tarski(A_58,B_59),k2_tarski(E_294,F_293)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_8973])).

tff(c_9006,plain,(
    ! [A_58,B_59,E_294,F_293] : k2_xboole_0(k2_tarski(A_58,B_59),k2_tarski(E_294,F_293)) = k2_enumset1(A_58,B_59,E_294,F_293) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_9000])).

tff(c_530,plain,(
    ! [A_10,D_13,B_11] : k2_enumset1(A_10,D_13,D_13,B_11) = k1_enumset1(D_13,B_11,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_466])).

tff(c_1161,plain,(
    ! [D_144,A_143,C_145,E_142,B_146] : k2_xboole_0(k2_enumset1(A_143,B_146,C_145,D_144),k1_tarski(E_142)) = k3_enumset1(A_143,B_146,C_145,D_144,E_142) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1209,plain,(
    ! [A_60,B_61,C_62,E_142] : k3_enumset1(A_60,A_60,B_61,C_62,E_142) = k2_xboole_0(k1_enumset1(A_60,B_61,C_62),k1_tarski(E_142)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1161])).

tff(c_1212,plain,(
    ! [A_60,B_61,C_62,E_142] : k2_xboole_0(k1_enumset1(A_60,B_61,C_62),k1_tarski(E_142)) = k2_enumset1(A_60,B_61,C_62,E_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1209])).

tff(c_9034,plain,(
    ! [A_303,B_302,C_301,D_299,E_300] : k2_xboole_0(k2_enumset1(A_303,B_302,C_301,D_299),k1_tarski(E_300)) = k3_enumset1(B_302,D_299,C_301,A_303,E_300) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1161])).

tff(c_9199,plain,(
    ! [A_60,C_62,B_61,E_300] : k3_enumset1(A_60,C_62,B_61,A_60,E_300) = k2_xboole_0(k1_enumset1(A_60,B_61,C_62),k1_tarski(E_300)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_9034])).

tff(c_10704,plain,(
    ! [A_361,C_362,B_363,E_364] : k3_enumset1(A_361,C_362,B_363,A_361,E_364) = k2_enumset1(A_361,B_363,C_362,E_364) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1212,c_9199])).

tff(c_399,plain,(
    ! [D_105,C_106,B_107] : k2_enumset1(D_105,C_106,B_107,B_107) = k1_enumset1(B_107,C_106,D_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_30])).

tff(c_8252,plain,(
    ! [C_275,D_274,E_271,A_273,B_272] : k2_xboole_0(k2_enumset1(A_273,B_272,C_275,D_274),k1_tarski(E_271)) = k3_enumset1(A_273,D_274,C_275,B_272,E_271) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1161])).

tff(c_8372,plain,(
    ! [D_105,B_107,C_106,E_271] : k3_enumset1(D_105,B_107,B_107,C_106,E_271) = k2_xboole_0(k1_enumset1(B_107,C_106,D_105),k1_tarski(E_271)) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_8252])).

tff(c_8410,plain,(
    ! [D_105,B_107,C_106,E_271] : k3_enumset1(D_105,B_107,B_107,C_106,E_271) = k2_enumset1(B_107,C_106,D_105,E_271) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1212,c_8372])).

tff(c_10711,plain,(
    ! [B_363,A_361,E_364] : k2_enumset1(B_363,A_361,A_361,E_364) = k2_enumset1(A_361,B_363,B_363,E_364) ),
    inference(superposition,[status(thm),theory(equality)],[c_10704,c_8410])).

tff(c_10812,plain,(
    ! [B_373,E_374,A_375] : k1_enumset1(B_373,E_374,A_375) = k1_enumset1(A_375,E_374,B_373) ),
    inference(demodulation,[status(thm),theory(equality)],[c_530,c_530,c_10711])).

tff(c_538,plain,(
    ! [C_62,A_60] : k1_enumset1(C_62,A_60,A_60) = k1_enumset1(A_60,C_62,C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_466])).

tff(c_10870,plain,(
    ! [B_373,A_375] : k1_enumset1(B_373,B_373,A_375) = k1_enumset1(B_373,A_375,A_375) ),
    inference(superposition,[status(thm),theory(equality)],[c_10812,c_538])).

tff(c_10937,plain,(
    ! [B_373,A_375] : k1_enumset1(B_373,A_375,A_375) = k2_tarski(B_373,A_375) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_10870])).

tff(c_10949,plain,(
    ! [C_62,A_60] : k2_tarski(C_62,A_60) = k2_tarski(A_60,C_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10937,c_10937,c_538])).

tff(c_38,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_967,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_858,c_38])).

tff(c_11010,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10949,c_10949,c_967])).

tff(c_23433,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9006,c_11010])).

tff(c_23436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_858,c_522,c_10,c_23433])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n012.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 18:00:22 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.25/5.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.25/5.22  
% 12.25/5.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.33/5.22  %$ k7_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 12.33/5.22  
% 12.33/5.22  %Foreground sorts:
% 12.33/5.22  
% 12.33/5.22  
% 12.33/5.22  %Background operators:
% 12.33/5.22  
% 12.33/5.22  
% 12.33/5.22  %Foreground operators:
% 12.33/5.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.33/5.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.33/5.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.33/5.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.33/5.22  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 12.33/5.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.33/5.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.33/5.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.33/5.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.33/5.22  tff('#skF_2', type, '#skF_2': $i).
% 12.33/5.22  tff('#skF_3', type, '#skF_3': $i).
% 12.33/5.22  tff('#skF_1', type, '#skF_1': $i).
% 12.33/5.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.33/5.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.33/5.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.33/5.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.33/5.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.33/5.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.33/5.22  
% 12.33/5.24  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 12.33/5.24  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 12.33/5.24  tff(f_55, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 12.33/5.24  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 12.33/5.24  tff(f_57, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 12.33/5.24  tff(f_53, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 12.33/5.24  tff(f_59, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 12.33/5.24  tff(f_49, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_enumset1)).
% 12.33/5.24  tff(f_45, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 12.33/5.24  tff(f_64, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 12.33/5.24  tff(c_343, plain, (![D_105, C_106, B_107, A_108]: (k2_enumset1(D_105, C_106, B_107, A_108)=k2_enumset1(A_108, B_107, C_106, D_105))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.33/5.24  tff(c_210, plain, (![B_98, D_99, C_100, A_101]: (k2_enumset1(B_98, D_99, C_100, A_101)=k2_enumset1(A_101, B_98, C_100, D_99))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.33/5.24  tff(c_30, plain, (![A_60, B_61, C_62]: (k2_enumset1(A_60, A_60, B_61, C_62)=k1_enumset1(A_60, B_61, C_62))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.33/5.24  tff(c_250, plain, (![A_101, D_99, C_100]: (k2_enumset1(A_101, D_99, C_100, D_99)=k1_enumset1(D_99, C_100, A_101))), inference(superposition, [status(thm), theory('equality')], [c_210, c_30])).
% 12.33/5.24  tff(c_852, plain, (![A_133, B_134, D_135]: (k2_enumset1(A_133, B_134, A_133, D_135)=k1_enumset1(A_133, B_134, D_135))), inference(superposition, [status(thm), theory('equality')], [c_343, c_250])).
% 12.33/5.24  tff(c_12, plain, (![B_15, D_17, C_16, A_14]: (k2_enumset1(B_15, D_17, C_16, A_14)=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.33/5.24  tff(c_466, plain, (![D_109, C_110, B_111]: (k2_enumset1(D_109, C_110, B_111, B_111)=k1_enumset1(B_111, C_110, D_109))), inference(superposition, [status(thm), theory('equality')], [c_343, c_30])).
% 12.33/5.24  tff(c_522, plain, (![A_14, B_15, D_17]: (k2_enumset1(A_14, B_15, A_14, D_17)=k1_enumset1(A_14, D_17, B_15))), inference(superposition, [status(thm), theory('equality')], [c_12, c_466])).
% 12.33/5.24  tff(c_858, plain, (![A_133, D_135, B_134]: (k1_enumset1(A_133, D_135, B_134)=k1_enumset1(A_133, B_134, D_135))), inference(superposition, [status(thm), theory('equality')], [c_852, c_522])).
% 12.33/5.24  tff(c_10, plain, (![A_10, D_13, C_12, B_11]: (k2_enumset1(A_10, D_13, C_12, B_11)=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.33/5.24  tff(c_32, plain, (![A_63, B_64, C_65, D_66]: (k3_enumset1(A_63, A_63, B_64, C_65, D_66)=k2_enumset1(A_63, B_64, C_65, D_66))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.33/5.24  tff(c_28, plain, (![A_58, B_59]: (k1_enumset1(A_58, A_58, B_59)=k2_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.33/5.24  tff(c_34, plain, (![D_70, B_68, A_67, C_69, E_71]: (k4_enumset1(A_67, A_67, B_68, C_69, D_70, E_71)=k3_enumset1(A_67, B_68, C_69, D_70, E_71))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.33/5.24  tff(c_1506, plain, (![B_166, F_170, D_168, A_165, E_169, C_167]: (k2_xboole_0(k2_enumset1(A_165, B_166, C_167, D_168), k2_tarski(E_169, F_170))=k4_enumset1(A_165, B_166, C_167, D_168, E_169, F_170))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.33/5.24  tff(c_1560, plain, (![F_170, A_60, C_62, E_169, B_61]: (k4_enumset1(A_60, A_60, B_61, C_62, E_169, F_170)=k2_xboole_0(k1_enumset1(A_60, B_61, C_62), k2_tarski(E_169, F_170)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1506])).
% 12.33/5.24  tff(c_8973, plain, (![A_296, F_293, C_292, E_294, B_295]: (k2_xboole_0(k1_enumset1(A_296, B_295, C_292), k2_tarski(E_294, F_293))=k3_enumset1(A_296, B_295, C_292, E_294, F_293))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1560])).
% 12.33/5.24  tff(c_9000, plain, (![A_58, B_59, E_294, F_293]: (k3_enumset1(A_58, A_58, B_59, E_294, F_293)=k2_xboole_0(k2_tarski(A_58, B_59), k2_tarski(E_294, F_293)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_8973])).
% 12.33/5.24  tff(c_9006, plain, (![A_58, B_59, E_294, F_293]: (k2_xboole_0(k2_tarski(A_58, B_59), k2_tarski(E_294, F_293))=k2_enumset1(A_58, B_59, E_294, F_293))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_9000])).
% 12.33/5.24  tff(c_530, plain, (![A_10, D_13, B_11]: (k2_enumset1(A_10, D_13, D_13, B_11)=k1_enumset1(D_13, B_11, A_10))), inference(superposition, [status(thm), theory('equality')], [c_10, c_466])).
% 12.33/5.24  tff(c_1161, plain, (![D_144, A_143, C_145, E_142, B_146]: (k2_xboole_0(k2_enumset1(A_143, B_146, C_145, D_144), k1_tarski(E_142))=k3_enumset1(A_143, B_146, C_145, D_144, E_142))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.33/5.24  tff(c_1209, plain, (![A_60, B_61, C_62, E_142]: (k3_enumset1(A_60, A_60, B_61, C_62, E_142)=k2_xboole_0(k1_enumset1(A_60, B_61, C_62), k1_tarski(E_142)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1161])).
% 12.33/5.24  tff(c_1212, plain, (![A_60, B_61, C_62, E_142]: (k2_xboole_0(k1_enumset1(A_60, B_61, C_62), k1_tarski(E_142))=k2_enumset1(A_60, B_61, C_62, E_142))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1209])).
% 12.33/5.24  tff(c_9034, plain, (![A_303, B_302, C_301, D_299, E_300]: (k2_xboole_0(k2_enumset1(A_303, B_302, C_301, D_299), k1_tarski(E_300))=k3_enumset1(B_302, D_299, C_301, A_303, E_300))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1161])).
% 12.33/5.24  tff(c_9199, plain, (![A_60, C_62, B_61, E_300]: (k3_enumset1(A_60, C_62, B_61, A_60, E_300)=k2_xboole_0(k1_enumset1(A_60, B_61, C_62), k1_tarski(E_300)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_9034])).
% 12.33/5.24  tff(c_10704, plain, (![A_361, C_362, B_363, E_364]: (k3_enumset1(A_361, C_362, B_363, A_361, E_364)=k2_enumset1(A_361, B_363, C_362, E_364))), inference(demodulation, [status(thm), theory('equality')], [c_1212, c_9199])).
% 12.33/5.24  tff(c_399, plain, (![D_105, C_106, B_107]: (k2_enumset1(D_105, C_106, B_107, B_107)=k1_enumset1(B_107, C_106, D_105))), inference(superposition, [status(thm), theory('equality')], [c_343, c_30])).
% 12.33/5.24  tff(c_8252, plain, (![C_275, D_274, E_271, A_273, B_272]: (k2_xboole_0(k2_enumset1(A_273, B_272, C_275, D_274), k1_tarski(E_271))=k3_enumset1(A_273, D_274, C_275, B_272, E_271))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1161])).
% 12.33/5.24  tff(c_8372, plain, (![D_105, B_107, C_106, E_271]: (k3_enumset1(D_105, B_107, B_107, C_106, E_271)=k2_xboole_0(k1_enumset1(B_107, C_106, D_105), k1_tarski(E_271)))), inference(superposition, [status(thm), theory('equality')], [c_399, c_8252])).
% 12.33/5.24  tff(c_8410, plain, (![D_105, B_107, C_106, E_271]: (k3_enumset1(D_105, B_107, B_107, C_106, E_271)=k2_enumset1(B_107, C_106, D_105, E_271))), inference(demodulation, [status(thm), theory('equality')], [c_1212, c_8372])).
% 12.33/5.24  tff(c_10711, plain, (![B_363, A_361, E_364]: (k2_enumset1(B_363, A_361, A_361, E_364)=k2_enumset1(A_361, B_363, B_363, E_364))), inference(superposition, [status(thm), theory('equality')], [c_10704, c_8410])).
% 12.33/5.24  tff(c_10812, plain, (![B_373, E_374, A_375]: (k1_enumset1(B_373, E_374, A_375)=k1_enumset1(A_375, E_374, B_373))), inference(demodulation, [status(thm), theory('equality')], [c_530, c_530, c_10711])).
% 12.33/5.24  tff(c_538, plain, (![C_62, A_60]: (k1_enumset1(C_62, A_60, A_60)=k1_enumset1(A_60, C_62, C_62))), inference(superposition, [status(thm), theory('equality')], [c_30, c_466])).
% 12.33/5.24  tff(c_10870, plain, (![B_373, A_375]: (k1_enumset1(B_373, B_373, A_375)=k1_enumset1(B_373, A_375, A_375))), inference(superposition, [status(thm), theory('equality')], [c_10812, c_538])).
% 12.33/5.24  tff(c_10937, plain, (![B_373, A_375]: (k1_enumset1(B_373, A_375, A_375)=k2_tarski(B_373, A_375))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_10870])).
% 12.33/5.24  tff(c_10949, plain, (![C_62, A_60]: (k2_tarski(C_62, A_60)=k2_tarski(A_60, C_62))), inference(demodulation, [status(thm), theory('equality')], [c_10937, c_10937, c_538])).
% 12.33/5.24  tff(c_38, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.33/5.24  tff(c_967, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_858, c_38])).
% 12.33/5.24  tff(c_11010, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10949, c_10949, c_967])).
% 12.33/5.24  tff(c_23433, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9006, c_11010])).
% 12.33/5.24  tff(c_23436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_858, c_522, c_10, c_23433])).
% 12.33/5.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.33/5.24  
% 12.33/5.24  Inference rules
% 12.33/5.24  ----------------------
% 12.33/5.24  #Ref     : 0
% 12.33/5.24  #Sup     : 5909
% 12.33/5.24  #Fact    : 0
% 12.33/5.24  #Define  : 0
% 12.33/5.24  #Split   : 0
% 12.33/5.24  #Chain   : 0
% 12.33/5.24  #Close   : 0
% 12.33/5.24  
% 12.33/5.24  Ordering : KBO
% 12.33/5.24  
% 12.33/5.24  Simplification rules
% 12.33/5.24  ----------------------
% 12.33/5.24  #Subsume      : 1959
% 12.33/5.24  #Demod        : 4296
% 12.33/5.24  #Tautology    : 2512
% 12.33/5.24  #SimpNegUnit  : 0
% 12.33/5.24  #BackRed      : 4
% 12.33/5.24  
% 12.33/5.24  #Partial instantiations: 0
% 12.33/5.24  #Strategies tried      : 1
% 12.33/5.24  
% 12.33/5.24  Timing (in seconds)
% 12.33/5.24  ----------------------
% 12.33/5.24  Preprocessing        : 0.33
% 12.33/5.24  Parsing              : 0.17
% 12.33/5.24  CNF conversion       : 0.02
% 12.33/5.24  Main loop            : 4.16
% 12.33/5.24  Inferencing          : 0.82
% 12.33/5.24  Reduction            : 2.69
% 12.33/5.24  Demodulation         : 2.53
% 12.33/5.24  BG Simplification    : 0.10
% 12.33/5.24  Subsumption          : 0.42
% 12.33/5.24  Abstraction          : 0.17
% 12.33/5.24  MUC search           : 0.00
% 12.33/5.24  Cooper               : 0.00
% 12.33/5.24  Total                : 4.52
% 12.33/5.24  Index Insertion      : 0.00
% 12.33/5.24  Index Deletion       : 0.00
% 12.33/5.24  Index Matching       : 0.00
% 12.33/5.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
