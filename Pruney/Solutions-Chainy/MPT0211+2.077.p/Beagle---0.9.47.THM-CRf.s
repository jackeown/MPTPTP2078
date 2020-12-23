%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:25 EST 2020

% Result     : Theorem 11.70s
% Output     : CNFRefutation 11.70s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 220 expanded)
%              Number of leaves         :   28 (  88 expanded)
%              Depth                    :   13
%              Number of atoms          :   46 ( 203 expanded)
%              Number of equality atoms :   45 ( 202 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_51,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_26,plain,(
    ! [A_40,B_41,C_42] : k2_enumset1(A_40,A_40,B_41,C_42) = k1_enumset1(A_40,B_41,C_42) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_10,C_12,D_13,B_11] : k2_enumset1(A_10,C_12,D_13,B_11) = k2_enumset1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ! [A_43,B_44,C_45,D_46] : k3_enumset1(A_43,A_43,B_44,C_45,D_46) = k2_enumset1(A_43,B_44,C_45,D_46) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_38,B_39] : k1_enumset1(A_38,A_38,B_39) = k2_tarski(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [A_47,E_51,D_50,C_49,B_48] : k4_enumset1(A_47,A_47,B_48,C_49,D_50,E_51) = k3_enumset1(A_47,B_48,C_49,D_50,E_51) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1925,plain,(
    ! [C_151,F_150,E_148,A_149,B_147,D_146] : k2_xboole_0(k2_enumset1(A_149,B_147,C_151,D_146),k2_tarski(E_148,F_150)) = k4_enumset1(A_149,B_147,C_151,D_146,E_148,F_150) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1988,plain,(
    ! [C_42,F_150,E_148,A_40,B_41] : k4_enumset1(A_40,A_40,B_41,C_42,E_148,F_150) = k2_xboole_0(k1_enumset1(A_40,B_41,C_42),k2_tarski(E_148,F_150)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1925])).

tff(c_9418,plain,(
    ! [A_263,E_266,B_267,F_265,C_264] : k2_xboole_0(k1_enumset1(A_263,B_267,C_264),k2_tarski(E_266,F_265)) = k3_enumset1(A_263,B_267,C_264,E_266,F_265) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1988])).

tff(c_9445,plain,(
    ! [A_38,B_39,E_266,F_265] : k3_enumset1(A_38,A_38,B_39,E_266,F_265) = k2_xboole_0(k2_tarski(A_38,B_39),k2_tarski(E_266,F_265)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_9418])).

tff(c_9451,plain,(
    ! [A_38,B_39,E_266,F_265] : k2_xboole_0(k2_tarski(A_38,B_39),k2_tarski(E_266,F_265)) = k2_enumset1(A_38,B_39,E_266,F_265) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_9445])).

tff(c_80,plain,(
    ! [D_68,C_69,B_70,A_71] : k2_enumset1(D_68,C_69,B_70,A_71) = k2_enumset1(A_71,B_70,C_69,D_68) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_96,plain,(
    ! [D_68,C_69,B_70] : k2_enumset1(D_68,C_69,B_70,B_70) = k1_enumset1(B_70,C_69,D_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_26])).

tff(c_18,plain,(
    ! [B_27,D_29,A_26,E_30,C_28] : k2_xboole_0(k2_enumset1(A_26,B_27,C_28,D_29),k1_tarski(E_30)) = k3_enumset1(A_26,B_27,C_28,D_29,E_30) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1991,plain,(
    ! [C_151,A_149,A_37,B_147,D_146] : k4_enumset1(A_149,B_147,C_151,D_146,A_37,A_37) = k2_xboole_0(k2_enumset1(A_149,B_147,C_151,D_146),k1_tarski(A_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1925])).

tff(c_7469,plain,(
    ! [D_215,A_214,C_212,B_213,A_211] : k4_enumset1(A_214,B_213,C_212,D_215,A_211,A_211) = k3_enumset1(A_214,B_213,C_212,D_215,A_211) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1991])).

tff(c_7483,plain,(
    ! [A_47,B_48,C_49,E_51] : k3_enumset1(A_47,B_48,C_49,E_51,E_51) = k3_enumset1(A_47,A_47,B_48,C_49,E_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_7469])).

tff(c_11151,plain,(
    ! [A_322,B_323,C_324,E_325] : k3_enumset1(A_322,B_323,C_324,E_325,E_325) = k2_enumset1(A_322,B_323,C_324,E_325) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7483])).

tff(c_11164,plain,(
    ! [B_323,C_324,E_325] : k2_enumset1(B_323,C_324,E_325,E_325) = k2_enumset1(B_323,B_323,C_324,E_325) ),
    inference(superposition,[status(thm),theory(equality)],[c_11151,c_28])).

tff(c_11184,plain,(
    ! [E_326,C_327,B_328] : k1_enumset1(E_326,C_327,B_328) = k1_enumset1(B_328,C_327,E_326) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_26,c_11164])).

tff(c_127,plain,(
    ! [D_72,C_73,B_74] : k2_enumset1(D_72,C_73,B_74,B_74) = k1_enumset1(B_74,C_73,D_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_26])).

tff(c_140,plain,(
    ! [C_73,B_74] : k1_enumset1(C_73,B_74,B_74) = k1_enumset1(B_74,C_73,C_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_26])).

tff(c_11224,plain,(
    ! [E_326,B_328] : k1_enumset1(E_326,E_326,B_328) = k1_enumset1(E_326,B_328,B_328) ),
    inference(superposition,[status(thm),theory(equality)],[c_11184,c_140])).

tff(c_11291,plain,(
    ! [E_326,B_328] : k1_enumset1(E_326,B_328,B_328) = k2_tarski(E_326,B_328) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_11224])).

tff(c_11303,plain,(
    ! [C_73,B_74] : k2_tarski(C_73,B_74) = k2_tarski(B_74,C_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11291,c_11291,c_140])).

tff(c_516,plain,(
    ! [A_93,D_94,C_95,B_96] : k2_enumset1(A_93,D_94,C_95,B_96) = k2_enumset1(A_93,B_96,C_95,D_94) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_748,plain,(
    ! [B_100,D_101,C_102] : k2_enumset1(B_100,D_101,C_102,B_100) = k1_enumset1(B_100,C_102,D_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_516,c_26])).

tff(c_237,plain,(
    ! [A_80,C_81,D_82,B_83] : k2_enumset1(A_80,C_81,D_82,B_83) = k2_enumset1(A_80,B_83,C_81,D_82) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_273,plain,(
    ! [B_83,C_81,D_82] : k2_enumset1(B_83,C_81,D_82,B_83) = k1_enumset1(B_83,C_81,D_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_26])).

tff(c_764,plain,(
    ! [B_100,D_101,C_102] : k1_enumset1(B_100,D_101,C_102) = k1_enumset1(B_100,C_102,D_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_748,c_273])).

tff(c_34,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_861,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_34])).

tff(c_11354,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11303,c_11303,c_861])).

tff(c_17773,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9451,c_11354])).

tff(c_17776,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10,c_10,c_17773])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:58:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.70/4.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.70/4.29  
% 11.70/4.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.70/4.29  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 11.70/4.29  
% 11.70/4.29  %Foreground sorts:
% 11.70/4.29  
% 11.70/4.29  
% 11.70/4.29  %Background operators:
% 11.70/4.29  
% 11.70/4.29  
% 11.70/4.29  %Foreground operators:
% 11.70/4.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.70/4.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.70/4.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.70/4.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.70/4.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.70/4.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.70/4.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.70/4.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.70/4.29  tff('#skF_2', type, '#skF_2': $i).
% 11.70/4.29  tff('#skF_3', type, '#skF_3': $i).
% 11.70/4.29  tff('#skF_1', type, '#skF_1': $i).
% 11.70/4.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.70/4.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.70/4.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.70/4.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.70/4.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.70/4.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.70/4.29  
% 11.70/4.31  tff(f_51, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 11.70/4.31  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 11.70/4.31  tff(f_53, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 11.70/4.31  tff(f_49, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 11.70/4.31  tff(f_55, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 11.70/4.31  tff(f_45, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 11.70/4.31  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 11.70/4.31  tff(f_43, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 11.70/4.31  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 11.70/4.31  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 11.70/4.31  tff(f_60, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 11.70/4.31  tff(c_26, plain, (![A_40, B_41, C_42]: (k2_enumset1(A_40, A_40, B_41, C_42)=k1_enumset1(A_40, B_41, C_42))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.70/4.31  tff(c_10, plain, (![A_10, C_12, D_13, B_11]: (k2_enumset1(A_10, C_12, D_13, B_11)=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.70/4.31  tff(c_28, plain, (![A_43, B_44, C_45, D_46]: (k3_enumset1(A_43, A_43, B_44, C_45, D_46)=k2_enumset1(A_43, B_44, C_45, D_46))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.70/4.31  tff(c_24, plain, (![A_38, B_39]: (k1_enumset1(A_38, A_38, B_39)=k2_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.70/4.31  tff(c_30, plain, (![A_47, E_51, D_50, C_49, B_48]: (k4_enumset1(A_47, A_47, B_48, C_49, D_50, E_51)=k3_enumset1(A_47, B_48, C_49, D_50, E_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.70/4.31  tff(c_1925, plain, (![C_151, F_150, E_148, A_149, B_147, D_146]: (k2_xboole_0(k2_enumset1(A_149, B_147, C_151, D_146), k2_tarski(E_148, F_150))=k4_enumset1(A_149, B_147, C_151, D_146, E_148, F_150))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.70/4.31  tff(c_1988, plain, (![C_42, F_150, E_148, A_40, B_41]: (k4_enumset1(A_40, A_40, B_41, C_42, E_148, F_150)=k2_xboole_0(k1_enumset1(A_40, B_41, C_42), k2_tarski(E_148, F_150)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1925])).
% 11.70/4.31  tff(c_9418, plain, (![A_263, E_266, B_267, F_265, C_264]: (k2_xboole_0(k1_enumset1(A_263, B_267, C_264), k2_tarski(E_266, F_265))=k3_enumset1(A_263, B_267, C_264, E_266, F_265))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1988])).
% 11.70/4.31  tff(c_9445, plain, (![A_38, B_39, E_266, F_265]: (k3_enumset1(A_38, A_38, B_39, E_266, F_265)=k2_xboole_0(k2_tarski(A_38, B_39), k2_tarski(E_266, F_265)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_9418])).
% 11.70/4.31  tff(c_9451, plain, (![A_38, B_39, E_266, F_265]: (k2_xboole_0(k2_tarski(A_38, B_39), k2_tarski(E_266, F_265))=k2_enumset1(A_38, B_39, E_266, F_265))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_9445])).
% 11.70/4.31  tff(c_80, plain, (![D_68, C_69, B_70, A_71]: (k2_enumset1(D_68, C_69, B_70, A_71)=k2_enumset1(A_71, B_70, C_69, D_68))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.70/4.31  tff(c_96, plain, (![D_68, C_69, B_70]: (k2_enumset1(D_68, C_69, B_70, B_70)=k1_enumset1(B_70, C_69, D_68))), inference(superposition, [status(thm), theory('equality')], [c_80, c_26])).
% 11.70/4.31  tff(c_18, plain, (![B_27, D_29, A_26, E_30, C_28]: (k2_xboole_0(k2_enumset1(A_26, B_27, C_28, D_29), k1_tarski(E_30))=k3_enumset1(A_26, B_27, C_28, D_29, E_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.70/4.31  tff(c_22, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.70/4.31  tff(c_1991, plain, (![C_151, A_149, A_37, B_147, D_146]: (k4_enumset1(A_149, B_147, C_151, D_146, A_37, A_37)=k2_xboole_0(k2_enumset1(A_149, B_147, C_151, D_146), k1_tarski(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1925])).
% 11.70/4.31  tff(c_7469, plain, (![D_215, A_214, C_212, B_213, A_211]: (k4_enumset1(A_214, B_213, C_212, D_215, A_211, A_211)=k3_enumset1(A_214, B_213, C_212, D_215, A_211))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1991])).
% 11.70/4.31  tff(c_7483, plain, (![A_47, B_48, C_49, E_51]: (k3_enumset1(A_47, B_48, C_49, E_51, E_51)=k3_enumset1(A_47, A_47, B_48, C_49, E_51))), inference(superposition, [status(thm), theory('equality')], [c_30, c_7469])).
% 11.70/4.31  tff(c_11151, plain, (![A_322, B_323, C_324, E_325]: (k3_enumset1(A_322, B_323, C_324, E_325, E_325)=k2_enumset1(A_322, B_323, C_324, E_325))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_7483])).
% 11.70/4.31  tff(c_11164, plain, (![B_323, C_324, E_325]: (k2_enumset1(B_323, C_324, E_325, E_325)=k2_enumset1(B_323, B_323, C_324, E_325))), inference(superposition, [status(thm), theory('equality')], [c_11151, c_28])).
% 11.70/4.31  tff(c_11184, plain, (![E_326, C_327, B_328]: (k1_enumset1(E_326, C_327, B_328)=k1_enumset1(B_328, C_327, E_326))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_26, c_11164])).
% 11.70/4.31  tff(c_127, plain, (![D_72, C_73, B_74]: (k2_enumset1(D_72, C_73, B_74, B_74)=k1_enumset1(B_74, C_73, D_72))), inference(superposition, [status(thm), theory('equality')], [c_80, c_26])).
% 11.70/4.31  tff(c_140, plain, (![C_73, B_74]: (k1_enumset1(C_73, B_74, B_74)=k1_enumset1(B_74, C_73, C_73))), inference(superposition, [status(thm), theory('equality')], [c_127, c_26])).
% 11.70/4.31  tff(c_11224, plain, (![E_326, B_328]: (k1_enumset1(E_326, E_326, B_328)=k1_enumset1(E_326, B_328, B_328))), inference(superposition, [status(thm), theory('equality')], [c_11184, c_140])).
% 11.70/4.31  tff(c_11291, plain, (![E_326, B_328]: (k1_enumset1(E_326, B_328, B_328)=k2_tarski(E_326, B_328))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_11224])).
% 11.70/4.31  tff(c_11303, plain, (![C_73, B_74]: (k2_tarski(C_73, B_74)=k2_tarski(B_74, C_73))), inference(demodulation, [status(thm), theory('equality')], [c_11291, c_11291, c_140])).
% 11.70/4.31  tff(c_516, plain, (![A_93, D_94, C_95, B_96]: (k2_enumset1(A_93, D_94, C_95, B_96)=k2_enumset1(A_93, B_96, C_95, D_94))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.70/4.31  tff(c_748, plain, (![B_100, D_101, C_102]: (k2_enumset1(B_100, D_101, C_102, B_100)=k1_enumset1(B_100, C_102, D_101))), inference(superposition, [status(thm), theory('equality')], [c_516, c_26])).
% 11.70/4.31  tff(c_237, plain, (![A_80, C_81, D_82, B_83]: (k2_enumset1(A_80, C_81, D_82, B_83)=k2_enumset1(A_80, B_83, C_81, D_82))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.70/4.31  tff(c_273, plain, (![B_83, C_81, D_82]: (k2_enumset1(B_83, C_81, D_82, B_83)=k1_enumset1(B_83, C_81, D_82))), inference(superposition, [status(thm), theory('equality')], [c_237, c_26])).
% 11.70/4.31  tff(c_764, plain, (![B_100, D_101, C_102]: (k1_enumset1(B_100, D_101, C_102)=k1_enumset1(B_100, C_102, D_101))), inference(superposition, [status(thm), theory('equality')], [c_748, c_273])).
% 11.70/4.31  tff(c_34, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.70/4.31  tff(c_861, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_764, c_34])).
% 11.70/4.31  tff(c_11354, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11303, c_11303, c_861])).
% 11.70/4.31  tff(c_17773, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9451, c_11354])).
% 11.70/4.31  tff(c_17776, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_10, c_10, c_17773])).
% 11.70/4.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.70/4.31  
% 11.70/4.31  Inference rules
% 11.70/4.31  ----------------------
% 11.70/4.31  #Ref     : 0
% 11.70/4.31  #Sup     : 4607
% 11.70/4.31  #Fact    : 0
% 11.70/4.31  #Define  : 0
% 11.70/4.31  #Split   : 0
% 11.70/4.31  #Chain   : 0
% 11.70/4.31  #Close   : 0
% 11.70/4.31  
% 11.70/4.31  Ordering : KBO
% 11.70/4.31  
% 11.70/4.31  Simplification rules
% 11.70/4.31  ----------------------
% 11.70/4.31  #Subsume      : 1488
% 11.70/4.31  #Demod        : 2867
% 11.70/4.31  #Tautology    : 1932
% 11.70/4.31  #SimpNegUnit  : 0
% 11.70/4.31  #BackRed      : 4
% 11.70/4.31  
% 11.70/4.31  #Partial instantiations: 0
% 11.70/4.31  #Strategies tried      : 1
% 11.70/4.31  
% 11.70/4.31  Timing (in seconds)
% 11.70/4.31  ----------------------
% 11.70/4.31  Preprocessing        : 0.32
% 11.70/4.31  Parsing              : 0.17
% 11.70/4.31  CNF conversion       : 0.02
% 11.70/4.31  Main loop            : 3.21
% 11.70/4.31  Inferencing          : 0.68
% 11.70/4.31  Reduction            : 2.02
% 11.70/4.31  Demodulation         : 1.89
% 11.70/4.31  BG Simplification    : 0.08
% 11.70/4.31  Subsumption          : 0.32
% 11.70/4.31  Abstraction          : 0.14
% 11.70/4.31  MUC search           : 0.00
% 11.70/4.31  Cooper               : 0.00
% 11.70/4.31  Total                : 3.57
% 11.70/4.31  Index Insertion      : 0.00
% 11.70/4.31  Index Deletion       : 0.00
% 11.70/4.31  Index Matching       : 0.00
% 11.70/4.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
