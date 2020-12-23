%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:11 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   55 (  93 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :   38 (  76 expanded)
%              Number of equality atoms :   37 (  75 expanded)
%              Maximal formula depth    :    9 (   5 average)
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

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_8,plain,(
    ! [A_11,B_12,C_13] : k2_xboole_0(k2_tarski(A_11,B_12),k1_tarski(C_13)) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [A_49] : k2_tarski(A_49,A_49) = k1_tarski(A_49) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_50,B_51] : k1_enumset1(A_50,A_50,B_51) = k2_tarski(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_118,plain,(
    ! [D_74,B_75,E_73,C_72,A_71] : k2_xboole_0(k2_tarski(A_71,B_75),k1_enumset1(C_72,D_74,E_73)) = k3_enumset1(A_71,B_75,C_72,D_74,E_73) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_161,plain,(
    ! [A_82,B_83,A_84,B_85] : k3_enumset1(A_82,B_83,A_84,A_84,B_85) = k2_xboole_0(k2_tarski(A_82,B_83),k2_tarski(A_84,B_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_118])).

tff(c_184,plain,(
    ! [A_49,A_84,B_85] : k3_enumset1(A_49,A_49,A_84,A_84,B_85) = k2_xboole_0(k1_tarski(A_49),k2_tarski(A_84,B_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_161])).

tff(c_12,plain,(
    ! [E_22,D_21,A_18,C_20,B_19] : k2_xboole_0(k2_tarski(A_18,B_19),k1_enumset1(C_20,D_21,E_22)) = k3_enumset1(A_18,B_19,C_20,D_21,E_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_387,plain,(
    ! [C_110,F_108,A_111,D_107,B_109,E_112] : k2_xboole_0(k1_enumset1(A_111,B_109,C_110),k1_enumset1(D_107,E_112,F_108)) = k4_enumset1(A_111,B_109,C_110,D_107,E_112,F_108) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_396,plain,(
    ! [A_50,F_108,B_51,D_107,E_112] : k4_enumset1(A_50,A_50,B_51,D_107,E_112,F_108) = k2_xboole_0(k2_tarski(A_50,B_51),k1_enumset1(D_107,E_112,F_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_387])).

tff(c_403,plain,(
    ! [B_115,F_117,E_116,D_113,A_114] : k4_enumset1(A_114,A_114,B_115,D_113,E_116,F_117) = k3_enumset1(A_114,B_115,D_113,E_116,F_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_396])).

tff(c_187,plain,(
    ! [A_82,B_83,A_49] : k3_enumset1(A_82,B_83,A_49,A_49,A_49) = k2_xboole_0(k2_tarski(A_82,B_83),k1_tarski(A_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_161])).

tff(c_194,plain,(
    ! [A_82,B_83,A_49] : k3_enumset1(A_82,B_83,A_49,A_49,A_49) = k1_enumset1(A_82,B_83,A_49) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_187])).

tff(c_278,plain,(
    ! [D_92,F_95,C_97,E_96,B_93,A_94] : k2_xboole_0(k3_enumset1(A_94,B_93,C_97,D_92,E_96),k1_tarski(F_95)) = k4_enumset1(A_94,B_93,C_97,D_92,E_96,F_95) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_290,plain,(
    ! [A_82,B_83,A_49,F_95] : k4_enumset1(A_82,B_83,A_49,A_49,A_49,F_95) = k2_xboole_0(k1_enumset1(A_82,B_83,A_49),k1_tarski(F_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_278])).

tff(c_410,plain,(
    ! [A_114,E_116,F_117] : k3_enumset1(A_114,E_116,E_116,E_116,F_117) = k2_xboole_0(k1_enumset1(A_114,A_114,E_116),k1_tarski(F_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_290])).

tff(c_429,plain,(
    ! [A_118,E_119,F_120] : k3_enumset1(A_118,E_119,E_119,E_119,F_120) = k1_enumset1(A_118,E_119,F_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_24,c_410])).

tff(c_443,plain,(
    ! [E_119,F_120] : k2_xboole_0(k1_tarski(E_119),k2_tarski(E_119,F_120)) = k1_enumset1(E_119,E_119,F_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_184])).

tff(c_582,plain,(
    ! [E_130,F_131] : k2_xboole_0(k1_tarski(E_130),k2_tarski(E_130,F_131)) = k2_tarski(E_130,F_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_443])).

tff(c_650,plain,(
    ! [A_140,B_141] : k3_enumset1(A_140,A_140,A_140,A_140,B_141) = k2_tarski(A_140,B_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_582])).

tff(c_16,plain,(
    ! [E_33,A_29,F_34,D_32,C_31,B_30] : k2_xboole_0(k3_enumset1(A_29,B_30,C_31,D_32,E_33),k1_tarski(F_34)) = k4_enumset1(A_29,B_30,C_31,D_32,E_33,F_34) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_666,plain,(
    ! [A_140,B_141,F_34] : k4_enumset1(A_140,A_140,A_140,A_140,B_141,F_34) = k2_xboole_0(k2_tarski(A_140,B_141),k1_tarski(F_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_16])).

tff(c_1655,plain,(
    ! [A_186,B_187,F_188] : k4_enumset1(A_186,A_186,A_186,A_186,B_187,F_188) = k1_enumset1(A_186,B_187,F_188) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_666])).

tff(c_402,plain,(
    ! [A_50,F_108,B_51,D_107,E_112] : k4_enumset1(A_50,A_50,B_51,D_107,E_112,F_108) = k3_enumset1(A_50,B_51,D_107,E_112,F_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_396])).

tff(c_1774,plain,(
    ! [A_189,B_190,F_191] : k3_enumset1(A_189,A_189,A_189,B_190,F_191) = k1_enumset1(A_189,B_190,F_191) ),
    inference(superposition,[status(thm),theory(equality)],[c_1655,c_402])).

tff(c_10,plain,(
    ! [A_14,B_15,C_16,D_17] : k2_xboole_0(k1_tarski(A_14),k1_enumset1(B_15,C_16,D_17)) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_130,plain,(
    ! [A_49,C_72,D_74,E_73] : k3_enumset1(A_49,A_49,C_72,D_74,E_73) = k2_xboole_0(k1_tarski(A_49),k1_enumset1(C_72,D_74,E_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_118])).

tff(c_133,plain,(
    ! [A_49,C_72,D_74,E_73] : k3_enumset1(A_49,A_49,C_72,D_74,E_73) = k2_enumset1(A_49,C_72,D_74,E_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_130])).

tff(c_1817,plain,(
    ! [A_189,B_190,F_191] : k2_enumset1(A_189,A_189,B_190,F_191) = k1_enumset1(A_189,B_190,F_191) ),
    inference(superposition,[status(thm),theory(equality)],[c_1774,c_133])).

tff(c_26,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1870,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1817,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.55  
% 3.32/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.55  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.32/1.55  
% 3.32/1.55  %Foreground sorts:
% 3.32/1.55  
% 3.32/1.55  
% 3.32/1.55  %Background operators:
% 3.32/1.55  
% 3.32/1.55  
% 3.32/1.55  %Foreground operators:
% 3.32/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.32/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.32/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.32/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.32/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.32/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.32/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.32/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.32/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.32/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.32/1.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.32/1.55  
% 3.32/1.56  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 3.32/1.56  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.32/1.56  tff(f_49, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.32/1.56  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 3.32/1.56  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 3.32/1.56  tff(f_41, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 3.32/1.56  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 3.32/1.56  tff(f_52, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.32/1.56  tff(c_8, plain, (![A_11, B_12, C_13]: (k2_xboole_0(k2_tarski(A_11, B_12), k1_tarski(C_13))=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.32/1.56  tff(c_22, plain, (![A_49]: (k2_tarski(A_49, A_49)=k1_tarski(A_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.32/1.56  tff(c_24, plain, (![A_50, B_51]: (k1_enumset1(A_50, A_50, B_51)=k2_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.32/1.56  tff(c_118, plain, (![D_74, B_75, E_73, C_72, A_71]: (k2_xboole_0(k2_tarski(A_71, B_75), k1_enumset1(C_72, D_74, E_73))=k3_enumset1(A_71, B_75, C_72, D_74, E_73))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.32/1.56  tff(c_161, plain, (![A_82, B_83, A_84, B_85]: (k3_enumset1(A_82, B_83, A_84, A_84, B_85)=k2_xboole_0(k2_tarski(A_82, B_83), k2_tarski(A_84, B_85)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_118])).
% 3.32/1.56  tff(c_184, plain, (![A_49, A_84, B_85]: (k3_enumset1(A_49, A_49, A_84, A_84, B_85)=k2_xboole_0(k1_tarski(A_49), k2_tarski(A_84, B_85)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_161])).
% 3.32/1.56  tff(c_12, plain, (![E_22, D_21, A_18, C_20, B_19]: (k2_xboole_0(k2_tarski(A_18, B_19), k1_enumset1(C_20, D_21, E_22))=k3_enumset1(A_18, B_19, C_20, D_21, E_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.32/1.56  tff(c_387, plain, (![C_110, F_108, A_111, D_107, B_109, E_112]: (k2_xboole_0(k1_enumset1(A_111, B_109, C_110), k1_enumset1(D_107, E_112, F_108))=k4_enumset1(A_111, B_109, C_110, D_107, E_112, F_108))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.56  tff(c_396, plain, (![A_50, F_108, B_51, D_107, E_112]: (k4_enumset1(A_50, A_50, B_51, D_107, E_112, F_108)=k2_xboole_0(k2_tarski(A_50, B_51), k1_enumset1(D_107, E_112, F_108)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_387])).
% 3.32/1.56  tff(c_403, plain, (![B_115, F_117, E_116, D_113, A_114]: (k4_enumset1(A_114, A_114, B_115, D_113, E_116, F_117)=k3_enumset1(A_114, B_115, D_113, E_116, F_117))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_396])).
% 3.32/1.56  tff(c_187, plain, (![A_82, B_83, A_49]: (k3_enumset1(A_82, B_83, A_49, A_49, A_49)=k2_xboole_0(k2_tarski(A_82, B_83), k1_tarski(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_161])).
% 3.32/1.56  tff(c_194, plain, (![A_82, B_83, A_49]: (k3_enumset1(A_82, B_83, A_49, A_49, A_49)=k1_enumset1(A_82, B_83, A_49))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_187])).
% 3.32/1.56  tff(c_278, plain, (![D_92, F_95, C_97, E_96, B_93, A_94]: (k2_xboole_0(k3_enumset1(A_94, B_93, C_97, D_92, E_96), k1_tarski(F_95))=k4_enumset1(A_94, B_93, C_97, D_92, E_96, F_95))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.32/1.56  tff(c_290, plain, (![A_82, B_83, A_49, F_95]: (k4_enumset1(A_82, B_83, A_49, A_49, A_49, F_95)=k2_xboole_0(k1_enumset1(A_82, B_83, A_49), k1_tarski(F_95)))), inference(superposition, [status(thm), theory('equality')], [c_194, c_278])).
% 3.32/1.56  tff(c_410, plain, (![A_114, E_116, F_117]: (k3_enumset1(A_114, E_116, E_116, E_116, F_117)=k2_xboole_0(k1_enumset1(A_114, A_114, E_116), k1_tarski(F_117)))), inference(superposition, [status(thm), theory('equality')], [c_403, c_290])).
% 3.32/1.56  tff(c_429, plain, (![A_118, E_119, F_120]: (k3_enumset1(A_118, E_119, E_119, E_119, F_120)=k1_enumset1(A_118, E_119, F_120))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_24, c_410])).
% 3.32/1.56  tff(c_443, plain, (![E_119, F_120]: (k2_xboole_0(k1_tarski(E_119), k2_tarski(E_119, F_120))=k1_enumset1(E_119, E_119, F_120))), inference(superposition, [status(thm), theory('equality')], [c_429, c_184])).
% 3.32/1.56  tff(c_582, plain, (![E_130, F_131]: (k2_xboole_0(k1_tarski(E_130), k2_tarski(E_130, F_131))=k2_tarski(E_130, F_131))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_443])).
% 3.32/1.56  tff(c_650, plain, (![A_140, B_141]: (k3_enumset1(A_140, A_140, A_140, A_140, B_141)=k2_tarski(A_140, B_141))), inference(superposition, [status(thm), theory('equality')], [c_184, c_582])).
% 3.32/1.56  tff(c_16, plain, (![E_33, A_29, F_34, D_32, C_31, B_30]: (k2_xboole_0(k3_enumset1(A_29, B_30, C_31, D_32, E_33), k1_tarski(F_34))=k4_enumset1(A_29, B_30, C_31, D_32, E_33, F_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.32/1.56  tff(c_666, plain, (![A_140, B_141, F_34]: (k4_enumset1(A_140, A_140, A_140, A_140, B_141, F_34)=k2_xboole_0(k2_tarski(A_140, B_141), k1_tarski(F_34)))), inference(superposition, [status(thm), theory('equality')], [c_650, c_16])).
% 3.32/1.56  tff(c_1655, plain, (![A_186, B_187, F_188]: (k4_enumset1(A_186, A_186, A_186, A_186, B_187, F_188)=k1_enumset1(A_186, B_187, F_188))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_666])).
% 3.32/1.56  tff(c_402, plain, (![A_50, F_108, B_51, D_107, E_112]: (k4_enumset1(A_50, A_50, B_51, D_107, E_112, F_108)=k3_enumset1(A_50, B_51, D_107, E_112, F_108))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_396])).
% 3.32/1.56  tff(c_1774, plain, (![A_189, B_190, F_191]: (k3_enumset1(A_189, A_189, A_189, B_190, F_191)=k1_enumset1(A_189, B_190, F_191))), inference(superposition, [status(thm), theory('equality')], [c_1655, c_402])).
% 3.32/1.56  tff(c_10, plain, (![A_14, B_15, C_16, D_17]: (k2_xboole_0(k1_tarski(A_14), k1_enumset1(B_15, C_16, D_17))=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.32/1.56  tff(c_130, plain, (![A_49, C_72, D_74, E_73]: (k3_enumset1(A_49, A_49, C_72, D_74, E_73)=k2_xboole_0(k1_tarski(A_49), k1_enumset1(C_72, D_74, E_73)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_118])).
% 3.32/1.56  tff(c_133, plain, (![A_49, C_72, D_74, E_73]: (k3_enumset1(A_49, A_49, C_72, D_74, E_73)=k2_enumset1(A_49, C_72, D_74, E_73))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_130])).
% 3.32/1.56  tff(c_1817, plain, (![A_189, B_190, F_191]: (k2_enumset1(A_189, A_189, B_190, F_191)=k1_enumset1(A_189, B_190, F_191))), inference(superposition, [status(thm), theory('equality')], [c_1774, c_133])).
% 3.32/1.56  tff(c_26, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.32/1.56  tff(c_1870, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1817, c_26])).
% 3.32/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.56  
% 3.32/1.56  Inference rules
% 3.32/1.56  ----------------------
% 3.32/1.56  #Ref     : 0
% 3.32/1.56  #Sup     : 420
% 3.32/1.56  #Fact    : 0
% 3.32/1.56  #Define  : 0
% 3.32/1.56  #Split   : 0
% 3.32/1.56  #Chain   : 0
% 3.32/1.56  #Close   : 0
% 3.32/1.56  
% 3.32/1.56  Ordering : KBO
% 3.32/1.56  
% 3.32/1.56  Simplification rules
% 3.32/1.56  ----------------------
% 3.32/1.56  #Subsume      : 6
% 3.32/1.56  #Demod        : 491
% 3.32/1.56  #Tautology    : 321
% 3.32/1.56  #SimpNegUnit  : 0
% 3.32/1.56  #BackRed      : 1
% 3.32/1.56  
% 3.32/1.56  #Partial instantiations: 0
% 3.32/1.56  #Strategies tried      : 1
% 3.32/1.56  
% 3.32/1.56  Timing (in seconds)
% 3.32/1.56  ----------------------
% 3.48/1.57  Preprocessing        : 0.30
% 3.48/1.57  Parsing              : 0.17
% 3.48/1.57  CNF conversion       : 0.02
% 3.48/1.57  Main loop            : 0.45
% 3.48/1.57  Inferencing          : 0.19
% 3.48/1.57  Reduction            : 0.18
% 3.48/1.57  Demodulation         : 0.15
% 3.48/1.57  BG Simplification    : 0.02
% 3.48/1.57  Subsumption          : 0.04
% 3.48/1.57  Abstraction          : 0.03
% 3.48/1.57  MUC search           : 0.00
% 3.48/1.57  Cooper               : 0.00
% 3.48/1.57  Total                : 0.78
% 3.48/1.57  Index Insertion      : 0.00
% 3.48/1.57  Index Deletion       : 0.00
% 3.48/1.57  Index Matching       : 0.00
% 3.48/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
