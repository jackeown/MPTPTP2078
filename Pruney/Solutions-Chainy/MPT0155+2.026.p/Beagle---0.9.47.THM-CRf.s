%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:12 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   49 (  72 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   33 (  56 expanded)
%              Number of equality atoms :   32 (  55 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_8,plain,(
    ! [A_12,B_13,C_14,D_15] : k2_xboole_0(k1_tarski(A_12),k1_enumset1(B_13,C_14,D_15)) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [A_47] : k2_tarski(A_47,A_47) = k1_tarski(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_125,plain,(
    ! [C_73,E_70,D_72,B_69,A_71] : k2_xboole_0(k2_tarski(A_71,B_69),k1_enumset1(C_73,D_72,E_70)) = k3_enumset1(A_71,B_69,C_73,D_72,E_70) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_137,plain,(
    ! [A_47,C_73,D_72,E_70] : k3_enumset1(A_47,A_47,C_73,D_72,E_70) = k2_xboole_0(k1_tarski(A_47),k1_enumset1(C_73,D_72,E_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_125])).

tff(c_140,plain,(
    ! [A_47,C_73,D_72,E_70] : k3_enumset1(A_47,A_47,C_73,D_72,E_70) = k2_enumset1(A_47,C_73,D_72,E_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_137])).

tff(c_6,plain,(
    ! [A_9,B_10,C_11] : k2_xboole_0(k2_tarski(A_9,B_10),k1_tarski(C_11)) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_48,B_49] : k1_enumset1(A_48,A_48,B_49) = k2_tarski(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [C_18,B_17,A_16,D_19,E_20] : k2_xboole_0(k2_tarski(A_16,B_17),k1_enumset1(C_18,D_19,E_20)) = k3_enumset1(A_16,B_17,C_18,D_19,E_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_419,plain,(
    ! [E_108,D_109,A_111,F_110,B_113,C_112] : k2_xboole_0(k1_enumset1(A_111,B_113,C_112),k1_enumset1(D_109,E_108,F_110)) = k4_enumset1(A_111,B_113,C_112,D_109,E_108,F_110) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_428,plain,(
    ! [E_108,D_109,B_49,A_48,F_110] : k4_enumset1(A_48,A_48,B_49,D_109,E_108,F_110) = k2_xboole_0(k2_tarski(A_48,B_49),k1_enumset1(D_109,E_108,F_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_419])).

tff(c_436,plain,(
    ! [B_115,A_116,F_117,D_118,E_114] : k4_enumset1(A_116,A_116,B_115,D_118,E_114,F_117) = k3_enumset1(A_116,B_115,D_118,E_114,F_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_428])).

tff(c_150,plain,(
    ! [A_78,B_79,A_80,B_81] : k3_enumset1(A_78,B_79,A_80,A_80,B_81) = k2_xboole_0(k2_tarski(A_78,B_79),k2_tarski(A_80,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_125])).

tff(c_176,plain,(
    ! [A_78,B_79,A_47] : k3_enumset1(A_78,B_79,A_47,A_47,A_47) = k2_xboole_0(k2_tarski(A_78,B_79),k1_tarski(A_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_150])).

tff(c_183,plain,(
    ! [A_78,B_79,A_47] : k3_enumset1(A_78,B_79,A_47,A_47,A_47) = k1_enumset1(A_78,B_79,A_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_176])).

tff(c_312,plain,(
    ! [D_92,A_95,B_94,F_90,C_91,E_93] : k2_xboole_0(k3_enumset1(A_95,B_94,C_91,D_92,E_93),k1_tarski(F_90)) = k4_enumset1(A_95,B_94,C_91,D_92,E_93,F_90) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_327,plain,(
    ! [A_78,B_79,A_47,F_90] : k4_enumset1(A_78,B_79,A_47,A_47,A_47,F_90) = k2_xboole_0(k1_enumset1(A_78,B_79,A_47),k1_tarski(F_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_312])).

tff(c_443,plain,(
    ! [A_116,E_114,F_117] : k3_enumset1(A_116,E_114,E_114,E_114,F_117) = k2_xboole_0(k1_enumset1(A_116,A_116,E_114),k1_tarski(F_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_327])).

tff(c_462,plain,(
    ! [A_119,E_120,F_121] : k3_enumset1(A_119,E_120,E_120,E_120,F_121) = k1_enumset1(A_119,E_120,F_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_22,c_443])).

tff(c_14,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] : k2_xboole_0(k3_enumset1(A_27,B_28,C_29,D_30,E_31),k1_tarski(F_32)) = k4_enumset1(A_27,B_28,C_29,D_30,E_31,F_32) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1375,plain,(
    ! [A_181,E_182,F_183,F_184] : k4_enumset1(A_181,E_182,E_182,E_182,F_183,F_184) = k2_xboole_0(k1_enumset1(A_181,E_182,F_183),k1_tarski(F_184)) ),
    inference(superposition,[status(thm),theory(equality)],[c_462,c_14])).

tff(c_434,plain,(
    ! [E_108,D_109,B_49,A_48,F_110] : k4_enumset1(A_48,A_48,B_49,D_109,E_108,F_110) = k3_enumset1(A_48,B_49,D_109,E_108,F_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_428])).

tff(c_1409,plain,(
    ! [E_182,F_183,F_184] : k3_enumset1(E_182,E_182,E_182,F_183,F_184) = k2_xboole_0(k1_enumset1(E_182,E_182,F_183),k1_tarski(F_184)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1375,c_434])).

tff(c_1475,plain,(
    ! [E_182,F_183,F_184] : k2_enumset1(E_182,E_182,F_183,F_184) = k1_enumset1(E_182,F_183,F_184) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_6,c_22,c_1409])).

tff(c_24,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1475,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:30:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.55  
% 3.22/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.55  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.22/1.55  
% 3.22/1.55  %Foreground sorts:
% 3.22/1.55  
% 3.22/1.55  
% 3.22/1.55  %Background operators:
% 3.22/1.55  
% 3.22/1.55  
% 3.22/1.55  %Foreground operators:
% 3.22/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.22/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.22/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.22/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.22/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.22/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.22/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.22/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.22/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.22/1.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.55  
% 3.22/1.56  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 3.22/1.56  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.22/1.56  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 3.22/1.56  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 3.22/1.56  tff(f_47, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.22/1.56  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 3.22/1.56  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 3.22/1.56  tff(f_50, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.22/1.56  tff(c_8, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k1_tarski(A_12), k1_enumset1(B_13, C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.22/1.56  tff(c_20, plain, (![A_47]: (k2_tarski(A_47, A_47)=k1_tarski(A_47))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.22/1.56  tff(c_125, plain, (![C_73, E_70, D_72, B_69, A_71]: (k2_xboole_0(k2_tarski(A_71, B_69), k1_enumset1(C_73, D_72, E_70))=k3_enumset1(A_71, B_69, C_73, D_72, E_70))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.56  tff(c_137, plain, (![A_47, C_73, D_72, E_70]: (k3_enumset1(A_47, A_47, C_73, D_72, E_70)=k2_xboole_0(k1_tarski(A_47), k1_enumset1(C_73, D_72, E_70)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_125])).
% 3.22/1.56  tff(c_140, plain, (![A_47, C_73, D_72, E_70]: (k3_enumset1(A_47, A_47, C_73, D_72, E_70)=k2_enumset1(A_47, C_73, D_72, E_70))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_137])).
% 3.22/1.56  tff(c_6, plain, (![A_9, B_10, C_11]: (k2_xboole_0(k2_tarski(A_9, B_10), k1_tarski(C_11))=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.56  tff(c_22, plain, (![A_48, B_49]: (k1_enumset1(A_48, A_48, B_49)=k2_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.22/1.56  tff(c_10, plain, (![C_18, B_17, A_16, D_19, E_20]: (k2_xboole_0(k2_tarski(A_16, B_17), k1_enumset1(C_18, D_19, E_20))=k3_enumset1(A_16, B_17, C_18, D_19, E_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.56  tff(c_419, plain, (![E_108, D_109, A_111, F_110, B_113, C_112]: (k2_xboole_0(k1_enumset1(A_111, B_113, C_112), k1_enumset1(D_109, E_108, F_110))=k4_enumset1(A_111, B_113, C_112, D_109, E_108, F_110))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.22/1.56  tff(c_428, plain, (![E_108, D_109, B_49, A_48, F_110]: (k4_enumset1(A_48, A_48, B_49, D_109, E_108, F_110)=k2_xboole_0(k2_tarski(A_48, B_49), k1_enumset1(D_109, E_108, F_110)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_419])).
% 3.22/1.56  tff(c_436, plain, (![B_115, A_116, F_117, D_118, E_114]: (k4_enumset1(A_116, A_116, B_115, D_118, E_114, F_117)=k3_enumset1(A_116, B_115, D_118, E_114, F_117))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_428])).
% 3.22/1.56  tff(c_150, plain, (![A_78, B_79, A_80, B_81]: (k3_enumset1(A_78, B_79, A_80, A_80, B_81)=k2_xboole_0(k2_tarski(A_78, B_79), k2_tarski(A_80, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_125])).
% 3.22/1.56  tff(c_176, plain, (![A_78, B_79, A_47]: (k3_enumset1(A_78, B_79, A_47, A_47, A_47)=k2_xboole_0(k2_tarski(A_78, B_79), k1_tarski(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_150])).
% 3.22/1.56  tff(c_183, plain, (![A_78, B_79, A_47]: (k3_enumset1(A_78, B_79, A_47, A_47, A_47)=k1_enumset1(A_78, B_79, A_47))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_176])).
% 3.22/1.56  tff(c_312, plain, (![D_92, A_95, B_94, F_90, C_91, E_93]: (k2_xboole_0(k3_enumset1(A_95, B_94, C_91, D_92, E_93), k1_tarski(F_90))=k4_enumset1(A_95, B_94, C_91, D_92, E_93, F_90))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.22/1.56  tff(c_327, plain, (![A_78, B_79, A_47, F_90]: (k4_enumset1(A_78, B_79, A_47, A_47, A_47, F_90)=k2_xboole_0(k1_enumset1(A_78, B_79, A_47), k1_tarski(F_90)))), inference(superposition, [status(thm), theory('equality')], [c_183, c_312])).
% 3.22/1.56  tff(c_443, plain, (![A_116, E_114, F_117]: (k3_enumset1(A_116, E_114, E_114, E_114, F_117)=k2_xboole_0(k1_enumset1(A_116, A_116, E_114), k1_tarski(F_117)))), inference(superposition, [status(thm), theory('equality')], [c_436, c_327])).
% 3.22/1.56  tff(c_462, plain, (![A_119, E_120, F_121]: (k3_enumset1(A_119, E_120, E_120, E_120, F_121)=k1_enumset1(A_119, E_120, F_121))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_22, c_443])).
% 3.22/1.56  tff(c_14, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (k2_xboole_0(k3_enumset1(A_27, B_28, C_29, D_30, E_31), k1_tarski(F_32))=k4_enumset1(A_27, B_28, C_29, D_30, E_31, F_32))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.22/1.56  tff(c_1375, plain, (![A_181, E_182, F_183, F_184]: (k4_enumset1(A_181, E_182, E_182, E_182, F_183, F_184)=k2_xboole_0(k1_enumset1(A_181, E_182, F_183), k1_tarski(F_184)))), inference(superposition, [status(thm), theory('equality')], [c_462, c_14])).
% 3.22/1.56  tff(c_434, plain, (![E_108, D_109, B_49, A_48, F_110]: (k4_enumset1(A_48, A_48, B_49, D_109, E_108, F_110)=k3_enumset1(A_48, B_49, D_109, E_108, F_110))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_428])).
% 3.22/1.56  tff(c_1409, plain, (![E_182, F_183, F_184]: (k3_enumset1(E_182, E_182, E_182, F_183, F_184)=k2_xboole_0(k1_enumset1(E_182, E_182, F_183), k1_tarski(F_184)))), inference(superposition, [status(thm), theory('equality')], [c_1375, c_434])).
% 3.22/1.56  tff(c_1475, plain, (![E_182, F_183, F_184]: (k2_enumset1(E_182, E_182, F_183, F_184)=k1_enumset1(E_182, F_183, F_184))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_6, c_22, c_1409])).
% 3.22/1.56  tff(c_24, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.22/1.56  tff(c_1492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1475, c_24])).
% 3.22/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.56  
% 3.22/1.56  Inference rules
% 3.22/1.56  ----------------------
% 3.22/1.56  #Ref     : 0
% 3.22/1.56  #Sup     : 337
% 3.22/1.56  #Fact    : 0
% 3.22/1.56  #Define  : 0
% 3.22/1.56  #Split   : 0
% 3.22/1.56  #Chain   : 0
% 3.22/1.56  #Close   : 0
% 3.22/1.56  
% 3.22/1.56  Ordering : KBO
% 3.22/1.56  
% 3.22/1.56  Simplification rules
% 3.22/1.56  ----------------------
% 3.22/1.56  #Subsume      : 4
% 3.22/1.56  #Demod        : 348
% 3.22/1.56  #Tautology    : 253
% 3.22/1.56  #SimpNegUnit  : 0
% 3.22/1.57  #BackRed      : 2
% 3.22/1.57  
% 3.22/1.57  #Partial instantiations: 0
% 3.22/1.57  #Strategies tried      : 1
% 3.22/1.57  
% 3.22/1.57  Timing (in seconds)
% 3.22/1.57  ----------------------
% 3.22/1.57  Preprocessing        : 0.40
% 3.22/1.57  Parsing              : 0.22
% 3.22/1.57  CNF conversion       : 0.02
% 3.22/1.57  Main loop            : 0.43
% 3.22/1.57  Inferencing          : 0.18
% 3.22/1.57  Reduction            : 0.16
% 3.22/1.57  Demodulation         : 0.13
% 3.22/1.57  BG Simplification    : 0.03
% 3.22/1.57  Subsumption          : 0.04
% 3.22/1.57  Abstraction          : 0.03
% 3.22/1.57  MUC search           : 0.00
% 3.22/1.57  Cooper               : 0.00
% 3.22/1.57  Total                : 0.85
% 3.22/1.57  Index Insertion      : 0.00
% 3.22/1.57  Index Deletion       : 0.00
% 3.22/1.57  Index Matching       : 0.00
% 3.22/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
