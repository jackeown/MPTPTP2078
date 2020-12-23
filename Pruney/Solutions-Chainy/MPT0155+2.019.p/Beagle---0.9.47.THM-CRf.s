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
% DateTime   : Thu Dec  3 09:46:11 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 141 expanded)
%              Number of leaves         :   25 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :   47 ( 124 expanded)
%              Number of equality atoms :   46 ( 123 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_tarski(A,B),k2_enumset1(C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_10,plain,(
    ! [A_19,B_20,C_21,D_22] : k2_xboole_0(k1_tarski(A_19),k1_enumset1(B_20,C_21,D_22)) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_16,B_17,C_18] : k2_xboole_0(k2_tarski(A_16,B_17),k1_tarski(C_18)) = k1_enumset1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [A_57] : k2_tarski(A_57,A_57) = k1_tarski(A_57) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_58,B_59] : k1_enumset1(A_58,A_58,B_59) = k2_tarski(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_127,plain,(
    ! [E_80,C_79,B_81,A_83,D_82] : k2_xboole_0(k2_tarski(A_83,B_81),k1_enumset1(C_79,D_82,E_80)) = k3_enumset1(A_83,B_81,C_79,D_82,E_80) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_152,plain,(
    ! [A_88,B_89,A_90,B_91] : k3_enumset1(A_88,B_89,A_90,A_90,B_91) = k2_xboole_0(k2_tarski(A_88,B_89),k2_tarski(A_90,B_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_127])).

tff(c_178,plain,(
    ! [A_88,B_89,A_57] : k3_enumset1(A_88,B_89,A_57,A_57,A_57) = k2_xboole_0(k2_tarski(A_88,B_89),k1_tarski(A_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_152])).

tff(c_185,plain,(
    ! [A_88,B_89,A_57] : k3_enumset1(A_88,B_89,A_57,A_57,A_57) = k1_enumset1(A_88,B_89,A_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_178])).

tff(c_67,plain,(
    ! [A_68,B_69,C_70,D_71] : k2_xboole_0(k1_tarski(A_68),k1_enumset1(B_69,C_70,D_71)) = k2_enumset1(A_68,B_69,C_70,D_71) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    ! [A_68,A_58,B_59] : k2_xboole_0(k1_tarski(A_68),k2_tarski(A_58,B_59)) = k2_enumset1(A_68,A_58,A_58,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_67])).

tff(c_54,plain,(
    ! [A_65,B_66,C_67] : k2_xboole_0(k2_tarski(A_65,B_66),k1_tarski(C_67)) = k1_enumset1(A_65,B_66,C_67) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_63,plain,(
    ! [A_57,C_67] : k2_xboole_0(k1_tarski(A_57),k1_tarski(C_67)) = k1_enumset1(A_57,A_57,C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_54])).

tff(c_66,plain,(
    ! [A_57,C_67] : k2_xboole_0(k1_tarski(A_57),k1_tarski(C_67)) = k2_tarski(A_57,C_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_63])).

tff(c_88,plain,(
    ! [A_74,A_75,B_76] : k2_xboole_0(k1_tarski(A_74),k2_tarski(A_75,B_76)) = k2_enumset1(A_74,A_75,A_75,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_67])).

tff(c_103,plain,(
    ! [A_74,A_57] : k2_xboole_0(k1_tarski(A_74),k1_tarski(A_57)) = k2_enumset1(A_74,A_57,A_57,A_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_88])).

tff(c_108,plain,(
    ! [A_74,A_57] : k2_enumset1(A_74,A_57,A_57,A_57) = k2_tarski(A_74,A_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_103])).

tff(c_314,plain,(
    ! [C_103,B_104,A_102,F_100,D_105,E_101] : k2_xboole_0(k2_tarski(A_102,B_104),k2_enumset1(C_103,D_105,E_101,F_100)) = k4_enumset1(A_102,B_104,C_103,D_105,E_101,F_100) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_332,plain,(
    ! [A_106,B_107,A_108,A_109] : k4_enumset1(A_106,B_107,A_108,A_109,A_109,A_109) = k2_xboole_0(k2_tarski(A_106,B_107),k2_tarski(A_108,A_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_314])).

tff(c_380,plain,(
    ! [A_113,A_114,A_115] : k4_enumset1(A_113,A_113,A_114,A_115,A_115,A_115) = k2_xboole_0(k1_tarski(A_113),k2_tarski(A_114,A_115)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_332])).

tff(c_419,plain,(
    ! [A_68,A_58,B_59] : k4_enumset1(A_68,A_68,A_58,B_59,B_59,B_59) = k2_enumset1(A_68,A_58,A_58,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_380])).

tff(c_12,plain,(
    ! [A_23,B_24,D_26,C_25,E_27] : k2_xboole_0(k2_tarski(A_23,B_24),k1_enumset1(C_25,D_26,E_27)) = k3_enumset1(A_23,B_24,C_25,D_26,E_27) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_432,plain,(
    ! [A_119,B_121,F_118,E_116,C_120,D_117] : k2_xboole_0(k1_enumset1(A_119,B_121,C_120),k1_enumset1(D_117,E_116,F_118)) = k4_enumset1(A_119,B_121,C_120,D_117,E_116,F_118) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_441,plain,(
    ! [B_59,A_58,F_118,E_116,D_117] : k4_enumset1(A_58,A_58,B_59,D_117,E_116,F_118) = k2_xboole_0(k2_tarski(A_58,B_59),k1_enumset1(D_117,E_116,F_118)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_432])).

tff(c_544,plain,(
    ! [F_129,E_130,D_131,A_128,B_127] : k4_enumset1(A_128,A_128,B_127,D_131,E_130,F_129) = k3_enumset1(A_128,B_127,D_131,E_130,F_129) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_441])).

tff(c_573,plain,(
    ! [A_68,A_58,B_59] : k3_enumset1(A_68,A_58,B_59,B_59,B_59) = k2_enumset1(A_68,A_58,A_58,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_544])).

tff(c_594,plain,(
    ! [A_68,A_58,B_59] : k2_enumset1(A_68,A_58,A_58,B_59) = k1_enumset1(A_68,A_58,B_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_573])).

tff(c_447,plain,(
    ! [B_59,A_58,F_118,E_116,D_117] : k4_enumset1(A_58,A_58,B_59,D_117,E_116,F_118) = k3_enumset1(A_58,B_59,D_117,E_116,F_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_441])).

tff(c_329,plain,(
    ! [C_103,A_57,F_100,D_105,E_101] : k4_enumset1(A_57,A_57,C_103,D_105,E_101,F_100) = k2_xboole_0(k1_tarski(A_57),k2_enumset1(C_103,D_105,E_101,F_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_314])).

tff(c_997,plain,(
    ! [E_177,F_178,D_179,C_181,A_180] : k2_xboole_0(k1_tarski(A_180),k2_enumset1(C_181,D_179,E_177,F_178)) = k3_enumset1(A_180,C_181,D_179,E_177,F_178) ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_329])).

tff(c_1006,plain,(
    ! [A_180,A_68,A_58,B_59] : k3_enumset1(A_180,A_68,A_58,A_58,B_59) = k2_xboole_0(k1_tarski(A_180),k1_enumset1(A_68,A_58,B_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_997])).

tff(c_1119,plain,(
    ! [A_188,A_189,A_190,B_191] : k3_enumset1(A_188,A_189,A_190,A_190,B_191) = k2_enumset1(A_188,A_189,A_190,B_191) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1006])).

tff(c_323,plain,(
    ! [A_102,B_104,A_74,A_57] : k4_enumset1(A_102,B_104,A_74,A_57,A_57,A_57) = k2_xboole_0(k2_tarski(A_102,B_104),k2_tarski(A_74,A_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_314])).

tff(c_587,plain,(
    ! [B_104,A_74,A_57] : k3_enumset1(B_104,A_74,A_57,A_57,A_57) = k2_xboole_0(k2_tarski(B_104,B_104),k2_tarski(A_74,A_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_544])).

tff(c_597,plain,(
    ! [B_104,A_74,A_57] : k2_xboole_0(k1_tarski(B_104),k2_tarski(A_74,A_57)) = k1_enumset1(B_104,A_74,A_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_22,c_587])).

tff(c_175,plain,(
    ! [A_57,A_90,B_91] : k3_enumset1(A_57,A_57,A_90,A_90,B_91) = k2_xboole_0(k1_tarski(A_57),k2_tarski(A_90,B_91)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_152])).

tff(c_917,plain,(
    ! [A_57,A_90,B_91] : k3_enumset1(A_57,A_57,A_90,A_90,B_91) = k1_enumset1(A_57,A_90,B_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_175])).

tff(c_1126,plain,(
    ! [A_189,A_190,B_191] : k2_enumset1(A_189,A_189,A_190,B_191) = k1_enumset1(A_189,A_190,B_191) ),
    inference(superposition,[status(thm),theory(equality)],[c_1119,c_917])).

tff(c_26,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1126,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:08:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.43  
% 2.80/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.43  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.80/1.43  
% 2.80/1.43  %Foreground sorts:
% 2.80/1.43  
% 2.80/1.43  
% 2.80/1.43  %Background operators:
% 2.80/1.43  
% 2.80/1.43  
% 2.80/1.43  %Foreground operators:
% 2.80/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.80/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.80/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.80/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.80/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.80/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.80/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.80/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.80/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.80/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.80/1.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.80/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.80/1.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.80/1.43  
% 3.12/1.45  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 3.12/1.45  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 3.12/1.45  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.12/1.45  tff(f_49, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.12/1.45  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 3.12/1.45  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_tarski(A, B), k2_enumset1(C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_enumset1)).
% 3.12/1.45  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 3.12/1.45  tff(f_52, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.12/1.45  tff(c_10, plain, (![A_19, B_20, C_21, D_22]: (k2_xboole_0(k1_tarski(A_19), k1_enumset1(B_20, C_21, D_22))=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.12/1.45  tff(c_8, plain, (![A_16, B_17, C_18]: (k2_xboole_0(k2_tarski(A_16, B_17), k1_tarski(C_18))=k1_enumset1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.12/1.45  tff(c_22, plain, (![A_57]: (k2_tarski(A_57, A_57)=k1_tarski(A_57))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.12/1.45  tff(c_24, plain, (![A_58, B_59]: (k1_enumset1(A_58, A_58, B_59)=k2_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.12/1.45  tff(c_127, plain, (![E_80, C_79, B_81, A_83, D_82]: (k2_xboole_0(k2_tarski(A_83, B_81), k1_enumset1(C_79, D_82, E_80))=k3_enumset1(A_83, B_81, C_79, D_82, E_80))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.12/1.45  tff(c_152, plain, (![A_88, B_89, A_90, B_91]: (k3_enumset1(A_88, B_89, A_90, A_90, B_91)=k2_xboole_0(k2_tarski(A_88, B_89), k2_tarski(A_90, B_91)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_127])).
% 3.12/1.45  tff(c_178, plain, (![A_88, B_89, A_57]: (k3_enumset1(A_88, B_89, A_57, A_57, A_57)=k2_xboole_0(k2_tarski(A_88, B_89), k1_tarski(A_57)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_152])).
% 3.12/1.45  tff(c_185, plain, (![A_88, B_89, A_57]: (k3_enumset1(A_88, B_89, A_57, A_57, A_57)=k1_enumset1(A_88, B_89, A_57))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_178])).
% 3.12/1.45  tff(c_67, plain, (![A_68, B_69, C_70, D_71]: (k2_xboole_0(k1_tarski(A_68), k1_enumset1(B_69, C_70, D_71))=k2_enumset1(A_68, B_69, C_70, D_71))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.12/1.45  tff(c_76, plain, (![A_68, A_58, B_59]: (k2_xboole_0(k1_tarski(A_68), k2_tarski(A_58, B_59))=k2_enumset1(A_68, A_58, A_58, B_59))), inference(superposition, [status(thm), theory('equality')], [c_24, c_67])).
% 3.12/1.45  tff(c_54, plain, (![A_65, B_66, C_67]: (k2_xboole_0(k2_tarski(A_65, B_66), k1_tarski(C_67))=k1_enumset1(A_65, B_66, C_67))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.12/1.45  tff(c_63, plain, (![A_57, C_67]: (k2_xboole_0(k1_tarski(A_57), k1_tarski(C_67))=k1_enumset1(A_57, A_57, C_67))), inference(superposition, [status(thm), theory('equality')], [c_22, c_54])).
% 3.12/1.45  tff(c_66, plain, (![A_57, C_67]: (k2_xboole_0(k1_tarski(A_57), k1_tarski(C_67))=k2_tarski(A_57, C_67))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_63])).
% 3.12/1.45  tff(c_88, plain, (![A_74, A_75, B_76]: (k2_xboole_0(k1_tarski(A_74), k2_tarski(A_75, B_76))=k2_enumset1(A_74, A_75, A_75, B_76))), inference(superposition, [status(thm), theory('equality')], [c_24, c_67])).
% 3.12/1.45  tff(c_103, plain, (![A_74, A_57]: (k2_xboole_0(k1_tarski(A_74), k1_tarski(A_57))=k2_enumset1(A_74, A_57, A_57, A_57))), inference(superposition, [status(thm), theory('equality')], [c_22, c_88])).
% 3.12/1.45  tff(c_108, plain, (![A_74, A_57]: (k2_enumset1(A_74, A_57, A_57, A_57)=k2_tarski(A_74, A_57))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_103])).
% 3.12/1.45  tff(c_314, plain, (![C_103, B_104, A_102, F_100, D_105, E_101]: (k2_xboole_0(k2_tarski(A_102, B_104), k2_enumset1(C_103, D_105, E_101, F_100))=k4_enumset1(A_102, B_104, C_103, D_105, E_101, F_100))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.12/1.45  tff(c_332, plain, (![A_106, B_107, A_108, A_109]: (k4_enumset1(A_106, B_107, A_108, A_109, A_109, A_109)=k2_xboole_0(k2_tarski(A_106, B_107), k2_tarski(A_108, A_109)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_314])).
% 3.12/1.45  tff(c_380, plain, (![A_113, A_114, A_115]: (k4_enumset1(A_113, A_113, A_114, A_115, A_115, A_115)=k2_xboole_0(k1_tarski(A_113), k2_tarski(A_114, A_115)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_332])).
% 3.12/1.45  tff(c_419, plain, (![A_68, A_58, B_59]: (k4_enumset1(A_68, A_68, A_58, B_59, B_59, B_59)=k2_enumset1(A_68, A_58, A_58, B_59))), inference(superposition, [status(thm), theory('equality')], [c_76, c_380])).
% 3.12/1.45  tff(c_12, plain, (![A_23, B_24, D_26, C_25, E_27]: (k2_xboole_0(k2_tarski(A_23, B_24), k1_enumset1(C_25, D_26, E_27))=k3_enumset1(A_23, B_24, C_25, D_26, E_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.12/1.45  tff(c_432, plain, (![A_119, B_121, F_118, E_116, C_120, D_117]: (k2_xboole_0(k1_enumset1(A_119, B_121, C_120), k1_enumset1(D_117, E_116, F_118))=k4_enumset1(A_119, B_121, C_120, D_117, E_116, F_118))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.12/1.45  tff(c_441, plain, (![B_59, A_58, F_118, E_116, D_117]: (k4_enumset1(A_58, A_58, B_59, D_117, E_116, F_118)=k2_xboole_0(k2_tarski(A_58, B_59), k1_enumset1(D_117, E_116, F_118)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_432])).
% 3.12/1.45  tff(c_544, plain, (![F_129, E_130, D_131, A_128, B_127]: (k4_enumset1(A_128, A_128, B_127, D_131, E_130, F_129)=k3_enumset1(A_128, B_127, D_131, E_130, F_129))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_441])).
% 3.12/1.45  tff(c_573, plain, (![A_68, A_58, B_59]: (k3_enumset1(A_68, A_58, B_59, B_59, B_59)=k2_enumset1(A_68, A_58, A_58, B_59))), inference(superposition, [status(thm), theory('equality')], [c_419, c_544])).
% 3.12/1.45  tff(c_594, plain, (![A_68, A_58, B_59]: (k2_enumset1(A_68, A_58, A_58, B_59)=k1_enumset1(A_68, A_58, B_59))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_573])).
% 3.12/1.45  tff(c_447, plain, (![B_59, A_58, F_118, E_116, D_117]: (k4_enumset1(A_58, A_58, B_59, D_117, E_116, F_118)=k3_enumset1(A_58, B_59, D_117, E_116, F_118))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_441])).
% 3.12/1.45  tff(c_329, plain, (![C_103, A_57, F_100, D_105, E_101]: (k4_enumset1(A_57, A_57, C_103, D_105, E_101, F_100)=k2_xboole_0(k1_tarski(A_57), k2_enumset1(C_103, D_105, E_101, F_100)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_314])).
% 3.12/1.45  tff(c_997, plain, (![E_177, F_178, D_179, C_181, A_180]: (k2_xboole_0(k1_tarski(A_180), k2_enumset1(C_181, D_179, E_177, F_178))=k3_enumset1(A_180, C_181, D_179, E_177, F_178))), inference(demodulation, [status(thm), theory('equality')], [c_447, c_329])).
% 3.12/1.45  tff(c_1006, plain, (![A_180, A_68, A_58, B_59]: (k3_enumset1(A_180, A_68, A_58, A_58, B_59)=k2_xboole_0(k1_tarski(A_180), k1_enumset1(A_68, A_58, B_59)))), inference(superposition, [status(thm), theory('equality')], [c_594, c_997])).
% 3.12/1.45  tff(c_1119, plain, (![A_188, A_189, A_190, B_191]: (k3_enumset1(A_188, A_189, A_190, A_190, B_191)=k2_enumset1(A_188, A_189, A_190, B_191))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1006])).
% 3.12/1.45  tff(c_323, plain, (![A_102, B_104, A_74, A_57]: (k4_enumset1(A_102, B_104, A_74, A_57, A_57, A_57)=k2_xboole_0(k2_tarski(A_102, B_104), k2_tarski(A_74, A_57)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_314])).
% 3.12/1.45  tff(c_587, plain, (![B_104, A_74, A_57]: (k3_enumset1(B_104, A_74, A_57, A_57, A_57)=k2_xboole_0(k2_tarski(B_104, B_104), k2_tarski(A_74, A_57)))), inference(superposition, [status(thm), theory('equality')], [c_323, c_544])).
% 3.12/1.45  tff(c_597, plain, (![B_104, A_74, A_57]: (k2_xboole_0(k1_tarski(B_104), k2_tarski(A_74, A_57))=k1_enumset1(B_104, A_74, A_57))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_22, c_587])).
% 3.12/1.45  tff(c_175, plain, (![A_57, A_90, B_91]: (k3_enumset1(A_57, A_57, A_90, A_90, B_91)=k2_xboole_0(k1_tarski(A_57), k2_tarski(A_90, B_91)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_152])).
% 3.12/1.45  tff(c_917, plain, (![A_57, A_90, B_91]: (k3_enumset1(A_57, A_57, A_90, A_90, B_91)=k1_enumset1(A_57, A_90, B_91))), inference(demodulation, [status(thm), theory('equality')], [c_597, c_175])).
% 3.12/1.45  tff(c_1126, plain, (![A_189, A_190, B_191]: (k2_enumset1(A_189, A_189, A_190, B_191)=k1_enumset1(A_189, A_190, B_191))), inference(superposition, [status(thm), theory('equality')], [c_1119, c_917])).
% 3.12/1.45  tff(c_26, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.12/1.45  tff(c_1315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1126, c_26])).
% 3.12/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.45  
% 3.12/1.45  Inference rules
% 3.12/1.45  ----------------------
% 3.12/1.45  #Ref     : 0
% 3.12/1.45  #Sup     : 299
% 3.12/1.45  #Fact    : 0
% 3.12/1.45  #Define  : 0
% 3.12/1.45  #Split   : 0
% 3.12/1.45  #Chain   : 0
% 3.12/1.45  #Close   : 0
% 3.12/1.45  
% 3.12/1.45  Ordering : KBO
% 3.12/1.45  
% 3.12/1.45  Simplification rules
% 3.12/1.45  ----------------------
% 3.12/1.45  #Subsume      : 11
% 3.12/1.45  #Demod        : 265
% 3.12/1.45  #Tautology    : 205
% 3.12/1.45  #SimpNegUnit  : 0
% 3.12/1.45  #BackRed      : 6
% 3.12/1.45  
% 3.12/1.45  #Partial instantiations: 0
% 3.12/1.45  #Strategies tried      : 1
% 3.12/1.45  
% 3.12/1.45  Timing (in seconds)
% 3.12/1.45  ----------------------
% 3.12/1.45  Preprocessing        : 0.30
% 3.12/1.45  Parsing              : 0.16
% 3.12/1.45  CNF conversion       : 0.02
% 3.12/1.45  Main loop            : 0.39
% 3.12/1.45  Inferencing          : 0.16
% 3.12/1.45  Reduction            : 0.15
% 3.12/1.45  Demodulation         : 0.12
% 3.12/1.45  BG Simplification    : 0.03
% 3.12/1.45  Subsumption          : 0.04
% 3.12/1.45  Abstraction          : 0.03
% 3.12/1.45  MUC search           : 0.00
% 3.12/1.45  Cooper               : 0.00
% 3.12/1.45  Total                : 0.72
% 3.12/1.45  Index Insertion      : 0.00
% 3.12/1.45  Index Deletion       : 0.00
% 3.12/1.45  Index Matching       : 0.00
% 3.12/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
