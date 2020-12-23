%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:15 EST 2020

% Result     : Theorem 4.40s
% Output     : CNFRefutation 4.40s
% Verified   : 
% Statistics : Number of formulae       :   57 (  82 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :   39 (  64 expanded)
%              Number of equality atoms :   38 (  63 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(c_8,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] : k2_xboole_0(k1_tarski(A_13),k2_enumset1(B_14,C_15,D_16,E_17)) = k3_enumset1(A_13,B_14,C_15,D_16,E_17) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_9,B_10,C_11,D_12] : k2_xboole_0(k1_tarski(A_9),k1_enumset1(B_10,C_11,D_12)) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_58,B_59,C_60] : k2_enumset1(A_58,A_58,B_59,C_60) = k1_enumset1(A_58,B_59,C_60) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_134,plain,(
    ! [A_82,D_79,E_81,B_80,C_83] : k2_xboole_0(k1_tarski(A_82),k2_enumset1(B_80,C_83,D_79,E_81)) = k3_enumset1(A_82,B_80,C_83,D_79,E_81) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_146,plain,(
    ! [A_82,A_58,B_59,C_60] : k3_enumset1(A_82,A_58,A_58,B_59,C_60) = k2_xboole_0(k1_tarski(A_82),k1_enumset1(A_58,B_59,C_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_134])).

tff(c_149,plain,(
    ! [A_82,A_58,B_59,C_60] : k3_enumset1(A_82,A_58,A_58,B_59,C_60) = k2_enumset1(A_82,A_58,B_59,C_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_146])).

tff(c_20,plain,(
    ! [A_55] : k2_tarski(A_55,A_55) = k1_tarski(A_55) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_329,plain,(
    ! [C_99,A_98,G_97,D_96,B_101,F_100,E_102] : k2_xboole_0(k2_tarski(A_98,B_101),k3_enumset1(C_99,D_96,E_102,F_100,G_97)) = k5_enumset1(A_98,B_101,C_99,D_96,E_102,F_100,G_97) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2864,plain,(
    ! [G_231,F_232,A_233,C_234,E_235,D_236] : k5_enumset1(A_233,A_233,C_234,D_236,E_235,F_232,G_231) = k2_xboole_0(k1_tarski(A_233),k3_enumset1(C_234,D_236,E_235,F_232,G_231)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_329])).

tff(c_4,plain,(
    ! [A_3,F_8,D_6,C_5,E_7,B_4] : k2_xboole_0(k1_enumset1(A_3,B_4,C_5),k1_enumset1(D_6,E_7,F_8)) = k4_enumset1(A_3,B_4,C_5,D_6,E_7,F_8) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_561,plain,(
    ! [A_130,E_126,D_131,F_128,G_132,B_127,C_129] : k2_xboole_0(k1_enumset1(A_130,B_127,C_129),k2_enumset1(D_131,E_126,F_128,G_132)) = k5_enumset1(A_130,B_127,C_129,D_131,E_126,F_128,G_132) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_585,plain,(
    ! [B_59,A_58,A_130,B_127,C_60,C_129] : k5_enumset1(A_130,B_127,C_129,A_58,A_58,B_59,C_60) = k2_xboole_0(k1_enumset1(A_130,B_127,C_129),k1_enumset1(A_58,B_59,C_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_561])).

tff(c_592,plain,(
    ! [B_59,A_58,A_130,B_127,C_60,C_129] : k5_enumset1(A_130,B_127,C_129,A_58,A_58,B_59,C_60) = k4_enumset1(A_130,B_127,C_129,A_58,B_59,C_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_585])).

tff(c_2889,plain,(
    ! [G_231,F_232,A_233,C_234,E_235] : k4_enumset1(A_233,A_233,C_234,E_235,F_232,G_231) = k2_xboole_0(k1_tarski(A_233),k3_enumset1(C_234,E_235,E_235,F_232,G_231)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2864,c_592])).

tff(c_2977,plain,(
    ! [E_238,A_240,C_239,F_241,G_237] : k4_enumset1(A_240,A_240,C_239,E_238,F_241,G_237) = k3_enumset1(A_240,C_239,E_238,F_241,G_237) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_149,c_2889])).

tff(c_22,plain,(
    ! [A_56,B_57] : k1_enumset1(A_56,A_56,B_57) = k2_tarski(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_63,plain,(
    ! [A_69,B_70,C_71,D_72] : k2_xboole_0(k1_tarski(A_69),k1_enumset1(B_70,C_71,D_72)) = k2_enumset1(A_69,B_70,C_71,D_72) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_73,A_74,B_75] : k2_xboole_0(k1_tarski(A_73),k2_tarski(A_74,B_75)) = k2_enumset1(A_73,A_74,A_74,B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_63])).

tff(c_182,plain,(
    ! [A_86,A_87] : k2_xboole_0(k1_tarski(A_86),k1_tarski(A_87)) = k2_enumset1(A_86,A_87,A_87,A_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_75])).

tff(c_85,plain,(
    ! [A_74,B_75] : k2_xboole_0(k1_tarski(A_74),k2_tarski(A_74,B_75)) = k1_enumset1(A_74,A_74,B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_24])).

tff(c_105,plain,(
    ! [A_76,B_77] : k2_xboole_0(k1_tarski(A_76),k2_tarski(A_76,B_77)) = k2_tarski(A_76,B_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_85])).

tff(c_121,plain,(
    ! [A_55] : k2_xboole_0(k1_tarski(A_55),k1_tarski(A_55)) = k2_tarski(A_55,A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_105])).

tff(c_124,plain,(
    ! [A_55] : k2_xboole_0(k1_tarski(A_55),k1_tarski(A_55)) = k1_tarski(A_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_121])).

tff(c_238,plain,(
    ! [A_88] : k2_enumset1(A_88,A_88,A_88,A_88) = k1_tarski(A_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_124])).

tff(c_299,plain,(
    ! [A_95] : k1_enumset1(A_95,A_95,A_95) = k1_tarski(A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_24])).

tff(c_305,plain,(
    ! [A_95,D_6,E_7,F_8] : k4_enumset1(A_95,A_95,A_95,D_6,E_7,F_8) = k2_xboole_0(k1_tarski(A_95),k1_enumset1(D_6,E_7,F_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_4])).

tff(c_323,plain,(
    ! [A_95,D_6,E_7,F_8] : k4_enumset1(A_95,A_95,A_95,D_6,E_7,F_8) = k2_enumset1(A_95,D_6,E_7,F_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_305])).

tff(c_3036,plain,(
    ! [C_239,E_238,F_241,G_237] : k3_enumset1(C_239,C_239,E_238,F_241,G_237) = k2_enumset1(C_239,E_238,F_241,G_237) ),
    inference(superposition,[status(thm),theory(equality)],[c_2977,c_323])).

tff(c_26,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3036,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.40/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.40/1.80  
% 4.40/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.40/1.81  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.40/1.81  
% 4.40/1.81  %Foreground sorts:
% 4.40/1.81  
% 4.40/1.81  
% 4.40/1.81  %Background operators:
% 4.40/1.81  
% 4.40/1.81  
% 4.40/1.81  %Foreground operators:
% 4.40/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.40/1.81  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.40/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.40/1.81  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.40/1.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.40/1.81  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.40/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.40/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.40/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.40/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.40/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.40/1.81  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.40/1.81  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.40/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.40/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.40/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.40/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.40/1.81  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.40/1.81  
% 4.40/1.82  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 4.40/1.82  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 4.40/1.82  tff(f_49, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.40/1.82  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.40/1.82  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_enumset1)).
% 4.40/1.82  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 4.40/1.82  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 4.40/1.82  tff(f_47, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.40/1.82  tff(f_52, negated_conjecture, ~(![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.40/1.82  tff(c_8, plain, (![E_17, A_13, B_14, C_15, D_16]: (k2_xboole_0(k1_tarski(A_13), k2_enumset1(B_14, C_15, D_16, E_17))=k3_enumset1(A_13, B_14, C_15, D_16, E_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.40/1.82  tff(c_6, plain, (![A_9, B_10, C_11, D_12]: (k2_xboole_0(k1_tarski(A_9), k1_enumset1(B_10, C_11, D_12))=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.40/1.82  tff(c_24, plain, (![A_58, B_59, C_60]: (k2_enumset1(A_58, A_58, B_59, C_60)=k1_enumset1(A_58, B_59, C_60))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.40/1.82  tff(c_134, plain, (![A_82, D_79, E_81, B_80, C_83]: (k2_xboole_0(k1_tarski(A_82), k2_enumset1(B_80, C_83, D_79, E_81))=k3_enumset1(A_82, B_80, C_83, D_79, E_81))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.40/1.82  tff(c_146, plain, (![A_82, A_58, B_59, C_60]: (k3_enumset1(A_82, A_58, A_58, B_59, C_60)=k2_xboole_0(k1_tarski(A_82), k1_enumset1(A_58, B_59, C_60)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_134])).
% 4.40/1.82  tff(c_149, plain, (![A_82, A_58, B_59, C_60]: (k3_enumset1(A_82, A_58, A_58, B_59, C_60)=k2_enumset1(A_82, A_58, B_59, C_60))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_146])).
% 4.40/1.82  tff(c_20, plain, (![A_55]: (k2_tarski(A_55, A_55)=k1_tarski(A_55))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.40/1.82  tff(c_329, plain, (![C_99, A_98, G_97, D_96, B_101, F_100, E_102]: (k2_xboole_0(k2_tarski(A_98, B_101), k3_enumset1(C_99, D_96, E_102, F_100, G_97))=k5_enumset1(A_98, B_101, C_99, D_96, E_102, F_100, G_97))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.40/1.82  tff(c_2864, plain, (![G_231, F_232, A_233, C_234, E_235, D_236]: (k5_enumset1(A_233, A_233, C_234, D_236, E_235, F_232, G_231)=k2_xboole_0(k1_tarski(A_233), k3_enumset1(C_234, D_236, E_235, F_232, G_231)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_329])).
% 4.40/1.82  tff(c_4, plain, (![A_3, F_8, D_6, C_5, E_7, B_4]: (k2_xboole_0(k1_enumset1(A_3, B_4, C_5), k1_enumset1(D_6, E_7, F_8))=k4_enumset1(A_3, B_4, C_5, D_6, E_7, F_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.40/1.82  tff(c_561, plain, (![A_130, E_126, D_131, F_128, G_132, B_127, C_129]: (k2_xboole_0(k1_enumset1(A_130, B_127, C_129), k2_enumset1(D_131, E_126, F_128, G_132))=k5_enumset1(A_130, B_127, C_129, D_131, E_126, F_128, G_132))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.40/1.82  tff(c_585, plain, (![B_59, A_58, A_130, B_127, C_60, C_129]: (k5_enumset1(A_130, B_127, C_129, A_58, A_58, B_59, C_60)=k2_xboole_0(k1_enumset1(A_130, B_127, C_129), k1_enumset1(A_58, B_59, C_60)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_561])).
% 4.40/1.82  tff(c_592, plain, (![B_59, A_58, A_130, B_127, C_60, C_129]: (k5_enumset1(A_130, B_127, C_129, A_58, A_58, B_59, C_60)=k4_enumset1(A_130, B_127, C_129, A_58, B_59, C_60))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_585])).
% 4.40/1.82  tff(c_2889, plain, (![G_231, F_232, A_233, C_234, E_235]: (k4_enumset1(A_233, A_233, C_234, E_235, F_232, G_231)=k2_xboole_0(k1_tarski(A_233), k3_enumset1(C_234, E_235, E_235, F_232, G_231)))), inference(superposition, [status(thm), theory('equality')], [c_2864, c_592])).
% 4.40/1.82  tff(c_2977, plain, (![E_238, A_240, C_239, F_241, G_237]: (k4_enumset1(A_240, A_240, C_239, E_238, F_241, G_237)=k3_enumset1(A_240, C_239, E_238, F_241, G_237))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_149, c_2889])).
% 4.40/1.82  tff(c_22, plain, (![A_56, B_57]: (k1_enumset1(A_56, A_56, B_57)=k2_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.40/1.82  tff(c_63, plain, (![A_69, B_70, C_71, D_72]: (k2_xboole_0(k1_tarski(A_69), k1_enumset1(B_70, C_71, D_72))=k2_enumset1(A_69, B_70, C_71, D_72))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.40/1.82  tff(c_75, plain, (![A_73, A_74, B_75]: (k2_xboole_0(k1_tarski(A_73), k2_tarski(A_74, B_75))=k2_enumset1(A_73, A_74, A_74, B_75))), inference(superposition, [status(thm), theory('equality')], [c_22, c_63])).
% 4.40/1.82  tff(c_182, plain, (![A_86, A_87]: (k2_xboole_0(k1_tarski(A_86), k1_tarski(A_87))=k2_enumset1(A_86, A_87, A_87, A_87))), inference(superposition, [status(thm), theory('equality')], [c_20, c_75])).
% 4.40/1.82  tff(c_85, plain, (![A_74, B_75]: (k2_xboole_0(k1_tarski(A_74), k2_tarski(A_74, B_75))=k1_enumset1(A_74, A_74, B_75))), inference(superposition, [status(thm), theory('equality')], [c_75, c_24])).
% 4.40/1.82  tff(c_105, plain, (![A_76, B_77]: (k2_xboole_0(k1_tarski(A_76), k2_tarski(A_76, B_77))=k2_tarski(A_76, B_77))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_85])).
% 4.40/1.82  tff(c_121, plain, (![A_55]: (k2_xboole_0(k1_tarski(A_55), k1_tarski(A_55))=k2_tarski(A_55, A_55))), inference(superposition, [status(thm), theory('equality')], [c_20, c_105])).
% 4.40/1.82  tff(c_124, plain, (![A_55]: (k2_xboole_0(k1_tarski(A_55), k1_tarski(A_55))=k1_tarski(A_55))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_121])).
% 4.40/1.82  tff(c_238, plain, (![A_88]: (k2_enumset1(A_88, A_88, A_88, A_88)=k1_tarski(A_88))), inference(superposition, [status(thm), theory('equality')], [c_182, c_124])).
% 4.40/1.82  tff(c_299, plain, (![A_95]: (k1_enumset1(A_95, A_95, A_95)=k1_tarski(A_95))), inference(superposition, [status(thm), theory('equality')], [c_238, c_24])).
% 4.40/1.82  tff(c_305, plain, (![A_95, D_6, E_7, F_8]: (k4_enumset1(A_95, A_95, A_95, D_6, E_7, F_8)=k2_xboole_0(k1_tarski(A_95), k1_enumset1(D_6, E_7, F_8)))), inference(superposition, [status(thm), theory('equality')], [c_299, c_4])).
% 4.40/1.82  tff(c_323, plain, (![A_95, D_6, E_7, F_8]: (k4_enumset1(A_95, A_95, A_95, D_6, E_7, F_8)=k2_enumset1(A_95, D_6, E_7, F_8))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_305])).
% 4.40/1.82  tff(c_3036, plain, (![C_239, E_238, F_241, G_237]: (k3_enumset1(C_239, C_239, E_238, F_241, G_237)=k2_enumset1(C_239, E_238, F_241, G_237))), inference(superposition, [status(thm), theory('equality')], [c_2977, c_323])).
% 4.40/1.82  tff(c_26, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.40/1.82  tff(c_3110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3036, c_26])).
% 4.40/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.40/1.82  
% 4.40/1.82  Inference rules
% 4.40/1.82  ----------------------
% 4.40/1.82  #Ref     : 0
% 4.40/1.82  #Sup     : 722
% 4.40/1.82  #Fact    : 0
% 4.40/1.82  #Define  : 0
% 4.40/1.82  #Split   : 0
% 4.40/1.82  #Chain   : 0
% 4.40/1.82  #Close   : 0
% 4.40/1.82  
% 4.40/1.82  Ordering : KBO
% 4.40/1.82  
% 4.40/1.82  Simplification rules
% 4.40/1.82  ----------------------
% 4.40/1.82  #Subsume      : 83
% 4.40/1.82  #Demod        : 913
% 4.40/1.82  #Tautology    : 501
% 4.40/1.82  #SimpNegUnit  : 0
% 4.40/1.82  #BackRed      : 2
% 4.40/1.82  
% 4.40/1.82  #Partial instantiations: 0
% 4.40/1.82  #Strategies tried      : 1
% 4.40/1.82  
% 4.40/1.82  Timing (in seconds)
% 4.40/1.82  ----------------------
% 4.40/1.82  Preprocessing        : 0.31
% 4.40/1.82  Parsing              : 0.16
% 4.40/1.82  CNF conversion       : 0.02
% 4.40/1.82  Main loop            : 0.70
% 4.40/1.82  Inferencing          : 0.28
% 4.40/1.82  Reduction            : 0.30
% 4.40/1.82  Demodulation         : 0.25
% 4.40/1.82  BG Simplification    : 0.03
% 4.40/1.82  Subsumption          : 0.06
% 4.40/1.82  Abstraction          : 0.05
% 4.40/1.82  MUC search           : 0.00
% 4.40/1.82  Cooper               : 0.00
% 4.40/1.82  Total                : 1.04
% 4.40/1.82  Index Insertion      : 0.00
% 4.40/1.82  Index Deletion       : 0.00
% 4.40/1.82  Index Matching       : 0.00
% 4.40/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
