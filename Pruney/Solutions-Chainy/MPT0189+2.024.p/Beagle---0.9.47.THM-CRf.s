%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:53 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 113 expanded)
%              Number of leaves         :   27 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   27 (  94 expanded)
%              Number of equality atoms :   26 (  93 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_8,plain,(
    ! [B_14,C_15,A_13] : k1_enumset1(B_14,C_15,A_13) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [A_57,B_58,C_59,D_60] : k3_enumset1(A_57,A_57,B_58,C_59,D_60) = k2_enumset1(A_57,B_58,C_59,D_60) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_24,plain,(
    ! [A_54,B_55,C_56] : k2_enumset1(A_54,A_54,B_55,C_56) = k1_enumset1(A_54,B_55,C_56) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    ! [A_61,B_62,E_65,C_63,D_64] : k4_enumset1(A_61,A_61,B_62,C_63,D_64,E_65) = k3_enumset1(A_61,B_62,C_63,D_64,E_65) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [B_67,A_66,F_71,C_68,E_70,D_69] : k5_enumset1(A_66,A_66,B_67,C_68,D_69,E_70,F_71) = k4_enumset1(A_66,B_67,C_68,D_69,E_70,F_71) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_333,plain,(
    ! [G_126,C_125,A_130,F_131,E_129,B_127,D_128] : k2_xboole_0(k4_enumset1(A_130,B_127,C_125,D_128,E_129,F_131),k1_tarski(G_126)) = k5_enumset1(A_130,B_127,C_125,D_128,E_129,F_131,G_126) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_342,plain,(
    ! [A_61,B_62,G_126,E_65,C_63,D_64] : k5_enumset1(A_61,A_61,B_62,C_63,D_64,E_65,G_126) = k2_xboole_0(k3_enumset1(A_61,B_62,C_63,D_64,E_65),k1_tarski(G_126)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_333])).

tff(c_346,plain,(
    ! [C_133,E_137,G_132,D_134,B_135,A_136] : k2_xboole_0(k3_enumset1(A_136,B_135,C_133,D_134,E_137),k1_tarski(G_132)) = k4_enumset1(A_136,B_135,C_133,D_134,E_137,G_132) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_342])).

tff(c_355,plain,(
    ! [A_57,G_132,B_58,D_60,C_59] : k4_enumset1(A_57,A_57,B_58,C_59,D_60,G_132) = k2_xboole_0(k2_enumset1(A_57,B_58,C_59,D_60),k1_tarski(G_132)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_346])).

tff(c_359,plain,(
    ! [A_139,B_138,C_142,D_140,G_141] : k2_xboole_0(k2_enumset1(A_139,B_138,C_142,D_140),k1_tarski(G_141)) = k3_enumset1(A_139,B_138,C_142,D_140,G_141) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_355])).

tff(c_377,plain,(
    ! [A_54,B_55,C_56,G_141] : k3_enumset1(A_54,A_54,B_55,C_56,G_141) = k2_xboole_0(k1_enumset1(A_54,B_55,C_56),k1_tarski(G_141)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_359])).

tff(c_394,plain,(
    ! [A_151,B_152,C_153,G_154] : k2_xboole_0(k1_enumset1(A_151,B_152,C_153),k1_tarski(G_154)) = k2_enumset1(A_151,B_152,C_153,G_154) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_377])).

tff(c_540,plain,(
    ! [B_175,C_176,A_177,G_178] : k2_xboole_0(k1_enumset1(B_175,C_176,A_177),k1_tarski(G_178)) = k2_enumset1(A_177,B_175,C_176,G_178) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_394])).

tff(c_380,plain,(
    ! [A_54,B_55,C_56,G_141] : k2_xboole_0(k1_enumset1(A_54,B_55,C_56),k1_tarski(G_141)) = k2_enumset1(A_54,B_55,C_56,G_141) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_377])).

tff(c_546,plain,(
    ! [B_175,C_176,A_177,G_178] : k2_enumset1(B_175,C_176,A_177,G_178) = k2_enumset1(A_177,B_175,C_176,G_178) ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_380])).

tff(c_10,plain,(
    ! [A_16,C_18,B_17,D_19] : k2_enumset1(A_16,C_18,B_17,D_19) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_35,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_34])).

tff(c_576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_546,c_35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.75  
% 2.77/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.75  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.07/1.75  
% 3.07/1.75  %Foreground sorts:
% 3.07/1.75  
% 3.07/1.75  
% 3.07/1.75  %Background operators:
% 3.07/1.75  
% 3.07/1.75  
% 3.07/1.75  %Foreground operators:
% 3.07/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.07/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.07/1.75  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.07/1.75  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.07/1.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.07/1.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.07/1.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.07/1.75  tff('#skF_2', type, '#skF_2': $i).
% 3.07/1.75  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.75  tff('#skF_1', type, '#skF_1': $i).
% 3.07/1.75  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.07/1.75  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.07/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.75  tff('#skF_4', type, '#skF_4': $i).
% 3.07/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.07/1.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.07/1.75  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.07/1.75  
% 3.07/1.76  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 3.07/1.76  tff(f_51, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.07/1.76  tff(f_49, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.07/1.76  tff(f_53, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 3.07/1.76  tff(f_55, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 3.07/1.76  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 3.07/1.76  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 3.07/1.76  tff(f_60, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 3.07/1.76  tff(c_8, plain, (![B_14, C_15, A_13]: (k1_enumset1(B_14, C_15, A_13)=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.07/1.76  tff(c_26, plain, (![A_57, B_58, C_59, D_60]: (k3_enumset1(A_57, A_57, B_58, C_59, D_60)=k2_enumset1(A_57, B_58, C_59, D_60))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.07/1.76  tff(c_24, plain, (![A_54, B_55, C_56]: (k2_enumset1(A_54, A_54, B_55, C_56)=k1_enumset1(A_54, B_55, C_56))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.07/1.76  tff(c_28, plain, (![A_61, B_62, E_65, C_63, D_64]: (k4_enumset1(A_61, A_61, B_62, C_63, D_64, E_65)=k3_enumset1(A_61, B_62, C_63, D_64, E_65))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.07/1.76  tff(c_30, plain, (![B_67, A_66, F_71, C_68, E_70, D_69]: (k5_enumset1(A_66, A_66, B_67, C_68, D_69, E_70, F_71)=k4_enumset1(A_66, B_67, C_68, D_69, E_70, F_71))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.07/1.76  tff(c_333, plain, (![G_126, C_125, A_130, F_131, E_129, B_127, D_128]: (k2_xboole_0(k4_enumset1(A_130, B_127, C_125, D_128, E_129, F_131), k1_tarski(G_126))=k5_enumset1(A_130, B_127, C_125, D_128, E_129, F_131, G_126))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.07/1.76  tff(c_342, plain, (![A_61, B_62, G_126, E_65, C_63, D_64]: (k5_enumset1(A_61, A_61, B_62, C_63, D_64, E_65, G_126)=k2_xboole_0(k3_enumset1(A_61, B_62, C_63, D_64, E_65), k1_tarski(G_126)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_333])).
% 3.07/1.76  tff(c_346, plain, (![C_133, E_137, G_132, D_134, B_135, A_136]: (k2_xboole_0(k3_enumset1(A_136, B_135, C_133, D_134, E_137), k1_tarski(G_132))=k4_enumset1(A_136, B_135, C_133, D_134, E_137, G_132))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_342])).
% 3.07/1.76  tff(c_355, plain, (![A_57, G_132, B_58, D_60, C_59]: (k4_enumset1(A_57, A_57, B_58, C_59, D_60, G_132)=k2_xboole_0(k2_enumset1(A_57, B_58, C_59, D_60), k1_tarski(G_132)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_346])).
% 3.07/1.76  tff(c_359, plain, (![A_139, B_138, C_142, D_140, G_141]: (k2_xboole_0(k2_enumset1(A_139, B_138, C_142, D_140), k1_tarski(G_141))=k3_enumset1(A_139, B_138, C_142, D_140, G_141))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_355])).
% 3.07/1.76  tff(c_377, plain, (![A_54, B_55, C_56, G_141]: (k3_enumset1(A_54, A_54, B_55, C_56, G_141)=k2_xboole_0(k1_enumset1(A_54, B_55, C_56), k1_tarski(G_141)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_359])).
% 3.07/1.76  tff(c_394, plain, (![A_151, B_152, C_153, G_154]: (k2_xboole_0(k1_enumset1(A_151, B_152, C_153), k1_tarski(G_154))=k2_enumset1(A_151, B_152, C_153, G_154))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_377])).
% 3.07/1.76  tff(c_540, plain, (![B_175, C_176, A_177, G_178]: (k2_xboole_0(k1_enumset1(B_175, C_176, A_177), k1_tarski(G_178))=k2_enumset1(A_177, B_175, C_176, G_178))), inference(superposition, [status(thm), theory('equality')], [c_8, c_394])).
% 3.07/1.76  tff(c_380, plain, (![A_54, B_55, C_56, G_141]: (k2_xboole_0(k1_enumset1(A_54, B_55, C_56), k1_tarski(G_141))=k2_enumset1(A_54, B_55, C_56, G_141))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_377])).
% 3.07/1.76  tff(c_546, plain, (![B_175, C_176, A_177, G_178]: (k2_enumset1(B_175, C_176, A_177, G_178)=k2_enumset1(A_177, B_175, C_176, G_178))), inference(superposition, [status(thm), theory('equality')], [c_540, c_380])).
% 3.07/1.76  tff(c_10, plain, (![A_16, C_18, B_17, D_19]: (k2_enumset1(A_16, C_18, B_17, D_19)=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.07/1.76  tff(c_34, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.07/1.76  tff(c_35, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_34])).
% 3.07/1.76  tff(c_576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_546, c_546, c_35])).
% 3.07/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.07/1.76  
% 3.07/1.76  Inference rules
% 3.07/1.76  ----------------------
% 3.07/1.76  #Ref     : 0
% 3.07/1.76  #Sup     : 128
% 3.07/1.76  #Fact    : 0
% 3.07/1.76  #Define  : 0
% 3.07/1.76  #Split   : 0
% 3.07/1.76  #Chain   : 0
% 3.07/1.76  #Close   : 0
% 3.07/1.76  
% 3.07/1.76  Ordering : KBO
% 3.07/1.76  
% 3.07/1.76  Simplification rules
% 3.07/1.76  ----------------------
% 3.07/1.76  #Subsume      : 4
% 3.07/1.76  #Demod        : 68
% 3.07/1.76  #Tautology    : 95
% 3.07/1.76  #SimpNegUnit  : 0
% 3.07/1.76  #BackRed      : 1
% 3.07/1.76  
% 3.07/1.76  #Partial instantiations: 0
% 3.07/1.76  #Strategies tried      : 1
% 3.07/1.76  
% 3.07/1.76  Timing (in seconds)
% 3.07/1.76  ----------------------
% 3.07/1.77  Preprocessing        : 0.49
% 3.07/1.77  Parsing              : 0.25
% 3.07/1.77  CNF conversion       : 0.03
% 3.07/1.77  Main loop            : 0.38
% 3.07/1.77  Inferencing          : 0.15
% 3.07/1.77  Reduction            : 0.14
% 3.07/1.77  Demodulation         : 0.12
% 3.07/1.77  BG Simplification    : 0.03
% 3.07/1.77  Subsumption          : 0.04
% 3.07/1.77  Abstraction          : 0.03
% 3.07/1.77  MUC search           : 0.00
% 3.07/1.77  Cooper               : 0.00
% 3.07/1.77  Total                : 0.90
% 3.07/1.77  Index Insertion      : 0.00
% 3.07/1.77  Index Deletion       : 0.00
% 3.07/1.77  Index Matching       : 0.00
% 3.07/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
