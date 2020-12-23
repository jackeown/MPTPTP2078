%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:10 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   47 (  82 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :   30 (  65 expanded)
%              Number of equality atoms :   29 (  64 expanded)
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

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_16,plain,(
    ! [A_26,B_27,C_28,D_29] : k2_xboole_0(k1_tarski(A_26),k1_enumset1(B_27,C_28,D_29)) = k2_enumset1(A_26,B_27,C_28,D_29) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [A_54] : k2_tarski(A_54,A_54) = k1_tarski(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_134,plain,(
    ! [A_68,B_69,C_70] : k2_xboole_0(k1_tarski(A_68),k2_tarski(B_69,C_70)) = k1_enumset1(A_68,B_69,C_70) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_196,plain,(
    ! [A_74,A_75] : k2_xboole_0(k1_tarski(A_74),k1_tarski(A_75)) = k1_enumset1(A_74,A_75,A_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_134])).

tff(c_28,plain,(
    ! [A_55,B_56] : k1_enumset1(A_55,A_55,B_56) = k2_tarski(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_206,plain,(
    ! [A_75] : k2_xboole_0(k1_tarski(A_75),k1_tarski(A_75)) = k2_tarski(A_75,A_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_28])).

tff(c_223,plain,(
    ! [A_76] : k2_xboole_0(k1_tarski(A_76),k1_tarski(A_76)) = k1_tarski(A_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_206])).

tff(c_143,plain,(
    ! [A_68,A_54] : k2_xboole_0(k1_tarski(A_68),k1_tarski(A_54)) = k1_enumset1(A_68,A_54,A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_134])).

tff(c_229,plain,(
    ! [A_76] : k1_enumset1(A_76,A_76,A_76) = k1_tarski(A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_143])).

tff(c_612,plain,(
    ! [B_115,A_117,E_116,D_118,C_120,F_119] : k2_xboole_0(k1_enumset1(A_117,B_115,C_120),k1_enumset1(D_118,E_116,F_119)) = k4_enumset1(A_117,B_115,C_120,D_118,E_116,F_119) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_621,plain,(
    ! [A_76,D_118,E_116,F_119] : k4_enumset1(A_76,A_76,A_76,D_118,E_116,F_119) = k2_xboole_0(k1_tarski(A_76),k1_enumset1(D_118,E_116,F_119)) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_612])).

tff(c_847,plain,(
    ! [A_142,D_143,E_144,F_145] : k4_enumset1(A_142,A_142,A_142,D_143,E_144,F_145) = k2_enumset1(A_142,D_143,E_144,F_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_621])).

tff(c_14,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k1_tarski(A_23),k2_tarski(B_24,C_25)) = k1_enumset1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_268,plain,(
    ! [A_78,B_79,C_80,D_81] : k2_xboole_0(k1_tarski(A_78),k1_enumset1(B_79,C_80,D_81)) = k2_enumset1(A_78,B_79,C_80,D_81) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_296,plain,(
    ! [A_85,A_86] : k2_xboole_0(k1_tarski(A_85),k1_tarski(A_86)) = k2_enumset1(A_85,A_86,A_86,A_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_268])).

tff(c_219,plain,(
    ! [A_75] : k2_xboole_0(k1_tarski(A_75),k1_tarski(A_75)) = k1_tarski(A_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_206])).

tff(c_309,plain,(
    ! [A_86] : k2_enumset1(A_86,A_86,A_86,A_86) = k1_tarski(A_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_219])).

tff(c_784,plain,(
    ! [C_128,D_130,F_127,B_131,A_126,E_129] : k2_xboole_0(k2_enumset1(A_126,B_131,C_128,D_130),k2_tarski(E_129,F_127)) = k4_enumset1(A_126,B_131,C_128,D_130,E_129,F_127) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_793,plain,(
    ! [A_86,E_129,F_127] : k4_enumset1(A_86,A_86,A_86,A_86,E_129,F_127) = k2_xboole_0(k1_tarski(A_86),k2_tarski(E_129,F_127)) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_784])).

tff(c_805,plain,(
    ! [A_86,E_129,F_127] : k4_enumset1(A_86,A_86,A_86,A_86,E_129,F_127) = k1_enumset1(A_86,E_129,F_127) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_793])).

tff(c_854,plain,(
    ! [D_143,E_144,F_145] : k2_enumset1(D_143,D_143,E_144,F_145) = k1_enumset1(D_143,E_144,F_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_847,c_805])).

tff(c_30,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_865,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:13:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.47  
% 2.87/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.47  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.87/1.47  
% 2.87/1.47  %Foreground sorts:
% 2.87/1.47  
% 2.87/1.47  
% 2.87/1.47  %Background operators:
% 2.87/1.47  
% 2.87/1.47  
% 2.87/1.47  %Foreground operators:
% 2.87/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.87/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.87/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.87/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.87/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.87/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.87/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.87/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.87/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.87/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.87/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.87/1.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.87/1.47  
% 2.90/1.48  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.90/1.48  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.90/1.48  tff(f_39, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.90/1.48  tff(f_53, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.90/1.48  tff(f_35, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 2.90/1.48  tff(f_45, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_enumset1)).
% 2.90/1.48  tff(f_56, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.90/1.48  tff(c_16, plain, (![A_26, B_27, C_28, D_29]: (k2_xboole_0(k1_tarski(A_26), k1_enumset1(B_27, C_28, D_29))=k2_enumset1(A_26, B_27, C_28, D_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.90/1.48  tff(c_26, plain, (![A_54]: (k2_tarski(A_54, A_54)=k1_tarski(A_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.90/1.48  tff(c_134, plain, (![A_68, B_69, C_70]: (k2_xboole_0(k1_tarski(A_68), k2_tarski(B_69, C_70))=k1_enumset1(A_68, B_69, C_70))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.90/1.48  tff(c_196, plain, (![A_74, A_75]: (k2_xboole_0(k1_tarski(A_74), k1_tarski(A_75))=k1_enumset1(A_74, A_75, A_75))), inference(superposition, [status(thm), theory('equality')], [c_26, c_134])).
% 2.90/1.48  tff(c_28, plain, (![A_55, B_56]: (k1_enumset1(A_55, A_55, B_56)=k2_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.90/1.48  tff(c_206, plain, (![A_75]: (k2_xboole_0(k1_tarski(A_75), k1_tarski(A_75))=k2_tarski(A_75, A_75))), inference(superposition, [status(thm), theory('equality')], [c_196, c_28])).
% 2.90/1.48  tff(c_223, plain, (![A_76]: (k2_xboole_0(k1_tarski(A_76), k1_tarski(A_76))=k1_tarski(A_76))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_206])).
% 2.90/1.48  tff(c_143, plain, (![A_68, A_54]: (k2_xboole_0(k1_tarski(A_68), k1_tarski(A_54))=k1_enumset1(A_68, A_54, A_54))), inference(superposition, [status(thm), theory('equality')], [c_26, c_134])).
% 2.90/1.48  tff(c_229, plain, (![A_76]: (k1_enumset1(A_76, A_76, A_76)=k1_tarski(A_76))), inference(superposition, [status(thm), theory('equality')], [c_223, c_143])).
% 2.90/1.48  tff(c_612, plain, (![B_115, A_117, E_116, D_118, C_120, F_119]: (k2_xboole_0(k1_enumset1(A_117, B_115, C_120), k1_enumset1(D_118, E_116, F_119))=k4_enumset1(A_117, B_115, C_120, D_118, E_116, F_119))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.90/1.48  tff(c_621, plain, (![A_76, D_118, E_116, F_119]: (k4_enumset1(A_76, A_76, A_76, D_118, E_116, F_119)=k2_xboole_0(k1_tarski(A_76), k1_enumset1(D_118, E_116, F_119)))), inference(superposition, [status(thm), theory('equality')], [c_229, c_612])).
% 2.90/1.48  tff(c_847, plain, (![A_142, D_143, E_144, F_145]: (k4_enumset1(A_142, A_142, A_142, D_143, E_144, F_145)=k2_enumset1(A_142, D_143, E_144, F_145))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_621])).
% 2.90/1.48  tff(c_14, plain, (![A_23, B_24, C_25]: (k2_xboole_0(k1_tarski(A_23), k2_tarski(B_24, C_25))=k1_enumset1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.90/1.48  tff(c_268, plain, (![A_78, B_79, C_80, D_81]: (k2_xboole_0(k1_tarski(A_78), k1_enumset1(B_79, C_80, D_81))=k2_enumset1(A_78, B_79, C_80, D_81))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.90/1.48  tff(c_296, plain, (![A_85, A_86]: (k2_xboole_0(k1_tarski(A_85), k1_tarski(A_86))=k2_enumset1(A_85, A_86, A_86, A_86))), inference(superposition, [status(thm), theory('equality')], [c_229, c_268])).
% 2.90/1.48  tff(c_219, plain, (![A_75]: (k2_xboole_0(k1_tarski(A_75), k1_tarski(A_75))=k1_tarski(A_75))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_206])).
% 2.90/1.48  tff(c_309, plain, (![A_86]: (k2_enumset1(A_86, A_86, A_86, A_86)=k1_tarski(A_86))), inference(superposition, [status(thm), theory('equality')], [c_296, c_219])).
% 2.90/1.48  tff(c_784, plain, (![C_128, D_130, F_127, B_131, A_126, E_129]: (k2_xboole_0(k2_enumset1(A_126, B_131, C_128, D_130), k2_tarski(E_129, F_127))=k4_enumset1(A_126, B_131, C_128, D_130, E_129, F_127))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.90/1.48  tff(c_793, plain, (![A_86, E_129, F_127]: (k4_enumset1(A_86, A_86, A_86, A_86, E_129, F_127)=k2_xboole_0(k1_tarski(A_86), k2_tarski(E_129, F_127)))), inference(superposition, [status(thm), theory('equality')], [c_309, c_784])).
% 2.90/1.48  tff(c_805, plain, (![A_86, E_129, F_127]: (k4_enumset1(A_86, A_86, A_86, A_86, E_129, F_127)=k1_enumset1(A_86, E_129, F_127))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_793])).
% 2.90/1.48  tff(c_854, plain, (![D_143, E_144, F_145]: (k2_enumset1(D_143, D_143, E_144, F_145)=k1_enumset1(D_143, E_144, F_145))), inference(superposition, [status(thm), theory('equality')], [c_847, c_805])).
% 2.90/1.48  tff(c_30, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.90/1.48  tff(c_865, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_854, c_30])).
% 2.90/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.48  
% 2.90/1.48  Inference rules
% 2.90/1.48  ----------------------
% 2.90/1.48  #Ref     : 0
% 2.90/1.48  #Sup     : 203
% 2.90/1.48  #Fact    : 0
% 2.90/1.48  #Define  : 0
% 2.90/1.48  #Split   : 0
% 2.90/1.48  #Chain   : 0
% 2.90/1.48  #Close   : 0
% 2.90/1.48  
% 2.90/1.48  Ordering : KBO
% 2.90/1.48  
% 2.90/1.48  Simplification rules
% 2.90/1.48  ----------------------
% 2.90/1.48  #Subsume      : 10
% 2.90/1.48  #Demod        : 82
% 2.90/1.48  #Tautology    : 119
% 2.90/1.48  #SimpNegUnit  : 0
% 2.90/1.48  #BackRed      : 1
% 2.90/1.48  
% 2.90/1.48  #Partial instantiations: 0
% 2.90/1.48  #Strategies tried      : 1
% 2.90/1.48  
% 2.90/1.48  Timing (in seconds)
% 2.90/1.48  ----------------------
% 2.90/1.48  Preprocessing        : 0.34
% 2.90/1.48  Parsing              : 0.18
% 2.90/1.48  CNF conversion       : 0.02
% 2.90/1.48  Main loop            : 0.32
% 2.90/1.48  Inferencing          : 0.13
% 2.90/1.48  Reduction            : 0.11
% 2.90/1.48  Demodulation         : 0.09
% 2.90/1.48  BG Simplification    : 0.02
% 2.90/1.48  Subsumption          : 0.04
% 2.90/1.48  Abstraction          : 0.02
% 2.90/1.48  MUC search           : 0.00
% 2.90/1.48  Cooper               : 0.00
% 2.90/1.48  Total                : 0.68
% 2.90/1.48  Index Insertion      : 0.00
% 2.90/1.48  Index Deletion       : 0.00
% 2.90/1.48  Index Matching       : 0.00
% 2.90/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
