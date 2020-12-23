%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:54 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
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

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_6,plain,(
    ! [B_6,C_7,A_5] : k1_enumset1(B_6,C_7,A_5) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_49,B_50,C_51,D_52] : k3_enumset1(A_49,A_49,B_50,C_51,D_52) = k2_enumset1(A_49,B_50,C_51,D_52) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_46,B_47,C_48] : k2_enumset1(A_46,A_46,B_47,C_48) = k1_enumset1(A_46,B_47,C_48) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_53,D_56,E_57,C_55,B_54] : k4_enumset1(A_53,A_53,B_54,C_55,D_56,E_57) = k3_enumset1(A_53,B_54,C_55,D_56,E_57) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [B_59,A_58,F_63,E_62,D_61,C_60] : k5_enumset1(A_58,A_58,B_59,C_60,D_61,E_62,F_63) = k4_enumset1(A_58,B_59,C_60,D_61,E_62,F_63) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_331,plain,(
    ! [B_118,G_117,A_119,D_121,C_123,F_122,E_120] : k2_xboole_0(k4_enumset1(A_119,B_118,C_123,D_121,E_120,F_122),k1_tarski(G_117)) = k5_enumset1(A_119,B_118,C_123,D_121,E_120,F_122,G_117) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_340,plain,(
    ! [G_117,A_53,D_56,E_57,C_55,B_54] : k5_enumset1(A_53,A_53,B_54,C_55,D_56,E_57,G_117) = k2_xboole_0(k3_enumset1(A_53,B_54,C_55,D_56,E_57),k1_tarski(G_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_331])).

tff(c_344,plain,(
    ! [D_127,B_129,E_126,G_128,A_125,C_124] : k2_xboole_0(k3_enumset1(A_125,B_129,C_124,D_127,E_126),k1_tarski(G_128)) = k4_enumset1(A_125,B_129,C_124,D_127,E_126,G_128) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_340])).

tff(c_353,plain,(
    ! [D_52,C_51,B_50,A_49,G_128] : k4_enumset1(A_49,A_49,B_50,C_51,D_52,G_128) = k2_xboole_0(k2_enumset1(A_49,B_50,C_51,D_52),k1_tarski(G_128)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_344])).

tff(c_357,plain,(
    ! [A_132,D_133,C_130,B_131,G_134] : k2_xboole_0(k2_enumset1(A_132,B_131,C_130,D_133),k1_tarski(G_134)) = k3_enumset1(A_132,B_131,C_130,D_133,G_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_353])).

tff(c_375,plain,(
    ! [A_46,B_47,C_48,G_134] : k3_enumset1(A_46,A_46,B_47,C_48,G_134) = k2_xboole_0(k1_enumset1(A_46,B_47,C_48),k1_tarski(G_134)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_357])).

tff(c_396,plain,(
    ! [A_143,B_144,C_145,G_146] : k2_xboole_0(k1_enumset1(A_143,B_144,C_145),k1_tarski(G_146)) = k2_enumset1(A_143,B_144,C_145,G_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_375])).

tff(c_533,plain,(
    ! [A_167,B_168,C_169,G_170] : k2_xboole_0(k1_enumset1(A_167,B_168,C_169),k1_tarski(G_170)) = k2_enumset1(B_168,C_169,A_167,G_170) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_396])).

tff(c_378,plain,(
    ! [A_46,B_47,C_48,G_134] : k2_xboole_0(k1_enumset1(A_46,B_47,C_48),k1_tarski(G_134)) = k2_enumset1(A_46,B_47,C_48,G_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_375])).

tff(c_539,plain,(
    ! [B_168,C_169,A_167,G_170] : k2_enumset1(B_168,C_169,A_167,G_170) = k2_enumset1(A_167,B_168,C_169,G_170) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_378])).

tff(c_8,plain,(
    ! [A_8,C_10,B_9,D_11] : k2_enumset1(A_8,C_10,B_9,D_11) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_33,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_32])).

tff(c_569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_539,c_33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:51:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.34  
% 2.42/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.34  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.42/1.34  
% 2.42/1.34  %Foreground sorts:
% 2.42/1.34  
% 2.42/1.34  
% 2.42/1.34  %Background operators:
% 2.42/1.34  
% 2.42/1.34  
% 2.42/1.34  %Foreground operators:
% 2.42/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.42/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.42/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.42/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.42/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.42/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.42/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.42/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.42/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.42/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.42/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.42/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.42/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.42/1.34  
% 2.42/1.35  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_enumset1)).
% 2.42/1.35  tff(f_49, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.42/1.35  tff(f_47, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.42/1.35  tff(f_51, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.42/1.35  tff(f_53, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.42/1.35  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 2.42/1.35  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 2.42/1.35  tff(f_58, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_enumset1)).
% 2.42/1.35  tff(c_6, plain, (![B_6, C_7, A_5]: (k1_enumset1(B_6, C_7, A_5)=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.42/1.35  tff(c_24, plain, (![A_49, B_50, C_51, D_52]: (k3_enumset1(A_49, A_49, B_50, C_51, D_52)=k2_enumset1(A_49, B_50, C_51, D_52))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.42/1.35  tff(c_22, plain, (![A_46, B_47, C_48]: (k2_enumset1(A_46, A_46, B_47, C_48)=k1_enumset1(A_46, B_47, C_48))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.42/1.35  tff(c_26, plain, (![A_53, D_56, E_57, C_55, B_54]: (k4_enumset1(A_53, A_53, B_54, C_55, D_56, E_57)=k3_enumset1(A_53, B_54, C_55, D_56, E_57))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.42/1.35  tff(c_28, plain, (![B_59, A_58, F_63, E_62, D_61, C_60]: (k5_enumset1(A_58, A_58, B_59, C_60, D_61, E_62, F_63)=k4_enumset1(A_58, B_59, C_60, D_61, E_62, F_63))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.42/1.35  tff(c_331, plain, (![B_118, G_117, A_119, D_121, C_123, F_122, E_120]: (k2_xboole_0(k4_enumset1(A_119, B_118, C_123, D_121, E_120, F_122), k1_tarski(G_117))=k5_enumset1(A_119, B_118, C_123, D_121, E_120, F_122, G_117))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.42/1.35  tff(c_340, plain, (![G_117, A_53, D_56, E_57, C_55, B_54]: (k5_enumset1(A_53, A_53, B_54, C_55, D_56, E_57, G_117)=k2_xboole_0(k3_enumset1(A_53, B_54, C_55, D_56, E_57), k1_tarski(G_117)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_331])).
% 2.42/1.35  tff(c_344, plain, (![D_127, B_129, E_126, G_128, A_125, C_124]: (k2_xboole_0(k3_enumset1(A_125, B_129, C_124, D_127, E_126), k1_tarski(G_128))=k4_enumset1(A_125, B_129, C_124, D_127, E_126, G_128))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_340])).
% 2.42/1.35  tff(c_353, plain, (![D_52, C_51, B_50, A_49, G_128]: (k4_enumset1(A_49, A_49, B_50, C_51, D_52, G_128)=k2_xboole_0(k2_enumset1(A_49, B_50, C_51, D_52), k1_tarski(G_128)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_344])).
% 2.42/1.35  tff(c_357, plain, (![A_132, D_133, C_130, B_131, G_134]: (k2_xboole_0(k2_enumset1(A_132, B_131, C_130, D_133), k1_tarski(G_134))=k3_enumset1(A_132, B_131, C_130, D_133, G_134))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_353])).
% 2.42/1.35  tff(c_375, plain, (![A_46, B_47, C_48, G_134]: (k3_enumset1(A_46, A_46, B_47, C_48, G_134)=k2_xboole_0(k1_enumset1(A_46, B_47, C_48), k1_tarski(G_134)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_357])).
% 2.42/1.35  tff(c_396, plain, (![A_143, B_144, C_145, G_146]: (k2_xboole_0(k1_enumset1(A_143, B_144, C_145), k1_tarski(G_146))=k2_enumset1(A_143, B_144, C_145, G_146))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_375])).
% 2.42/1.35  tff(c_533, plain, (![A_167, B_168, C_169, G_170]: (k2_xboole_0(k1_enumset1(A_167, B_168, C_169), k1_tarski(G_170))=k2_enumset1(B_168, C_169, A_167, G_170))), inference(superposition, [status(thm), theory('equality')], [c_6, c_396])).
% 2.42/1.35  tff(c_378, plain, (![A_46, B_47, C_48, G_134]: (k2_xboole_0(k1_enumset1(A_46, B_47, C_48), k1_tarski(G_134))=k2_enumset1(A_46, B_47, C_48, G_134))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_375])).
% 2.42/1.35  tff(c_539, plain, (![B_168, C_169, A_167, G_170]: (k2_enumset1(B_168, C_169, A_167, G_170)=k2_enumset1(A_167, B_168, C_169, G_170))), inference(superposition, [status(thm), theory('equality')], [c_533, c_378])).
% 2.42/1.35  tff(c_8, plain, (![A_8, C_10, B_9, D_11]: (k2_enumset1(A_8, C_10, B_9, D_11)=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.42/1.35  tff(c_32, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.42/1.35  tff(c_33, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_32])).
% 2.42/1.35  tff(c_569, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_539, c_539, c_33])).
% 2.42/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.35  
% 2.42/1.35  Inference rules
% 2.42/1.35  ----------------------
% 2.42/1.35  #Ref     : 0
% 2.42/1.35  #Sup     : 126
% 2.42/1.35  #Fact    : 0
% 2.42/1.35  #Define  : 0
% 2.42/1.35  #Split   : 0
% 2.42/1.35  #Chain   : 0
% 2.42/1.35  #Close   : 0
% 2.42/1.35  
% 2.42/1.35  Ordering : KBO
% 2.42/1.35  
% 2.42/1.35  Simplification rules
% 2.42/1.35  ----------------------
% 2.42/1.35  #Subsume      : 4
% 2.42/1.35  #Demod        : 68
% 2.42/1.35  #Tautology    : 94
% 2.42/1.35  #SimpNegUnit  : 0
% 2.42/1.35  #BackRed      : 1
% 2.42/1.35  
% 2.42/1.35  #Partial instantiations: 0
% 2.42/1.35  #Strategies tried      : 1
% 2.42/1.35  
% 2.42/1.35  Timing (in seconds)
% 2.42/1.35  ----------------------
% 2.42/1.35  Preprocessing        : 0.31
% 2.42/1.35  Parsing              : 0.16
% 2.42/1.35  CNF conversion       : 0.02
% 2.42/1.36  Main loop            : 0.25
% 2.42/1.36  Inferencing          : 0.10
% 2.42/1.36  Reduction            : 0.09
% 2.42/1.36  Demodulation         : 0.08
% 2.42/1.36  BG Simplification    : 0.02
% 2.42/1.36  Subsumption          : 0.03
% 2.42/1.36  Abstraction          : 0.02
% 2.42/1.36  MUC search           : 0.00
% 2.42/1.36  Cooper               : 0.00
% 2.42/1.36  Total                : 0.59
% 2.42/1.36  Index Insertion      : 0.00
% 2.42/1.36  Index Deletion       : 0.00
% 2.42/1.36  Index Matching       : 0.00
% 2.42/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
