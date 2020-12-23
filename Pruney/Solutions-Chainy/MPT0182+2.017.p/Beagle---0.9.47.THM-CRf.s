%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:44 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   49 (  55 expanded)
%              Number of leaves         :   28 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :   31 (  37 expanded)
%              Number of equality atoms :   30 (  36 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_201,plain,(
    ! [A_89,B_90,C_91] : k2_xboole_0(k1_tarski(A_89),k2_tarski(B_90,C_91)) = k1_enumset1(A_89,B_90,C_91) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_216,plain,(
    ! [B_90,C_91,A_89] : k2_xboole_0(k2_tarski(B_90,C_91),k1_tarski(A_89)) = k1_enumset1(A_89,B_90,C_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_201])).

tff(c_22,plain,(
    ! [A_44,B_45,C_46] : k2_enumset1(A_44,A_44,B_45,C_46) = k1_enumset1(A_44,B_45,C_46) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_42,B_43] : k1_enumset1(A_42,A_42,B_43) = k2_tarski(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_47,B_48,C_49,D_50] : k3_enumset1(A_47,A_47,B_48,C_49,D_50) = k2_enumset1(A_47,B_48,C_49,D_50) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [B_52,E_55,C_53,D_54,A_51] : k4_enumset1(A_51,A_51,B_52,C_53,D_54,E_55) = k3_enumset1(A_51,B_52,C_53,D_54,E_55) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [D_59,A_56,B_57,F_61,C_58,E_60] : k5_enumset1(A_56,A_56,B_57,C_58,D_59,E_60,F_61) = k4_enumset1(A_56,B_57,C_58,D_59,E_60,F_61) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_521,plain,(
    ! [E_127,B_126,F_130,A_128,D_129,G_125,C_131] : k2_xboole_0(k4_enumset1(A_128,B_126,C_131,D_129,E_127,F_130),k1_tarski(G_125)) = k5_enumset1(A_128,B_126,C_131,D_129,E_127,F_130,G_125) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_536,plain,(
    ! [B_52,E_55,C_53,D_54,A_51,G_125] : k5_enumset1(A_51,A_51,B_52,C_53,D_54,E_55,G_125) = k2_xboole_0(k3_enumset1(A_51,B_52,C_53,D_54,E_55),k1_tarski(G_125)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_521])).

tff(c_571,plain,(
    ! [G_144,E_145,D_143,B_141,C_142,A_140] : k2_xboole_0(k3_enumset1(A_140,B_141,C_142,D_143,E_145),k1_tarski(G_144)) = k4_enumset1(A_140,B_141,C_142,D_143,E_145,G_144) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_536])).

tff(c_586,plain,(
    ! [A_47,G_144,D_50,C_49,B_48] : k4_enumset1(A_47,A_47,B_48,C_49,D_50,G_144) = k2_xboole_0(k2_enumset1(A_47,B_48,C_49,D_50),k1_tarski(G_144)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_571])).

tff(c_596,plain,(
    ! [G_148,D_147,B_149,A_146,C_150] : k2_xboole_0(k2_enumset1(A_146,B_149,C_150,D_147),k1_tarski(G_148)) = k3_enumset1(A_146,B_149,C_150,D_147,G_148) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_586])).

tff(c_611,plain,(
    ! [A_44,B_45,C_46,G_148] : k3_enumset1(A_44,A_44,B_45,C_46,G_148) = k2_xboole_0(k1_enumset1(A_44,B_45,C_46),k1_tarski(G_148)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_596])).

tff(c_621,plain,(
    ! [A_151,B_152,C_153,G_154] : k2_xboole_0(k1_enumset1(A_151,B_152,C_153),k1_tarski(G_154)) = k2_enumset1(A_151,B_152,C_153,G_154) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_611])).

tff(c_660,plain,(
    ! [A_42,B_43,G_154] : k2_xboole_0(k2_tarski(A_42,B_43),k1_tarski(G_154)) = k2_enumset1(A_42,A_42,B_43,G_154) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_621])).

tff(c_670,plain,(
    ! [G_154,A_42,B_43] : k1_enumset1(G_154,A_42,B_43) = k1_enumset1(A_42,B_43,G_154) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_22,c_660])).

tff(c_32,plain,(
    ! [A_69,C_71,B_70] : k1_enumset1(A_69,C_71,B_70) = k1_enumset1(A_69,B_70,C_71) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_35,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:26:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.37  
% 2.72/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.37  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.72/1.37  
% 2.72/1.37  %Foreground sorts:
% 2.72/1.37  
% 2.72/1.37  
% 2.72/1.37  %Background operators:
% 2.72/1.37  
% 2.72/1.37  
% 2.72/1.37  %Foreground operators:
% 2.72/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.72/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.72/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.72/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.72/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.72/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.72/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.72/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.72/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.72/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.37  
% 2.72/1.38  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.72/1.38  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.72/1.38  tff(f_47, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.72/1.38  tff(f_45, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.72/1.38  tff(f_49, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.72/1.38  tff(f_51, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.72/1.38  tff(f_53, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.72/1.38  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 2.72/1.38  tff(f_57, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 2.72/1.38  tff(f_60, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_enumset1)).
% 2.72/1.38  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.72/1.38  tff(c_201, plain, (![A_89, B_90, C_91]: (k2_xboole_0(k1_tarski(A_89), k2_tarski(B_90, C_91))=k1_enumset1(A_89, B_90, C_91))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.72/1.38  tff(c_216, plain, (![B_90, C_91, A_89]: (k2_xboole_0(k2_tarski(B_90, C_91), k1_tarski(A_89))=k1_enumset1(A_89, B_90, C_91))), inference(superposition, [status(thm), theory('equality')], [c_2, c_201])).
% 2.72/1.38  tff(c_22, plain, (![A_44, B_45, C_46]: (k2_enumset1(A_44, A_44, B_45, C_46)=k1_enumset1(A_44, B_45, C_46))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.72/1.38  tff(c_20, plain, (![A_42, B_43]: (k1_enumset1(A_42, A_42, B_43)=k2_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.72/1.38  tff(c_24, plain, (![A_47, B_48, C_49, D_50]: (k3_enumset1(A_47, A_47, B_48, C_49, D_50)=k2_enumset1(A_47, B_48, C_49, D_50))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.72/1.38  tff(c_26, plain, (![B_52, E_55, C_53, D_54, A_51]: (k4_enumset1(A_51, A_51, B_52, C_53, D_54, E_55)=k3_enumset1(A_51, B_52, C_53, D_54, E_55))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.72/1.38  tff(c_28, plain, (![D_59, A_56, B_57, F_61, C_58, E_60]: (k5_enumset1(A_56, A_56, B_57, C_58, D_59, E_60, F_61)=k4_enumset1(A_56, B_57, C_58, D_59, E_60, F_61))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.72/1.38  tff(c_521, plain, (![E_127, B_126, F_130, A_128, D_129, G_125, C_131]: (k2_xboole_0(k4_enumset1(A_128, B_126, C_131, D_129, E_127, F_130), k1_tarski(G_125))=k5_enumset1(A_128, B_126, C_131, D_129, E_127, F_130, G_125))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.72/1.38  tff(c_536, plain, (![B_52, E_55, C_53, D_54, A_51, G_125]: (k5_enumset1(A_51, A_51, B_52, C_53, D_54, E_55, G_125)=k2_xboole_0(k3_enumset1(A_51, B_52, C_53, D_54, E_55), k1_tarski(G_125)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_521])).
% 2.72/1.38  tff(c_571, plain, (![G_144, E_145, D_143, B_141, C_142, A_140]: (k2_xboole_0(k3_enumset1(A_140, B_141, C_142, D_143, E_145), k1_tarski(G_144))=k4_enumset1(A_140, B_141, C_142, D_143, E_145, G_144))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_536])).
% 2.72/1.38  tff(c_586, plain, (![A_47, G_144, D_50, C_49, B_48]: (k4_enumset1(A_47, A_47, B_48, C_49, D_50, G_144)=k2_xboole_0(k2_enumset1(A_47, B_48, C_49, D_50), k1_tarski(G_144)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_571])).
% 2.72/1.38  tff(c_596, plain, (![G_148, D_147, B_149, A_146, C_150]: (k2_xboole_0(k2_enumset1(A_146, B_149, C_150, D_147), k1_tarski(G_148))=k3_enumset1(A_146, B_149, C_150, D_147, G_148))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_586])).
% 2.72/1.38  tff(c_611, plain, (![A_44, B_45, C_46, G_148]: (k3_enumset1(A_44, A_44, B_45, C_46, G_148)=k2_xboole_0(k1_enumset1(A_44, B_45, C_46), k1_tarski(G_148)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_596])).
% 2.72/1.38  tff(c_621, plain, (![A_151, B_152, C_153, G_154]: (k2_xboole_0(k1_enumset1(A_151, B_152, C_153), k1_tarski(G_154))=k2_enumset1(A_151, B_152, C_153, G_154))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_611])).
% 2.72/1.38  tff(c_660, plain, (![A_42, B_43, G_154]: (k2_xboole_0(k2_tarski(A_42, B_43), k1_tarski(G_154))=k2_enumset1(A_42, A_42, B_43, G_154))), inference(superposition, [status(thm), theory('equality')], [c_20, c_621])).
% 2.72/1.38  tff(c_670, plain, (![G_154, A_42, B_43]: (k1_enumset1(G_154, A_42, B_43)=k1_enumset1(A_42, B_43, G_154))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_22, c_660])).
% 2.72/1.38  tff(c_32, plain, (![A_69, C_71, B_70]: (k1_enumset1(A_69, C_71, B_70)=k1_enumset1(A_69, B_70, C_71))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.72/1.38  tff(c_34, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.72/1.38  tff(c_35, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34])).
% 2.72/1.38  tff(c_697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_670, c_35])).
% 2.72/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.38  
% 2.72/1.38  Inference rules
% 2.72/1.38  ----------------------
% 2.72/1.38  #Ref     : 0
% 2.72/1.38  #Sup     : 170
% 2.72/1.38  #Fact    : 0
% 2.72/1.38  #Define  : 0
% 2.72/1.38  #Split   : 0
% 2.72/1.38  #Chain   : 0
% 2.72/1.38  #Close   : 0
% 2.72/1.38  
% 2.72/1.38  Ordering : KBO
% 2.72/1.38  
% 2.72/1.38  Simplification rules
% 2.72/1.38  ----------------------
% 2.72/1.38  #Subsume      : 31
% 2.72/1.38  #Demod        : 54
% 2.72/1.38  #Tautology    : 95
% 2.72/1.38  #SimpNegUnit  : 0
% 2.72/1.38  #BackRed      : 1
% 2.72/1.38  
% 2.72/1.38  #Partial instantiations: 0
% 2.72/1.38  #Strategies tried      : 1
% 2.72/1.38  
% 2.72/1.38  Timing (in seconds)
% 2.72/1.38  ----------------------
% 2.72/1.38  Preprocessing        : 0.32
% 2.72/1.38  Parsing              : 0.17
% 2.72/1.38  CNF conversion       : 0.02
% 2.72/1.38  Main loop            : 0.30
% 2.72/1.38  Inferencing          : 0.12
% 2.72/1.38  Reduction            : 0.11
% 2.72/1.38  Demodulation         : 0.09
% 2.72/1.38  BG Simplification    : 0.02
% 2.72/1.38  Subsumption          : 0.04
% 2.72/1.38  Abstraction          : 0.02
% 2.72/1.38  MUC search           : 0.00
% 2.72/1.38  Cooper               : 0.00
% 2.72/1.38  Total                : 0.65
% 2.72/1.38  Index Insertion      : 0.00
% 2.72/1.38  Index Deletion       : 0.00
% 2.72/1.38  Index Matching       : 0.00
% 2.72/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
