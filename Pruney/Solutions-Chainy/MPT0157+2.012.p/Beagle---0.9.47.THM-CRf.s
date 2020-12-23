%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:18 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   51 (  64 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :   33 (  46 expanded)
%              Number of equality atoms :   32 (  45 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_enumset1(A,B,C),k3_enumset1(D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(c_6,plain,(
    ! [E_12,D_11,A_8,C_10,B_9,F_13] : k2_xboole_0(k1_tarski(A_8),k3_enumset1(B_9,C_10,D_11,E_12,F_13)) = k4_enumset1(A_8,B_9,C_10,D_11,E_12,F_13) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_30] : k2_tarski(A_30,A_30) = k1_tarski(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_3,D_6,C_5,E_7,B_4] : k2_xboole_0(k2_tarski(A_3,B_4),k1_enumset1(C_5,D_6,E_7)) = k3_enumset1(A_3,B_4,C_5,D_6,E_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_31,B_32] : k1_enumset1(A_31,A_31,B_32) = k2_tarski(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_66,plain,(
    ! [B_56,E_52,D_53,C_55,A_54] : k2_xboole_0(k2_tarski(A_54,B_56),k1_enumset1(C_55,D_53,E_52)) = k3_enumset1(A_54,B_56,C_55,D_53,E_52) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_495,plain,(
    ! [A_101,B_102,A_103,B_104] : k3_enumset1(A_101,B_102,A_103,A_103,B_104) = k2_xboole_0(k2_tarski(A_101,B_102),k2_tarski(A_103,B_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_66])).

tff(c_565,plain,(
    ! [A_105,A_106,B_107] : k3_enumset1(A_105,A_105,A_106,A_106,B_107) = k2_xboole_0(k1_tarski(A_105),k2_tarski(A_106,B_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_495])).

tff(c_18,plain,(
    ! [A_36,B_37,C_38,D_39] : k3_enumset1(A_36,A_36,B_37,C_38,D_39) = k2_enumset1(A_36,B_37,C_38,D_39) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_78,plain,(
    ! [A_30,C_55,D_53,E_52] : k3_enumset1(A_30,A_30,C_55,D_53,E_52) = k2_xboole_0(k1_tarski(A_30),k1_enumset1(C_55,D_53,E_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_66])).

tff(c_82,plain,(
    ! [A_57,C_58,D_59,E_60] : k2_xboole_0(k1_tarski(A_57),k1_enumset1(C_58,D_59,E_60)) = k2_enumset1(A_57,C_58,D_59,E_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_78])).

tff(c_94,plain,(
    ! [A_61,A_62,B_63] : k2_xboole_0(k1_tarski(A_61),k2_tarski(A_62,B_63)) = k2_enumset1(A_61,A_62,A_62,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_82])).

tff(c_16,plain,(
    ! [A_33,B_34,C_35] : k2_enumset1(A_33,A_33,B_34,C_35) = k1_enumset1(A_33,B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_104,plain,(
    ! [A_62,B_63] : k2_xboole_0(k1_tarski(A_62),k2_tarski(A_62,B_63)) = k1_enumset1(A_62,A_62,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_16])).

tff(c_120,plain,(
    ! [A_62,B_63] : k2_xboole_0(k1_tarski(A_62),k2_tarski(A_62,B_63)) = k2_tarski(A_62,B_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_104])).

tff(c_653,plain,(
    ! [A_108,B_109] : k3_enumset1(A_108,A_108,A_108,A_108,B_109) = k2_tarski(A_108,B_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_565,c_120])).

tff(c_10,plain,(
    ! [G_28,E_26,F_27,H_29,A_22,B_23,D_25,C_24] : k2_xboole_0(k3_enumset1(A_22,B_23,C_24,D_25,E_26),k1_enumset1(F_27,G_28,H_29)) = k6_enumset1(A_22,B_23,C_24,D_25,E_26,F_27,G_28,H_29) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_680,plain,(
    ! [G_28,A_108,F_27,B_109,H_29] : k6_enumset1(A_108,A_108,A_108,A_108,B_109,F_27,G_28,H_29) = k2_xboole_0(k2_tarski(A_108,B_109),k1_enumset1(F_27,G_28,H_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_10])).

tff(c_2086,plain,(
    ! [H_190,B_191,G_189,A_188,F_187] : k6_enumset1(A_188,A_188,A_188,A_188,B_191,F_187,G_189,H_190) = k3_enumset1(A_188,B_191,F_187,G_189,H_190) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_680])).

tff(c_332,plain,(
    ! [C_92,E_88,F_89,G_91,B_93,H_87,A_94,D_90] : k2_xboole_0(k1_enumset1(A_94,B_93,C_92),k3_enumset1(D_90,E_88,F_89,G_91,H_87)) = k6_enumset1(A_94,B_93,C_92,D_90,E_88,F_89,G_91,H_87) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_347,plain,(
    ! [A_31,E_88,F_89,B_32,G_91,H_87,D_90] : k6_enumset1(A_31,A_31,B_32,D_90,E_88,F_89,G_91,H_87) = k2_xboole_0(k2_tarski(A_31,B_32),k3_enumset1(D_90,E_88,F_89,G_91,H_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_332])).

tff(c_2096,plain,(
    ! [H_190,B_191,G_189,A_188,F_187] : k2_xboole_0(k2_tarski(A_188,A_188),k3_enumset1(A_188,B_191,F_187,G_189,H_190)) = k3_enumset1(A_188,B_191,F_187,G_189,H_190) ),
    inference(superposition,[status(thm),theory(equality)],[c_2086,c_347])).

tff(c_2125,plain,(
    ! [H_190,B_191,G_189,A_188,F_187] : k4_enumset1(A_188,A_188,B_191,F_187,G_189,H_190) = k3_enumset1(A_188,B_191,F_187,G_189,H_190) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12,c_2096])).

tff(c_20,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2125,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n001.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 17:16:00 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.56  
% 3.64/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.56  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.64/1.56  
% 3.64/1.56  %Foreground sorts:
% 3.64/1.56  
% 3.64/1.56  
% 3.64/1.56  %Background operators:
% 3.64/1.56  
% 3.64/1.56  
% 3.64/1.56  %Foreground operators:
% 3.64/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.64/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.64/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.64/1.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.64/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.64/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.64/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.64/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.64/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.64/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.64/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.64/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.64/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.64/1.56  
% 3.64/1.57  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 3.64/1.57  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.64/1.57  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 3.64/1.57  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.64/1.57  tff(f_43, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.64/1.57  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.64/1.57  tff(f_35, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 3.64/1.57  tff(f_33, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_enumset1(A, B, C), k3_enumset1(D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_enumset1)).
% 3.64/1.57  tff(f_46, negated_conjecture, ~(![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.64/1.57  tff(c_6, plain, (![E_12, D_11, A_8, C_10, B_9, F_13]: (k2_xboole_0(k1_tarski(A_8), k3_enumset1(B_9, C_10, D_11, E_12, F_13))=k4_enumset1(A_8, B_9, C_10, D_11, E_12, F_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.64/1.57  tff(c_12, plain, (![A_30]: (k2_tarski(A_30, A_30)=k1_tarski(A_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.64/1.57  tff(c_4, plain, (![A_3, D_6, C_5, E_7, B_4]: (k2_xboole_0(k2_tarski(A_3, B_4), k1_enumset1(C_5, D_6, E_7))=k3_enumset1(A_3, B_4, C_5, D_6, E_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.64/1.57  tff(c_14, plain, (![A_31, B_32]: (k1_enumset1(A_31, A_31, B_32)=k2_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.64/1.57  tff(c_66, plain, (![B_56, E_52, D_53, C_55, A_54]: (k2_xboole_0(k2_tarski(A_54, B_56), k1_enumset1(C_55, D_53, E_52))=k3_enumset1(A_54, B_56, C_55, D_53, E_52))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.64/1.57  tff(c_495, plain, (![A_101, B_102, A_103, B_104]: (k3_enumset1(A_101, B_102, A_103, A_103, B_104)=k2_xboole_0(k2_tarski(A_101, B_102), k2_tarski(A_103, B_104)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_66])).
% 3.64/1.57  tff(c_565, plain, (![A_105, A_106, B_107]: (k3_enumset1(A_105, A_105, A_106, A_106, B_107)=k2_xboole_0(k1_tarski(A_105), k2_tarski(A_106, B_107)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_495])).
% 3.64/1.57  tff(c_18, plain, (![A_36, B_37, C_38, D_39]: (k3_enumset1(A_36, A_36, B_37, C_38, D_39)=k2_enumset1(A_36, B_37, C_38, D_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.64/1.57  tff(c_78, plain, (![A_30, C_55, D_53, E_52]: (k3_enumset1(A_30, A_30, C_55, D_53, E_52)=k2_xboole_0(k1_tarski(A_30), k1_enumset1(C_55, D_53, E_52)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_66])).
% 3.64/1.57  tff(c_82, plain, (![A_57, C_58, D_59, E_60]: (k2_xboole_0(k1_tarski(A_57), k1_enumset1(C_58, D_59, E_60))=k2_enumset1(A_57, C_58, D_59, E_60))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_78])).
% 3.64/1.57  tff(c_94, plain, (![A_61, A_62, B_63]: (k2_xboole_0(k1_tarski(A_61), k2_tarski(A_62, B_63))=k2_enumset1(A_61, A_62, A_62, B_63))), inference(superposition, [status(thm), theory('equality')], [c_14, c_82])).
% 3.64/1.57  tff(c_16, plain, (![A_33, B_34, C_35]: (k2_enumset1(A_33, A_33, B_34, C_35)=k1_enumset1(A_33, B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.64/1.57  tff(c_104, plain, (![A_62, B_63]: (k2_xboole_0(k1_tarski(A_62), k2_tarski(A_62, B_63))=k1_enumset1(A_62, A_62, B_63))), inference(superposition, [status(thm), theory('equality')], [c_94, c_16])).
% 3.64/1.57  tff(c_120, plain, (![A_62, B_63]: (k2_xboole_0(k1_tarski(A_62), k2_tarski(A_62, B_63))=k2_tarski(A_62, B_63))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_104])).
% 3.64/1.57  tff(c_653, plain, (![A_108, B_109]: (k3_enumset1(A_108, A_108, A_108, A_108, B_109)=k2_tarski(A_108, B_109))), inference(superposition, [status(thm), theory('equality')], [c_565, c_120])).
% 3.64/1.57  tff(c_10, plain, (![G_28, E_26, F_27, H_29, A_22, B_23, D_25, C_24]: (k2_xboole_0(k3_enumset1(A_22, B_23, C_24, D_25, E_26), k1_enumset1(F_27, G_28, H_29))=k6_enumset1(A_22, B_23, C_24, D_25, E_26, F_27, G_28, H_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.64/1.57  tff(c_680, plain, (![G_28, A_108, F_27, B_109, H_29]: (k6_enumset1(A_108, A_108, A_108, A_108, B_109, F_27, G_28, H_29)=k2_xboole_0(k2_tarski(A_108, B_109), k1_enumset1(F_27, G_28, H_29)))), inference(superposition, [status(thm), theory('equality')], [c_653, c_10])).
% 3.64/1.57  tff(c_2086, plain, (![H_190, B_191, G_189, A_188, F_187]: (k6_enumset1(A_188, A_188, A_188, A_188, B_191, F_187, G_189, H_190)=k3_enumset1(A_188, B_191, F_187, G_189, H_190))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_680])).
% 3.64/1.57  tff(c_332, plain, (![C_92, E_88, F_89, G_91, B_93, H_87, A_94, D_90]: (k2_xboole_0(k1_enumset1(A_94, B_93, C_92), k3_enumset1(D_90, E_88, F_89, G_91, H_87))=k6_enumset1(A_94, B_93, C_92, D_90, E_88, F_89, G_91, H_87))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.64/1.57  tff(c_347, plain, (![A_31, E_88, F_89, B_32, G_91, H_87, D_90]: (k6_enumset1(A_31, A_31, B_32, D_90, E_88, F_89, G_91, H_87)=k2_xboole_0(k2_tarski(A_31, B_32), k3_enumset1(D_90, E_88, F_89, G_91, H_87)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_332])).
% 3.64/1.57  tff(c_2096, plain, (![H_190, B_191, G_189, A_188, F_187]: (k2_xboole_0(k2_tarski(A_188, A_188), k3_enumset1(A_188, B_191, F_187, G_189, H_190))=k3_enumset1(A_188, B_191, F_187, G_189, H_190))), inference(superposition, [status(thm), theory('equality')], [c_2086, c_347])).
% 3.64/1.57  tff(c_2125, plain, (![H_190, B_191, G_189, A_188, F_187]: (k4_enumset1(A_188, A_188, B_191, F_187, G_189, H_190)=k3_enumset1(A_188, B_191, F_187, G_189, H_190))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12, c_2096])).
% 3.64/1.57  tff(c_20, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.64/1.57  tff(c_2135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2125, c_20])).
% 3.64/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.57  
% 3.64/1.57  Inference rules
% 3.64/1.57  ----------------------
% 3.64/1.57  #Ref     : 0
% 3.64/1.57  #Sup     : 504
% 3.64/1.57  #Fact    : 0
% 3.64/1.57  #Define  : 0
% 3.64/1.57  #Split   : 0
% 3.64/1.57  #Chain   : 0
% 3.64/1.57  #Close   : 0
% 3.64/1.57  
% 3.64/1.57  Ordering : KBO
% 3.64/1.57  
% 3.64/1.57  Simplification rules
% 3.64/1.58  ----------------------
% 3.64/1.58  #Subsume      : 63
% 3.64/1.58  #Demod        : 470
% 3.64/1.58  #Tautology    : 347
% 3.64/1.58  #SimpNegUnit  : 0
% 3.64/1.58  #BackRed      : 1
% 3.64/1.58  
% 3.64/1.58  #Partial instantiations: 0
% 3.64/1.58  #Strategies tried      : 1
% 3.64/1.58  
% 3.64/1.58  Timing (in seconds)
% 3.64/1.58  ----------------------
% 3.64/1.58  Preprocessing        : 0.28
% 3.64/1.58  Parsing              : 0.15
% 3.64/1.58  CNF conversion       : 0.02
% 3.64/1.58  Main loop            : 0.55
% 3.64/1.58  Inferencing          : 0.23
% 3.64/1.58  Reduction            : 0.23
% 3.64/1.58  Demodulation         : 0.19
% 3.64/1.58  BG Simplification    : 0.03
% 3.64/1.58  Subsumption          : 0.05
% 3.64/1.58  Abstraction          : 0.04
% 3.64/1.58  MUC search           : 0.00
% 3.64/1.58  Cooper               : 0.00
% 3.64/1.58  Total                : 0.86
% 3.64/1.58  Index Insertion      : 0.00
% 3.64/1.58  Index Deletion       : 0.00
% 3.64/1.58  Index Matching       : 0.00
% 3.64/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
