%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:46 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   47 (  76 expanded)
%              Number of leaves         :   26 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :   30 (  59 expanded)
%              Number of equality atoms :   29 (  58 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_18,B_19,C_20,D_21] : k3_enumset1(A_18,A_18,B_19,C_20,D_21) = k2_enumset1(A_18,B_19,C_20,D_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [E_26,A_22,B_23,D_25,C_24] : k4_enumset1(A_22,A_22,B_23,C_24,D_25,E_26) = k3_enumset1(A_22,B_23,C_24,D_25,E_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_15,B_16,C_17] : k2_enumset1(A_15,A_15,B_16,C_17) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] : k5_enumset1(A_27,A_27,B_28,C_29,D_30,E_31,F_32) = k4_enumset1(A_27,B_28,C_29,D_30,E_31,F_32) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [D_36,G_39,F_38,E_37,A_33,B_34,C_35] : k6_enumset1(A_33,A_33,B_34,C_35,D_36,E_37,F_38,G_39) = k5_enumset1(A_33,B_34,C_35,D_36,E_37,F_38,G_39) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_117,plain,(
    ! [A_76,C_75,B_74,G_73,F_72,H_77,D_71,E_78] : k2_xboole_0(k4_enumset1(A_76,B_74,C_75,D_71,E_78,F_72),k2_tarski(G_73,H_77)) = k6_enumset1(A_76,B_74,C_75,D_71,E_78,F_72,G_73,H_77) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    ! [E_26,G_73,H_77,A_22,B_23,D_25,C_24] : k6_enumset1(A_22,A_22,B_23,C_24,D_25,E_26,G_73,H_77) = k2_xboole_0(k3_enumset1(A_22,B_23,C_24,D_25,E_26),k2_tarski(G_73,H_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_117])).

tff(c_136,plain,(
    ! [H_82,G_83,C_80,D_84,E_81,B_85,A_79] : k2_xboole_0(k3_enumset1(A_79,B_85,C_80,D_84,E_81),k2_tarski(G_83,H_82)) = k5_enumset1(A_79,B_85,C_80,D_84,E_81,G_83,H_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_126])).

tff(c_145,plain,(
    ! [H_82,D_21,G_83,A_18,C_20,B_19] : k5_enumset1(A_18,A_18,B_19,C_20,D_21,G_83,H_82) = k2_xboole_0(k2_enumset1(A_18,B_19,C_20,D_21),k2_tarski(G_83,H_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_136])).

tff(c_155,plain,(
    ! [G_89,B_91,H_87,C_88,D_90,A_86] : k2_xboole_0(k2_enumset1(A_86,B_91,C_88,D_90),k2_tarski(G_89,H_87)) = k4_enumset1(A_86,B_91,C_88,D_90,G_89,H_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_145])).

tff(c_164,plain,(
    ! [B_16,A_15,G_89,H_87,C_17] : k4_enumset1(A_15,A_15,B_16,C_17,G_89,H_87) = k2_xboole_0(k1_enumset1(A_15,B_16,C_17),k2_tarski(G_89,H_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_155])).

tff(c_174,plain,(
    ! [H_93,C_92,A_95,G_96,B_94] : k2_xboole_0(k1_enumset1(A_95,B_94,C_92),k2_tarski(G_96,H_93)) = k3_enumset1(A_95,B_94,C_92,G_96,H_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_164])).

tff(c_183,plain,(
    ! [A_13,B_14,G_96,H_93] : k3_enumset1(A_13,A_13,B_14,G_96,H_93) = k2_xboole_0(k2_tarski(A_13,B_14),k2_tarski(G_96,H_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_174])).

tff(c_193,plain,(
    ! [A_97,B_98,G_99,H_100] : k2_xboole_0(k2_tarski(A_97,B_98),k2_tarski(G_99,H_100)) = k2_enumset1(A_97,B_98,G_99,H_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_183])).

tff(c_309,plain,(
    ! [A_117,B_118,A_119,B_120] : k2_xboole_0(k2_tarski(A_117,B_118),k2_tarski(A_119,B_120)) = k2_enumset1(A_117,B_118,B_120,A_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_193])).

tff(c_192,plain,(
    ! [A_13,B_14,G_96,H_93] : k2_xboole_0(k2_tarski(A_13,B_14),k2_tarski(G_96,H_93)) = k2_enumset1(A_13,B_14,G_96,H_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_183])).

tff(c_318,plain,(
    ! [A_117,B_118,B_120,A_119] : k2_enumset1(A_117,B_118,B_120,A_119) = k2_enumset1(A_117,B_118,A_119,B_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_192])).

tff(c_20,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:22:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.36  
% 2.35/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.36  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.35/1.36  
% 2.35/1.36  %Foreground sorts:
% 2.35/1.36  
% 2.35/1.36  
% 2.35/1.36  %Background operators:
% 2.35/1.36  
% 2.35/1.36  
% 2.35/1.36  %Foreground operators:
% 2.35/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.35/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.35/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.35/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.35/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.35/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.35/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.35/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.35/1.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.36  
% 2.35/1.37  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.35/1.37  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.35/1.37  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.35/1.37  tff(f_39, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.35/1.37  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.35/1.37  tff(f_41, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.35/1.37  tff(f_43, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.35/1.37  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 2.35/1.37  tff(f_46, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_enumset1)).
% 2.35/1.37  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.35/1.37  tff(c_12, plain, (![A_18, B_19, C_20, D_21]: (k3_enumset1(A_18, A_18, B_19, C_20, D_21)=k2_enumset1(A_18, B_19, C_20, D_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.35/1.37  tff(c_8, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.35/1.37  tff(c_14, plain, (![E_26, A_22, B_23, D_25, C_24]: (k4_enumset1(A_22, A_22, B_23, C_24, D_25, E_26)=k3_enumset1(A_22, B_23, C_24, D_25, E_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.35/1.37  tff(c_10, plain, (![A_15, B_16, C_17]: (k2_enumset1(A_15, A_15, B_16, C_17)=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.35/1.37  tff(c_16, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (k5_enumset1(A_27, A_27, B_28, C_29, D_30, E_31, F_32)=k4_enumset1(A_27, B_28, C_29, D_30, E_31, F_32))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.35/1.37  tff(c_18, plain, (![D_36, G_39, F_38, E_37, A_33, B_34, C_35]: (k6_enumset1(A_33, A_33, B_34, C_35, D_36, E_37, F_38, G_39)=k5_enumset1(A_33, B_34, C_35, D_36, E_37, F_38, G_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.35/1.37  tff(c_117, plain, (![A_76, C_75, B_74, G_73, F_72, H_77, D_71, E_78]: (k2_xboole_0(k4_enumset1(A_76, B_74, C_75, D_71, E_78, F_72), k2_tarski(G_73, H_77))=k6_enumset1(A_76, B_74, C_75, D_71, E_78, F_72, G_73, H_77))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.37  tff(c_126, plain, (![E_26, G_73, H_77, A_22, B_23, D_25, C_24]: (k6_enumset1(A_22, A_22, B_23, C_24, D_25, E_26, G_73, H_77)=k2_xboole_0(k3_enumset1(A_22, B_23, C_24, D_25, E_26), k2_tarski(G_73, H_77)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_117])).
% 2.35/1.37  tff(c_136, plain, (![H_82, G_83, C_80, D_84, E_81, B_85, A_79]: (k2_xboole_0(k3_enumset1(A_79, B_85, C_80, D_84, E_81), k2_tarski(G_83, H_82))=k5_enumset1(A_79, B_85, C_80, D_84, E_81, G_83, H_82))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_126])).
% 2.35/1.37  tff(c_145, plain, (![H_82, D_21, G_83, A_18, C_20, B_19]: (k5_enumset1(A_18, A_18, B_19, C_20, D_21, G_83, H_82)=k2_xboole_0(k2_enumset1(A_18, B_19, C_20, D_21), k2_tarski(G_83, H_82)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_136])).
% 2.35/1.37  tff(c_155, plain, (![G_89, B_91, H_87, C_88, D_90, A_86]: (k2_xboole_0(k2_enumset1(A_86, B_91, C_88, D_90), k2_tarski(G_89, H_87))=k4_enumset1(A_86, B_91, C_88, D_90, G_89, H_87))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_145])).
% 2.35/1.37  tff(c_164, plain, (![B_16, A_15, G_89, H_87, C_17]: (k4_enumset1(A_15, A_15, B_16, C_17, G_89, H_87)=k2_xboole_0(k1_enumset1(A_15, B_16, C_17), k2_tarski(G_89, H_87)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_155])).
% 2.35/1.37  tff(c_174, plain, (![H_93, C_92, A_95, G_96, B_94]: (k2_xboole_0(k1_enumset1(A_95, B_94, C_92), k2_tarski(G_96, H_93))=k3_enumset1(A_95, B_94, C_92, G_96, H_93))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_164])).
% 2.35/1.37  tff(c_183, plain, (![A_13, B_14, G_96, H_93]: (k3_enumset1(A_13, A_13, B_14, G_96, H_93)=k2_xboole_0(k2_tarski(A_13, B_14), k2_tarski(G_96, H_93)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_174])).
% 2.35/1.37  tff(c_193, plain, (![A_97, B_98, G_99, H_100]: (k2_xboole_0(k2_tarski(A_97, B_98), k2_tarski(G_99, H_100))=k2_enumset1(A_97, B_98, G_99, H_100))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_183])).
% 2.35/1.37  tff(c_309, plain, (![A_117, B_118, A_119, B_120]: (k2_xboole_0(k2_tarski(A_117, B_118), k2_tarski(A_119, B_120))=k2_enumset1(A_117, B_118, B_120, A_119))), inference(superposition, [status(thm), theory('equality')], [c_4, c_193])).
% 2.35/1.37  tff(c_192, plain, (![A_13, B_14, G_96, H_93]: (k2_xboole_0(k2_tarski(A_13, B_14), k2_tarski(G_96, H_93))=k2_enumset1(A_13, B_14, G_96, H_93))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_183])).
% 2.35/1.37  tff(c_318, plain, (![A_117, B_118, B_120, A_119]: (k2_enumset1(A_117, B_118, B_120, A_119)=k2_enumset1(A_117, B_118, A_119, B_120))), inference(superposition, [status(thm), theory('equality')], [c_309, c_192])).
% 2.35/1.37  tff(c_20, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.35/1.37  tff(c_560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_318, c_20])).
% 2.35/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.37  
% 2.35/1.37  Inference rules
% 2.35/1.37  ----------------------
% 2.35/1.37  #Ref     : 0
% 2.35/1.37  #Sup     : 137
% 2.35/1.37  #Fact    : 0
% 2.35/1.37  #Define  : 0
% 2.35/1.37  #Split   : 0
% 2.35/1.37  #Chain   : 0
% 2.35/1.37  #Close   : 0
% 2.35/1.37  
% 2.35/1.37  Ordering : KBO
% 2.35/1.37  
% 2.35/1.37  Simplification rules
% 2.35/1.37  ----------------------
% 2.35/1.37  #Subsume      : 5
% 2.35/1.37  #Demod        : 32
% 2.35/1.37  #Tautology    : 88
% 2.35/1.37  #SimpNegUnit  : 0
% 2.35/1.37  #BackRed      : 1
% 2.35/1.37  
% 2.35/1.37  #Partial instantiations: 0
% 2.35/1.37  #Strategies tried      : 1
% 2.35/1.37  
% 2.35/1.37  Timing (in seconds)
% 2.35/1.37  ----------------------
% 2.35/1.37  Preprocessing        : 0.29
% 2.35/1.37  Parsing              : 0.16
% 2.35/1.37  CNF conversion       : 0.02
% 2.35/1.37  Main loop            : 0.26
% 2.35/1.37  Inferencing          : 0.11
% 2.35/1.37  Reduction            : 0.10
% 2.35/1.37  Demodulation         : 0.08
% 2.35/1.37  BG Simplification    : 0.02
% 2.35/1.37  Subsumption          : 0.03
% 2.35/1.38  Abstraction          : 0.02
% 2.35/1.38  MUC search           : 0.00
% 2.35/1.38  Cooper               : 0.00
% 2.35/1.38  Total                : 0.58
% 2.35/1.38  Index Insertion      : 0.00
% 2.35/1.38  Index Deletion       : 0.00
% 2.35/1.38  Index Matching       : 0.00
% 2.35/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
