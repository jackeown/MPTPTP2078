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
% DateTime   : Thu Dec  3 09:49:45 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   57 (  67 expanded)
%              Number of leaves         :   29 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :   40 (  50 expanded)
%              Number of equality atoms :   39 (  49 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_175,plain,(
    ! [C_61,B_62,A_63] : k1_enumset1(C_61,B_62,A_63) = k1_enumset1(A_63,B_62,C_61) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_20,B_21] : k1_enumset1(A_20,A_20,B_21) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_191,plain,(
    ! [C_61,B_62] : k1_enumset1(C_61,B_62,B_62) = k2_tarski(B_62,C_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_14])).

tff(c_12,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_22,B_23,C_24] : k2_enumset1(A_22,A_22,B_23,C_24) = k1_enumset1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_25,B_26,C_27,D_28] : k3_enumset1(A_25,A_25,B_26,C_27,D_28) = k2_enumset1(A_25,B_26,C_27,D_28) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [E_33,A_29,D_32,C_31,B_30] : k4_enumset1(A_29,A_29,B_30,C_31,D_32,E_33) = k3_enumset1(A_29,B_30,C_31,D_32,E_33) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [D_37,A_34,F_39,B_35,C_36,E_38] : k5_enumset1(A_34,A_34,B_35,C_36,D_37,E_38,F_39) = k4_enumset1(A_34,B_35,C_36,D_37,E_38,F_39) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [E_44,C_42,G_46,F_45,A_40,D_43,B_41] : k6_enumset1(A_40,A_40,B_41,C_42,D_43,E_44,F_45,G_46) = k5_enumset1(A_40,B_41,C_42,D_43,E_44,F_45,G_46) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_890,plain,(
    ! [E_121,G_117,B_119,D_120,F_115,H_122,A_118,C_116] : k2_xboole_0(k4_enumset1(A_118,B_119,C_116,D_120,E_121,F_115),k2_tarski(G_117,H_122)) = k6_enumset1(A_118,B_119,C_116,D_120,E_121,F_115,G_117,H_122) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_908,plain,(
    ! [E_33,G_117,A_29,H_122,D_32,C_31,B_30] : k6_enumset1(A_29,A_29,B_30,C_31,D_32,E_33,G_117,H_122) = k2_xboole_0(k3_enumset1(A_29,B_30,C_31,D_32,E_33),k2_tarski(G_117,H_122)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_890])).

tff(c_1075,plain,(
    ! [B_129,E_133,G_132,A_131,H_130,C_134,D_128] : k2_xboole_0(k3_enumset1(A_131,B_129,C_134,D_128,E_133),k2_tarski(G_132,H_130)) = k5_enumset1(A_131,B_129,C_134,D_128,E_133,G_132,H_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_908])).

tff(c_1099,plain,(
    ! [A_25,G_132,H_130,C_27,D_28,B_26] : k5_enumset1(A_25,A_25,B_26,C_27,D_28,G_132,H_130) = k2_xboole_0(k2_enumset1(A_25,B_26,C_27,D_28),k2_tarski(G_132,H_130)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1075])).

tff(c_1118,plain,(
    ! [G_140,H_137,A_136,D_135,C_138,B_139] : k2_xboole_0(k2_enumset1(A_136,B_139,C_138,D_135),k2_tarski(G_140,H_137)) = k4_enumset1(A_136,B_139,C_138,D_135,G_140,H_137) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1099])).

tff(c_1142,plain,(
    ! [G_140,H_137,A_22,B_23,C_24] : k4_enumset1(A_22,A_22,B_23,C_24,G_140,H_137) = k2_xboole_0(k1_enumset1(A_22,B_23,C_24),k2_tarski(G_140,H_137)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1118])).

tff(c_1161,plain,(
    ! [B_144,A_141,G_143,H_145,C_142] : k2_xboole_0(k1_enumset1(A_141,B_144,C_142),k2_tarski(G_143,H_145)) = k3_enumset1(A_141,B_144,C_142,G_143,H_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1142])).

tff(c_1200,plain,(
    ! [A_20,B_21,G_143,H_145] : k3_enumset1(A_20,A_20,B_21,G_143,H_145) = k2_xboole_0(k2_tarski(A_20,B_21),k2_tarski(G_143,H_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1161])).

tff(c_1213,plain,(
    ! [A_146,B_147,G_148,H_149] : k2_xboole_0(k2_tarski(A_146,B_147),k2_tarski(G_148,H_149)) = k2_enumset1(A_146,B_147,G_148,H_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1200])).

tff(c_1263,plain,(
    ! [A_19,G_148,H_149] : k2_xboole_0(k1_tarski(A_19),k2_tarski(G_148,H_149)) = k2_enumset1(A_19,A_19,G_148,H_149) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1213])).

tff(c_1436,plain,(
    ! [A_162,G_163,H_164] : k2_xboole_0(k1_tarski(A_162),k2_tarski(G_163,H_164)) = k1_enumset1(A_162,G_163,H_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1263])).

tff(c_1472,plain,(
    ! [A_162,A_19] : k2_xboole_0(k1_tarski(A_162),k1_tarski(A_19)) = k1_enumset1(A_162,A_19,A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1436])).

tff(c_1475,plain,(
    ! [A_162,A_19] : k2_xboole_0(k1_tarski(A_162),k1_tarski(A_19)) = k2_tarski(A_19,A_162) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_1472])).

tff(c_26,plain,(
    ! [A_47,B_48] : k3_tarski(k2_tarski(A_47,B_48)) = k2_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_29,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_1476,plain,(
    k2_tarski('#skF_2','#skF_1') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1475,c_29])).

tff(c_1479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1476])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n019.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 17:47:07 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.73/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.62  
% 3.73/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.62  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 3.73/1.62  
% 3.73/1.62  %Foreground sorts:
% 3.73/1.62  
% 3.73/1.62  
% 3.73/1.62  %Background operators:
% 3.73/1.62  
% 3.73/1.62  
% 3.73/1.62  %Foreground operators:
% 3.73/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.73/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.73/1.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.73/1.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.73/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.73/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.73/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.73/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.73/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.73/1.62  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.73/1.62  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.73/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.73/1.62  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.73/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.73/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.73/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.73/1.62  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.73/1.62  
% 3.73/1.64  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.73/1.64  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_enumset1)).
% 3.73/1.64  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.73/1.64  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.73/1.64  tff(f_41, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.73/1.64  tff(f_43, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.73/1.64  tff(f_45, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.73/1.64  tff(f_47, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.73/1.64  tff(f_49, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 3.73/1.64  tff(f_35, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 3.73/1.64  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.73/1.64  tff(f_54, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 3.73/1.64  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.73/1.64  tff(c_175, plain, (![C_61, B_62, A_63]: (k1_enumset1(C_61, B_62, A_63)=k1_enumset1(A_63, B_62, C_61))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.73/1.64  tff(c_14, plain, (![A_20, B_21]: (k1_enumset1(A_20, A_20, B_21)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.73/1.64  tff(c_191, plain, (![C_61, B_62]: (k1_enumset1(C_61, B_62, B_62)=k2_tarski(B_62, C_61))), inference(superposition, [status(thm), theory('equality')], [c_175, c_14])).
% 3.73/1.64  tff(c_12, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.73/1.64  tff(c_16, plain, (![A_22, B_23, C_24]: (k2_enumset1(A_22, A_22, B_23, C_24)=k1_enumset1(A_22, B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.73/1.64  tff(c_18, plain, (![A_25, B_26, C_27, D_28]: (k3_enumset1(A_25, A_25, B_26, C_27, D_28)=k2_enumset1(A_25, B_26, C_27, D_28))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.73/1.64  tff(c_20, plain, (![E_33, A_29, D_32, C_31, B_30]: (k4_enumset1(A_29, A_29, B_30, C_31, D_32, E_33)=k3_enumset1(A_29, B_30, C_31, D_32, E_33))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.73/1.64  tff(c_22, plain, (![D_37, A_34, F_39, B_35, C_36, E_38]: (k5_enumset1(A_34, A_34, B_35, C_36, D_37, E_38, F_39)=k4_enumset1(A_34, B_35, C_36, D_37, E_38, F_39))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.73/1.64  tff(c_24, plain, (![E_44, C_42, G_46, F_45, A_40, D_43, B_41]: (k6_enumset1(A_40, A_40, B_41, C_42, D_43, E_44, F_45, G_46)=k5_enumset1(A_40, B_41, C_42, D_43, E_44, F_45, G_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.73/1.64  tff(c_890, plain, (![E_121, G_117, B_119, D_120, F_115, H_122, A_118, C_116]: (k2_xboole_0(k4_enumset1(A_118, B_119, C_116, D_120, E_121, F_115), k2_tarski(G_117, H_122))=k6_enumset1(A_118, B_119, C_116, D_120, E_121, F_115, G_117, H_122))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.73/1.64  tff(c_908, plain, (![E_33, G_117, A_29, H_122, D_32, C_31, B_30]: (k6_enumset1(A_29, A_29, B_30, C_31, D_32, E_33, G_117, H_122)=k2_xboole_0(k3_enumset1(A_29, B_30, C_31, D_32, E_33), k2_tarski(G_117, H_122)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_890])).
% 3.73/1.64  tff(c_1075, plain, (![B_129, E_133, G_132, A_131, H_130, C_134, D_128]: (k2_xboole_0(k3_enumset1(A_131, B_129, C_134, D_128, E_133), k2_tarski(G_132, H_130))=k5_enumset1(A_131, B_129, C_134, D_128, E_133, G_132, H_130))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_908])).
% 3.73/1.64  tff(c_1099, plain, (![A_25, G_132, H_130, C_27, D_28, B_26]: (k5_enumset1(A_25, A_25, B_26, C_27, D_28, G_132, H_130)=k2_xboole_0(k2_enumset1(A_25, B_26, C_27, D_28), k2_tarski(G_132, H_130)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1075])).
% 3.73/1.64  tff(c_1118, plain, (![G_140, H_137, A_136, D_135, C_138, B_139]: (k2_xboole_0(k2_enumset1(A_136, B_139, C_138, D_135), k2_tarski(G_140, H_137))=k4_enumset1(A_136, B_139, C_138, D_135, G_140, H_137))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1099])).
% 3.73/1.64  tff(c_1142, plain, (![G_140, H_137, A_22, B_23, C_24]: (k4_enumset1(A_22, A_22, B_23, C_24, G_140, H_137)=k2_xboole_0(k1_enumset1(A_22, B_23, C_24), k2_tarski(G_140, H_137)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1118])).
% 3.73/1.64  tff(c_1161, plain, (![B_144, A_141, G_143, H_145, C_142]: (k2_xboole_0(k1_enumset1(A_141, B_144, C_142), k2_tarski(G_143, H_145))=k3_enumset1(A_141, B_144, C_142, G_143, H_145))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1142])).
% 3.73/1.64  tff(c_1200, plain, (![A_20, B_21, G_143, H_145]: (k3_enumset1(A_20, A_20, B_21, G_143, H_145)=k2_xboole_0(k2_tarski(A_20, B_21), k2_tarski(G_143, H_145)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1161])).
% 3.73/1.64  tff(c_1213, plain, (![A_146, B_147, G_148, H_149]: (k2_xboole_0(k2_tarski(A_146, B_147), k2_tarski(G_148, H_149))=k2_enumset1(A_146, B_147, G_148, H_149))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1200])).
% 3.73/1.64  tff(c_1263, plain, (![A_19, G_148, H_149]: (k2_xboole_0(k1_tarski(A_19), k2_tarski(G_148, H_149))=k2_enumset1(A_19, A_19, G_148, H_149))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1213])).
% 3.73/1.64  tff(c_1436, plain, (![A_162, G_163, H_164]: (k2_xboole_0(k1_tarski(A_162), k2_tarski(G_163, H_164))=k1_enumset1(A_162, G_163, H_164))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1263])).
% 3.73/1.64  tff(c_1472, plain, (![A_162, A_19]: (k2_xboole_0(k1_tarski(A_162), k1_tarski(A_19))=k1_enumset1(A_162, A_19, A_19))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1436])).
% 3.73/1.64  tff(c_1475, plain, (![A_162, A_19]: (k2_xboole_0(k1_tarski(A_162), k1_tarski(A_19))=k2_tarski(A_19, A_162))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_1472])).
% 3.73/1.64  tff(c_26, plain, (![A_47, B_48]: (k3_tarski(k2_tarski(A_47, B_48))=k2_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.73/1.64  tff(c_28, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.73/1.64  tff(c_29, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 3.73/1.64  tff(c_1476, plain, (k2_tarski('#skF_2', '#skF_1')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1475, c_29])).
% 3.73/1.64  tff(c_1479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1476])).
% 3.73/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.64  
% 3.73/1.64  Inference rules
% 3.73/1.64  ----------------------
% 3.73/1.64  #Ref     : 0
% 3.73/1.64  #Sup     : 374
% 3.73/1.64  #Fact    : 0
% 3.73/1.64  #Define  : 0
% 3.73/1.64  #Split   : 0
% 3.73/1.64  #Chain   : 0
% 3.73/1.64  #Close   : 0
% 3.73/1.64  
% 3.73/1.64  Ordering : KBO
% 3.73/1.64  
% 3.73/1.64  Simplification rules
% 3.73/1.64  ----------------------
% 3.73/1.64  #Subsume      : 2
% 3.73/1.64  #Demod        : 274
% 3.73/1.64  #Tautology    : 147
% 3.73/1.64  #SimpNegUnit  : 0
% 3.73/1.64  #BackRed      : 1
% 3.73/1.64  
% 3.73/1.64  #Partial instantiations: 0
% 3.73/1.64  #Strategies tried      : 1
% 3.73/1.64  
% 3.73/1.64  Timing (in seconds)
% 3.73/1.64  ----------------------
% 3.73/1.64  Preprocessing        : 0.31
% 3.73/1.64  Parsing              : 0.17
% 3.73/1.64  CNF conversion       : 0.02
% 3.73/1.64  Main loop            : 0.58
% 3.73/1.64  Inferencing          : 0.21
% 3.73/1.64  Reduction            : 0.25
% 3.73/1.64  Demodulation         : 0.21
% 3.73/1.64  BG Simplification    : 0.04
% 3.73/1.64  Subsumption          : 0.06
% 3.73/1.64  Abstraction          : 0.05
% 3.73/1.64  MUC search           : 0.00
% 3.73/1.64  Cooper               : 0.00
% 3.73/1.64  Total                : 0.93
% 3.73/1.64  Index Insertion      : 0.00
% 3.73/1.64  Index Deletion       : 0.00
% 3.73/1.64  Index Matching       : 0.00
% 3.73/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
