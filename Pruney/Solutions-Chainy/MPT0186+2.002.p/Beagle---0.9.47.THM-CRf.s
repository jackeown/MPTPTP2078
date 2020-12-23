%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:47 EST 2020

% Result     : Theorem 4.85s
% Output     : CNFRefutation 4.85s
% Verified   : 
% Statistics : Number of formulae       :   55 (  93 expanded)
%              Number of leaves         :   27 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :   39 (  77 expanded)
%              Number of equality atoms :   38 (  76 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_18,B_19,C_20] : k2_enumset1(A_18,A_18,B_19,C_20) = k1_enumset1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_16,B_17] : k1_enumset1(A_16,A_16,B_17) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    ! [A_55,B_56,C_57,D_58] : k2_xboole_0(k1_enumset1(A_55,B_56,C_57),k1_tarski(D_58)) = k2_enumset1(A_55,B_56,C_57,D_58) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_101,plain,(
    ! [A_16,B_17,D_58] : k2_xboole_0(k2_tarski(A_16,B_17),k1_tarski(D_58)) = k2_enumset1(A_16,A_16,B_17,D_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_92])).

tff(c_105,plain,(
    ! [A_59,B_60,D_61] : k2_xboole_0(k2_tarski(A_59,B_60),k1_tarski(D_61)) = k1_enumset1(A_59,B_60,D_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_101])).

tff(c_142,plain,(
    ! [A_69,B_70,D_71] : k2_xboole_0(k2_tarski(A_69,B_70),k1_tarski(D_71)) = k1_enumset1(B_70,A_69,D_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_105])).

tff(c_104,plain,(
    ! [A_16,B_17,D_58] : k2_xboole_0(k2_tarski(A_16,B_17),k1_tarski(D_58)) = k1_enumset1(A_16,B_17,D_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_101])).

tff(c_148,plain,(
    ! [B_70,A_69,D_71] : k1_enumset1(B_70,A_69,D_71) = k1_enumset1(A_69,B_70,D_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_104])).

tff(c_14,plain,(
    ! [A_21,B_22,C_23,D_24] : k3_enumset1(A_21,A_21,B_22,C_23,D_24) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_25,E_29,C_27,D_28,B_26] : k4_enumset1(A_25,A_25,B_26,C_27,D_28,E_29) = k3_enumset1(A_25,B_26,C_27,D_28,E_29) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,F_35] : k5_enumset1(A_30,A_30,B_31,C_32,D_33,E_34,F_35) = k4_enumset1(A_30,B_31,C_32,D_33,E_34,F_35) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [F_41,G_42,D_39,A_36,E_40,C_38,B_37] : k6_enumset1(A_36,A_36,B_37,C_38,D_39,E_40,F_41,G_42) = k5_enumset1(A_36,B_37,C_38,D_39,E_40,F_41,G_42) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_288,plain,(
    ! [D_96,H_103,A_99,F_101,B_97,G_100,C_98,E_102] : k2_xboole_0(k3_enumset1(A_99,B_97,C_98,D_96,E_102),k1_enumset1(F_101,G_100,H_103)) = k6_enumset1(A_99,B_97,C_98,D_96,E_102,F_101,G_100,H_103) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_303,plain,(
    ! [A_21,B_22,D_24,C_23,H_103,F_101,G_100] : k6_enumset1(A_21,A_21,B_22,C_23,D_24,F_101,G_100,H_103) = k2_xboole_0(k2_enumset1(A_21,B_22,C_23,D_24),k1_enumset1(F_101,G_100,H_103)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_288])).

tff(c_310,plain,(
    ! [G_107,C_108,B_110,A_105,F_109,H_104,D_106] : k2_xboole_0(k2_enumset1(A_105,B_110,C_108,D_106),k1_enumset1(F_109,G_107,H_104)) = k5_enumset1(A_105,B_110,C_108,D_106,F_109,G_107,H_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_303])).

tff(c_331,plain,(
    ! [G_107,F_109,H_104,A_18,C_20,B_19] : k5_enumset1(A_18,A_18,B_19,C_20,F_109,G_107,H_104) = k2_xboole_0(k1_enumset1(A_18,B_19,C_20),k1_enumset1(F_109,G_107,H_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_310])).

tff(c_338,plain,(
    ! [H_114,A_111,G_113,F_115,B_116,C_112] : k2_xboole_0(k1_enumset1(A_111,B_116,C_112),k1_enumset1(F_115,G_113,H_114)) = k4_enumset1(A_111,B_116,C_112,F_115,G_113,H_114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_331])).

tff(c_359,plain,(
    ! [B_17,A_16,H_114,G_113,F_115] : k4_enumset1(A_16,A_16,B_17,F_115,G_113,H_114) = k2_xboole_0(k2_tarski(A_16,B_17),k1_enumset1(F_115,G_113,H_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_338])).

tff(c_366,plain,(
    ! [B_118,G_117,H_119,A_120,F_121] : k2_xboole_0(k2_tarski(A_120,B_118),k1_enumset1(F_121,G_117,H_119)) = k3_enumset1(A_120,B_118,F_121,G_117,H_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_359])).

tff(c_390,plain,(
    ! [A_15,F_121,G_117,H_119] : k3_enumset1(A_15,A_15,F_121,G_117,H_119) = k2_xboole_0(k1_tarski(A_15),k1_enumset1(F_121,G_117,H_119)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_366])).

tff(c_394,plain,(
    ! [A_122,F_123,G_124,H_125] : k2_xboole_0(k1_tarski(A_122),k1_enumset1(F_123,G_124,H_125)) = k2_enumset1(A_122,F_123,G_124,H_125) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_390])).

tff(c_3499,plain,(
    ! [A_232,A_233,B_234,D_235] : k2_xboole_0(k1_tarski(A_232),k1_enumset1(A_233,B_234,D_235)) = k2_enumset1(A_232,B_234,A_233,D_235) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_394])).

tff(c_393,plain,(
    ! [A_15,F_121,G_117,H_119] : k2_xboole_0(k1_tarski(A_15),k1_enumset1(F_121,G_117,H_119)) = k2_enumset1(A_15,F_121,G_117,H_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_390])).

tff(c_3505,plain,(
    ! [A_232,B_234,A_233,D_235] : k2_enumset1(A_232,B_234,A_233,D_235) = k2_enumset1(A_232,A_233,B_234,D_235) ),
    inference(superposition,[status(thm),theory(equality)],[c_3499,c_393])).

tff(c_22,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3505,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:03:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.85/1.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.85/1.92  
% 4.85/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.85/1.92  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.85/1.92  
% 4.85/1.92  %Foreground sorts:
% 4.85/1.92  
% 4.85/1.92  
% 4.85/1.92  %Background operators:
% 4.85/1.92  
% 4.85/1.92  
% 4.85/1.92  %Foreground operators:
% 4.85/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.85/1.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.85/1.92  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.85/1.92  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.85/1.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.85/1.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.85/1.92  tff('#skF_2', type, '#skF_2': $i).
% 4.85/1.92  tff('#skF_3', type, '#skF_3': $i).
% 4.85/1.92  tff('#skF_1', type, '#skF_1': $i).
% 4.85/1.92  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.85/1.92  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.85/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.85/1.92  tff('#skF_4', type, '#skF_4': $i).
% 4.85/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.85/1.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.85/1.92  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.85/1.92  
% 4.85/1.93  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.85/1.93  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.85/1.93  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.85/1.93  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 4.85/1.93  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 4.85/1.93  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.85/1.93  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 4.85/1.93  tff(f_43, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 4.85/1.93  tff(f_45, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 4.85/1.93  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 4.85/1.93  tff(f_48, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 4.85/1.93  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.85/1.93  tff(c_12, plain, (![A_18, B_19, C_20]: (k2_enumset1(A_18, A_18, B_19, C_20)=k1_enumset1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.85/1.93  tff(c_10, plain, (![A_16, B_17]: (k1_enumset1(A_16, A_16, B_17)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.85/1.93  tff(c_92, plain, (![A_55, B_56, C_57, D_58]: (k2_xboole_0(k1_enumset1(A_55, B_56, C_57), k1_tarski(D_58))=k2_enumset1(A_55, B_56, C_57, D_58))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.85/1.93  tff(c_101, plain, (![A_16, B_17, D_58]: (k2_xboole_0(k2_tarski(A_16, B_17), k1_tarski(D_58))=k2_enumset1(A_16, A_16, B_17, D_58))), inference(superposition, [status(thm), theory('equality')], [c_10, c_92])).
% 4.85/1.93  tff(c_105, plain, (![A_59, B_60, D_61]: (k2_xboole_0(k2_tarski(A_59, B_60), k1_tarski(D_61))=k1_enumset1(A_59, B_60, D_61))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_101])).
% 4.85/1.93  tff(c_142, plain, (![A_69, B_70, D_71]: (k2_xboole_0(k2_tarski(A_69, B_70), k1_tarski(D_71))=k1_enumset1(B_70, A_69, D_71))), inference(superposition, [status(thm), theory('equality')], [c_2, c_105])).
% 4.85/1.93  tff(c_104, plain, (![A_16, B_17, D_58]: (k2_xboole_0(k2_tarski(A_16, B_17), k1_tarski(D_58))=k1_enumset1(A_16, B_17, D_58))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_101])).
% 4.85/1.93  tff(c_148, plain, (![B_70, A_69, D_71]: (k1_enumset1(B_70, A_69, D_71)=k1_enumset1(A_69, B_70, D_71))), inference(superposition, [status(thm), theory('equality')], [c_142, c_104])).
% 4.85/1.93  tff(c_14, plain, (![A_21, B_22, C_23, D_24]: (k3_enumset1(A_21, A_21, B_22, C_23, D_24)=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.85/1.93  tff(c_8, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.85/1.93  tff(c_16, plain, (![A_25, E_29, C_27, D_28, B_26]: (k4_enumset1(A_25, A_25, B_26, C_27, D_28, E_29)=k3_enumset1(A_25, B_26, C_27, D_28, E_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.85/1.93  tff(c_18, plain, (![D_33, A_30, C_32, B_31, E_34, F_35]: (k5_enumset1(A_30, A_30, B_31, C_32, D_33, E_34, F_35)=k4_enumset1(A_30, B_31, C_32, D_33, E_34, F_35))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.85/1.93  tff(c_20, plain, (![F_41, G_42, D_39, A_36, E_40, C_38, B_37]: (k6_enumset1(A_36, A_36, B_37, C_38, D_39, E_40, F_41, G_42)=k5_enumset1(A_36, B_37, C_38, D_39, E_40, F_41, G_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.85/1.93  tff(c_288, plain, (![D_96, H_103, A_99, F_101, B_97, G_100, C_98, E_102]: (k2_xboole_0(k3_enumset1(A_99, B_97, C_98, D_96, E_102), k1_enumset1(F_101, G_100, H_103))=k6_enumset1(A_99, B_97, C_98, D_96, E_102, F_101, G_100, H_103))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.85/1.93  tff(c_303, plain, (![A_21, B_22, D_24, C_23, H_103, F_101, G_100]: (k6_enumset1(A_21, A_21, B_22, C_23, D_24, F_101, G_100, H_103)=k2_xboole_0(k2_enumset1(A_21, B_22, C_23, D_24), k1_enumset1(F_101, G_100, H_103)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_288])).
% 4.85/1.93  tff(c_310, plain, (![G_107, C_108, B_110, A_105, F_109, H_104, D_106]: (k2_xboole_0(k2_enumset1(A_105, B_110, C_108, D_106), k1_enumset1(F_109, G_107, H_104))=k5_enumset1(A_105, B_110, C_108, D_106, F_109, G_107, H_104))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_303])).
% 4.85/1.93  tff(c_331, plain, (![G_107, F_109, H_104, A_18, C_20, B_19]: (k5_enumset1(A_18, A_18, B_19, C_20, F_109, G_107, H_104)=k2_xboole_0(k1_enumset1(A_18, B_19, C_20), k1_enumset1(F_109, G_107, H_104)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_310])).
% 4.85/1.93  tff(c_338, plain, (![H_114, A_111, G_113, F_115, B_116, C_112]: (k2_xboole_0(k1_enumset1(A_111, B_116, C_112), k1_enumset1(F_115, G_113, H_114))=k4_enumset1(A_111, B_116, C_112, F_115, G_113, H_114))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_331])).
% 4.85/1.93  tff(c_359, plain, (![B_17, A_16, H_114, G_113, F_115]: (k4_enumset1(A_16, A_16, B_17, F_115, G_113, H_114)=k2_xboole_0(k2_tarski(A_16, B_17), k1_enumset1(F_115, G_113, H_114)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_338])).
% 4.85/1.93  tff(c_366, plain, (![B_118, G_117, H_119, A_120, F_121]: (k2_xboole_0(k2_tarski(A_120, B_118), k1_enumset1(F_121, G_117, H_119))=k3_enumset1(A_120, B_118, F_121, G_117, H_119))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_359])).
% 4.85/1.93  tff(c_390, plain, (![A_15, F_121, G_117, H_119]: (k3_enumset1(A_15, A_15, F_121, G_117, H_119)=k2_xboole_0(k1_tarski(A_15), k1_enumset1(F_121, G_117, H_119)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_366])).
% 4.85/1.93  tff(c_394, plain, (![A_122, F_123, G_124, H_125]: (k2_xboole_0(k1_tarski(A_122), k1_enumset1(F_123, G_124, H_125))=k2_enumset1(A_122, F_123, G_124, H_125))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_390])).
% 4.85/1.93  tff(c_3499, plain, (![A_232, A_233, B_234, D_235]: (k2_xboole_0(k1_tarski(A_232), k1_enumset1(A_233, B_234, D_235))=k2_enumset1(A_232, B_234, A_233, D_235))), inference(superposition, [status(thm), theory('equality')], [c_148, c_394])).
% 4.85/1.93  tff(c_393, plain, (![A_15, F_121, G_117, H_119]: (k2_xboole_0(k1_tarski(A_15), k1_enumset1(F_121, G_117, H_119))=k2_enumset1(A_15, F_121, G_117, H_119))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_390])).
% 4.85/1.93  tff(c_3505, plain, (![A_232, B_234, A_233, D_235]: (k2_enumset1(A_232, B_234, A_233, D_235)=k2_enumset1(A_232, A_233, B_234, D_235))), inference(superposition, [status(thm), theory('equality')], [c_3499, c_393])).
% 4.85/1.93  tff(c_22, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.85/1.93  tff(c_3531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3505, c_22])).
% 4.85/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.85/1.93  
% 4.85/1.93  Inference rules
% 4.85/1.93  ----------------------
% 4.85/1.93  #Ref     : 0
% 4.85/1.93  #Sup     : 870
% 4.85/1.93  #Fact    : 0
% 4.85/1.93  #Define  : 0
% 4.85/1.93  #Split   : 0
% 4.85/1.93  #Chain   : 0
% 4.85/1.93  #Close   : 0
% 4.85/1.93  
% 4.85/1.93  Ordering : KBO
% 4.85/1.93  
% 4.85/1.93  Simplification rules
% 4.85/1.93  ----------------------
% 4.85/1.93  #Subsume      : 157
% 4.85/1.93  #Demod        : 633
% 4.85/1.93  #Tautology    : 508
% 4.85/1.93  #SimpNegUnit  : 0
% 4.85/1.93  #BackRed      : 1
% 4.85/1.93  
% 4.85/1.93  #Partial instantiations: 0
% 4.85/1.94  #Strategies tried      : 1
% 4.85/1.94  
% 4.85/1.94  Timing (in seconds)
% 4.85/1.94  ----------------------
% 4.85/1.94  Preprocessing        : 0.31
% 4.85/1.94  Parsing              : 0.17
% 4.85/1.94  CNF conversion       : 0.02
% 4.85/1.94  Main loop            : 0.83
% 4.85/1.94  Inferencing          : 0.29
% 4.85/1.94  Reduction            : 0.37
% 4.85/1.94  Demodulation         : 0.32
% 4.85/1.94  BG Simplification    : 0.04
% 4.85/1.94  Subsumption          : 0.10
% 4.85/1.94  Abstraction          : 0.05
% 4.85/1.94  MUC search           : 0.00
% 4.85/1.94  Cooper               : 0.00
% 4.85/1.94  Total                : 1.18
% 4.85/1.94  Index Insertion      : 0.00
% 4.85/1.94  Index Deletion       : 0.00
% 4.85/1.94  Index Matching       : 0.00
% 4.85/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
