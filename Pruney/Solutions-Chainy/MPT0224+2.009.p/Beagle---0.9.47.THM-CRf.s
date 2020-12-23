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
% DateTime   : Thu Dec  3 09:48:30 EST 2020

% Result     : Theorem 7.10s
% Output     : CNFRefutation 7.10s
% Verified   : 
% Statistics : Number of formulae       :   57 (  61 expanded)
%              Number of leaves         :   32 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :   37 (  41 expanded)
%              Number of equality atoms :   36 (  40 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_28,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_32,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(c_4,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_24,plain,(
    ! [A_23,B_24] : k1_enumset1(A_23,A_23,B_24) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26,plain,(
    ! [A_25,B_26,C_27] : k2_enumset1(A_25,A_25,B_26,C_27) = k1_enumset1(A_25,B_26,C_27) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    ! [A_28,B_29,C_30,D_31] : k3_enumset1(A_28,A_28,B_29,C_30,D_31) = k2_enumset1(A_28,B_29,C_30,D_31) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_30,plain,(
    ! [B_33,C_34,E_36,A_32,D_35] : k4_enumset1(A_32,A_32,B_33,C_34,D_35,E_36) = k3_enumset1(A_32,B_33,C_34,D_35,E_36) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    ! [C_39,B_38,A_37,D_40,F_42,E_41] : k5_enumset1(A_37,A_37,B_38,C_39,D_40,E_41,F_42) = k4_enumset1(A_37,B_38,C_39,D_40,E_41,F_42) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    ! [G_49,E_47,F_48,D_46,C_45,A_43,B_44] : k6_enumset1(A_43,A_43,B_44,C_45,D_46,E_47,F_48,G_49) = k5_enumset1(A_43,B_44,C_45,D_46,E_47,F_48,G_49) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_788,plain,(
    ! [D_116,H_113,G_117,B_119,F_115,A_120,E_114,C_118] : k2_xboole_0(k2_enumset1(A_120,B_119,C_118,D_116),k2_enumset1(E_114,F_115,G_117,H_113)) = k6_enumset1(A_120,B_119,C_118,D_116,E_114,F_115,G_117,H_113) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_837,plain,(
    ! [H_113,A_25,G_117,F_115,C_27,E_114,B_26] : k6_enumset1(A_25,A_25,B_26,C_27,E_114,F_115,G_117,H_113) = k2_xboole_0(k1_enumset1(A_25,B_26,C_27),k2_enumset1(E_114,F_115,G_117,H_113)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_788])).

tff(c_2938,plain,(
    ! [C_161,G_165,A_160,E_159,H_163,B_162,F_164] : k2_xboole_0(k1_enumset1(A_160,B_162,C_161),k2_enumset1(E_159,F_164,G_165,H_163)) = k5_enumset1(A_160,B_162,C_161,E_159,F_164,G_165,H_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_837])).

tff(c_8,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k2_xboole_0(A_4,B_5)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6935,plain,(
    ! [G_221,E_219,A_223,C_220,H_224,F_222,B_218] : k4_xboole_0(k1_enumset1(A_223,B_218,C_220),k5_enumset1(A_223,B_218,C_220,E_219,F_222,G_221,H_224)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2938,c_8])).

tff(c_6960,plain,(
    ! [C_39,B_38,A_37,D_40,F_42,E_41] : k4_xboole_0(k1_enumset1(A_37,A_37,B_38),k4_enumset1(A_37,B_38,C_39,D_40,E_41,F_42)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_6935])).

tff(c_6973,plain,(
    ! [D_228,A_225,B_226,C_230,E_229,F_227] : k4_xboole_0(k2_tarski(A_225,B_226),k4_enumset1(A_225,B_226,C_230,D_228,E_229,F_227)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_6960])).

tff(c_6998,plain,(
    ! [B_33,C_34,E_36,A_32,D_35] : k4_xboole_0(k2_tarski(A_32,A_32),k3_enumset1(A_32,B_33,C_34,D_35,E_36)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_6973])).

tff(c_7011,plain,(
    ! [C_233,A_234,B_232,D_235,E_231] : k4_xboole_0(k1_tarski(A_234),k3_enumset1(A_234,B_232,C_233,D_235,E_231)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6998])).

tff(c_7044,plain,(
    ! [A_236,B_237,C_238,D_239] : k4_xboole_0(k1_tarski(A_236),k2_enumset1(A_236,B_237,C_238,D_239)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_7011])).

tff(c_7077,plain,(
    ! [A_240,B_241,C_242] : k4_xboole_0(k1_tarski(A_240),k1_enumset1(A_240,B_241,C_242)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_7044])).

tff(c_7110,plain,(
    ! [A_243,B_244] : k4_xboole_0(k1_tarski(A_243),k2_tarski(A_243,B_244)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_7077])).

tff(c_10,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_7130,plain,(
    ! [A_243,B_244] : k3_xboole_0(k1_tarski(A_243),k2_tarski(A_243,B_244)) = k4_xboole_0(k1_tarski(A_243),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7110,c_10])).

tff(c_7141,plain,(
    ! [A_243,B_244] : k3_xboole_0(k1_tarski(A_243),k2_tarski(A_243,B_244)) = k1_tarski(A_243) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_7130])).

tff(c_36,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7141,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:16:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.10/2.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.10/2.53  
% 7.10/2.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.10/2.53  %$ r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1
% 7.10/2.53  
% 7.10/2.53  %Foreground sorts:
% 7.10/2.53  
% 7.10/2.53  
% 7.10/2.53  %Background operators:
% 7.10/2.53  
% 7.10/2.53  
% 7.10/2.53  %Foreground operators:
% 7.10/2.53  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 7.10/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.10/2.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.10/2.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.10/2.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.10/2.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.10/2.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.10/2.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.10/2.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.10/2.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.10/2.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.10/2.53  tff('#skF_2', type, '#skF_2': $i).
% 7.10/2.53  tff('#skF_1', type, '#skF_1': $i).
% 7.10/2.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.10/2.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.10/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.10/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.10/2.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.10/2.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.10/2.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.10/2.53  
% 7.10/2.55  tff(f_28, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.10/2.55  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.10/2.55  tff(f_52, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 7.10/2.55  tff(f_54, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 7.10/2.55  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 7.10/2.55  tff(f_56, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 7.10/2.55  tff(f_58, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 7.10/2.55  tff(f_60, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 7.10/2.55  tff(f_46, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l75_enumset1)).
% 7.10/2.55  tff(f_32, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 7.10/2.55  tff(f_34, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.10/2.55  tff(f_63, negated_conjecture, ~(![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 7.10/2.55  tff(c_4, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 7.10/2.55  tff(c_24, plain, (![A_23, B_24]: (k1_enumset1(A_23, A_23, B_24)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.10/2.55  tff(c_26, plain, (![A_25, B_26, C_27]: (k2_enumset1(A_25, A_25, B_26, C_27)=k1_enumset1(A_25, B_26, C_27))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.10/2.55  tff(c_28, plain, (![A_28, B_29, C_30, D_31]: (k3_enumset1(A_28, A_28, B_29, C_30, D_31)=k2_enumset1(A_28, B_29, C_30, D_31))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.10/2.55  tff(c_22, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.10/2.55  tff(c_30, plain, (![B_33, C_34, E_36, A_32, D_35]: (k4_enumset1(A_32, A_32, B_33, C_34, D_35, E_36)=k3_enumset1(A_32, B_33, C_34, D_35, E_36))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.10/2.55  tff(c_32, plain, (![C_39, B_38, A_37, D_40, F_42, E_41]: (k5_enumset1(A_37, A_37, B_38, C_39, D_40, E_41, F_42)=k4_enumset1(A_37, B_38, C_39, D_40, E_41, F_42))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.10/2.55  tff(c_34, plain, (![G_49, E_47, F_48, D_46, C_45, A_43, B_44]: (k6_enumset1(A_43, A_43, B_44, C_45, D_46, E_47, F_48, G_49)=k5_enumset1(A_43, B_44, C_45, D_46, E_47, F_48, G_49))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.10/2.55  tff(c_788, plain, (![D_116, H_113, G_117, B_119, F_115, A_120, E_114, C_118]: (k2_xboole_0(k2_enumset1(A_120, B_119, C_118, D_116), k2_enumset1(E_114, F_115, G_117, H_113))=k6_enumset1(A_120, B_119, C_118, D_116, E_114, F_115, G_117, H_113))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.10/2.55  tff(c_837, plain, (![H_113, A_25, G_117, F_115, C_27, E_114, B_26]: (k6_enumset1(A_25, A_25, B_26, C_27, E_114, F_115, G_117, H_113)=k2_xboole_0(k1_enumset1(A_25, B_26, C_27), k2_enumset1(E_114, F_115, G_117, H_113)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_788])).
% 7.10/2.55  tff(c_2938, plain, (![C_161, G_165, A_160, E_159, H_163, B_162, F_164]: (k2_xboole_0(k1_enumset1(A_160, B_162, C_161), k2_enumset1(E_159, F_164, G_165, H_163))=k5_enumset1(A_160, B_162, C_161, E_159, F_164, G_165, H_163))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_837])).
% 7.10/2.55  tff(c_8, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k2_xboole_0(A_4, B_5))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.10/2.55  tff(c_6935, plain, (![G_221, E_219, A_223, C_220, H_224, F_222, B_218]: (k4_xboole_0(k1_enumset1(A_223, B_218, C_220), k5_enumset1(A_223, B_218, C_220, E_219, F_222, G_221, H_224))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2938, c_8])).
% 7.10/2.55  tff(c_6960, plain, (![C_39, B_38, A_37, D_40, F_42, E_41]: (k4_xboole_0(k1_enumset1(A_37, A_37, B_38), k4_enumset1(A_37, B_38, C_39, D_40, E_41, F_42))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_6935])).
% 7.10/2.55  tff(c_6973, plain, (![D_228, A_225, B_226, C_230, E_229, F_227]: (k4_xboole_0(k2_tarski(A_225, B_226), k4_enumset1(A_225, B_226, C_230, D_228, E_229, F_227))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_6960])).
% 7.10/2.55  tff(c_6998, plain, (![B_33, C_34, E_36, A_32, D_35]: (k4_xboole_0(k2_tarski(A_32, A_32), k3_enumset1(A_32, B_33, C_34, D_35, E_36))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_6973])).
% 7.10/2.55  tff(c_7011, plain, (![C_233, A_234, B_232, D_235, E_231]: (k4_xboole_0(k1_tarski(A_234), k3_enumset1(A_234, B_232, C_233, D_235, E_231))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6998])).
% 7.10/2.55  tff(c_7044, plain, (![A_236, B_237, C_238, D_239]: (k4_xboole_0(k1_tarski(A_236), k2_enumset1(A_236, B_237, C_238, D_239))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_7011])).
% 7.10/2.55  tff(c_7077, plain, (![A_240, B_241, C_242]: (k4_xboole_0(k1_tarski(A_240), k1_enumset1(A_240, B_241, C_242))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_7044])).
% 7.10/2.55  tff(c_7110, plain, (![A_243, B_244]: (k4_xboole_0(k1_tarski(A_243), k2_tarski(A_243, B_244))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_7077])).
% 7.10/2.55  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.10/2.55  tff(c_7130, plain, (![A_243, B_244]: (k3_xboole_0(k1_tarski(A_243), k2_tarski(A_243, B_244))=k4_xboole_0(k1_tarski(A_243), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7110, c_10])).
% 7.10/2.55  tff(c_7141, plain, (![A_243, B_244]: (k3_xboole_0(k1_tarski(A_243), k2_tarski(A_243, B_244))=k1_tarski(A_243))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_7130])).
% 7.10/2.55  tff(c_36, plain, (k3_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.10/2.55  tff(c_7147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7141, c_36])).
% 7.10/2.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.10/2.55  
% 7.10/2.55  Inference rules
% 7.10/2.55  ----------------------
% 7.10/2.55  #Ref     : 0
% 7.10/2.55  #Sup     : 1793
% 7.10/2.55  #Fact    : 0
% 7.10/2.55  #Define  : 0
% 7.10/2.55  #Split   : 0
% 7.10/2.55  #Chain   : 0
% 7.10/2.55  #Close   : 0
% 7.10/2.55  
% 7.10/2.55  Ordering : KBO
% 7.10/2.55  
% 7.10/2.55  Simplification rules
% 7.10/2.55  ----------------------
% 7.10/2.55  #Subsume      : 108
% 7.10/2.55  #Demod        : 2584
% 7.10/2.55  #Tautology    : 848
% 7.10/2.55  #SimpNegUnit  : 0
% 7.10/2.55  #BackRed      : 2
% 7.10/2.55  
% 7.10/2.55  #Partial instantiations: 0
% 7.10/2.55  #Strategies tried      : 1
% 7.10/2.55  
% 7.10/2.55  Timing (in seconds)
% 7.10/2.55  ----------------------
% 7.10/2.55  Preprocessing        : 0.31
% 7.10/2.55  Parsing              : 0.17
% 7.10/2.55  CNF conversion       : 0.02
% 7.10/2.55  Main loop            : 1.48
% 7.10/2.55  Inferencing          : 0.38
% 7.10/2.55  Reduction            : 0.80
% 7.10/2.55  Demodulation         : 0.71
% 7.10/2.55  BG Simplification    : 0.05
% 7.10/2.55  Subsumption          : 0.17
% 7.10/2.55  Abstraction          : 0.09
% 7.10/2.55  MUC search           : 0.00
% 7.10/2.55  Cooper               : 0.00
% 7.10/2.55  Total                : 1.82
% 7.10/2.55  Index Insertion      : 0.00
% 7.10/2.55  Index Deletion       : 0.00
% 7.10/2.55  Index Matching       : 0.00
% 7.10/2.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
