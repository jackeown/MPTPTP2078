%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:45 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   57 (  67 expanded)
%              Number of leaves         :   30 (  35 expanded)
%              Depth                    :   14
%              Number of atoms          :   39 (  49 expanded)
%              Number of equality atoms :   38 (  48 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_235,plain,(
    ! [C_68,B_69,A_70] : k1_enumset1(C_68,B_69,A_70) = k1_enumset1(A_70,B_69,C_68) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_21,B_22] : k1_enumset1(A_21,A_21,B_22) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_251,plain,(
    ! [C_68,B_69] : k1_enumset1(C_68,B_69,B_69) = k2_tarski(B_69,C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_16])).

tff(c_14,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [D_33,A_30,C_32,B_31,E_34] : k4_enumset1(A_30,A_30,B_31,C_32,D_33,E_34) = k3_enumset1(A_30,B_31,C_32,D_33,E_34) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_23,B_24,C_25] : k2_enumset1(A_23,A_23,B_24,C_25) = k1_enumset1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39] : k5_enumset1(A_35,A_35,B_36,C_37,D_38,E_39,F_40) = k4_enumset1(A_35,B_36,C_37,D_38,E_39,F_40) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_26,B_27,C_28,D_29] : k3_enumset1(A_26,A_26,B_27,C_28,D_29) = k2_enumset1(A_26,B_27,C_28,D_29) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [D_44,F_46,C_43,A_41,B_42,G_47,E_45] : k6_enumset1(A_41,A_41,B_42,C_43,D_44,E_45,F_46,G_47) = k5_enumset1(A_41,B_42,C_43,D_44,E_45,F_46,G_47) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_395,plain,(
    ! [H_102,E_104,F_106,B_101,A_103,G_100,D_105,C_107] : k2_xboole_0(k4_enumset1(A_103,B_101,C_107,D_105,E_104,F_106),k2_tarski(G_100,H_102)) = k6_enumset1(A_103,B_101,C_107,D_105,E_104,F_106,G_100,H_102) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_410,plain,(
    ! [H_102,D_33,A_30,C_32,B_31,E_34,G_100] : k6_enumset1(A_30,A_30,B_31,C_32,D_33,E_34,G_100,H_102) = k2_xboole_0(k3_enumset1(A_30,B_31,C_32,D_33,E_34),k2_tarski(G_100,H_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_395])).

tff(c_429,plain,(
    ! [H_109,A_112,C_108,B_110,D_114,G_111,E_113] : k2_xboole_0(k3_enumset1(A_112,B_110,C_108,D_114,E_113),k2_tarski(G_111,H_109)) = k5_enumset1(A_112,B_110,C_108,D_114,E_113,G_111,H_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_410])).

tff(c_444,plain,(
    ! [H_109,B_27,D_29,A_26,G_111,C_28] : k5_enumset1(A_26,A_26,B_27,C_28,D_29,G_111,H_109) = k2_xboole_0(k2_enumset1(A_26,B_27,C_28,D_29),k2_tarski(G_111,H_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_429])).

tff(c_463,plain,(
    ! [G_119,D_115,A_117,H_118,B_116,C_120] : k2_xboole_0(k2_enumset1(A_117,B_116,C_120,D_115),k2_tarski(G_119,H_118)) = k4_enumset1(A_117,B_116,C_120,D_115,G_119,H_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_444])).

tff(c_478,plain,(
    ! [G_119,A_23,B_24,H_118,C_25] : k4_enumset1(A_23,A_23,B_24,C_25,G_119,H_118) = k2_xboole_0(k1_enumset1(A_23,B_24,C_25),k2_tarski(G_119,H_118)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_463])).

tff(c_497,plain,(
    ! [H_121,C_122,G_124,A_125,B_123] : k2_xboole_0(k1_enumset1(A_125,B_123,C_122),k2_tarski(G_124,H_121)) = k3_enumset1(A_125,B_123,C_122,G_124,H_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_478])).

tff(c_540,plain,(
    ! [A_126,B_127,C_128,A_129] : k3_enumset1(A_126,B_127,C_128,A_129,A_129) = k2_xboole_0(k1_enumset1(A_126,B_127,C_128),k1_tarski(A_129)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_497])).

tff(c_553,plain,(
    ! [B_127,C_128,A_129] : k2_xboole_0(k1_enumset1(B_127,B_127,C_128),k1_tarski(A_129)) = k2_enumset1(B_127,C_128,A_129,A_129) ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_20])).

tff(c_594,plain,(
    ! [B_130,C_131,A_132] : k2_xboole_0(k2_tarski(B_130,C_131),k1_tarski(A_132)) = k2_enumset1(B_130,C_131,A_132,A_132) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_553])).

tff(c_607,plain,(
    ! [C_131,A_132] : k2_xboole_0(k2_tarski(C_131,C_131),k1_tarski(A_132)) = k1_enumset1(C_131,A_132,A_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_18])).

tff(c_641,plain,(
    ! [C_131,A_132] : k2_xboole_0(k1_tarski(C_131),k1_tarski(A_132)) = k2_tarski(A_132,C_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_14,c_607])).

tff(c_28,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_31,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_645,plain,(
    k2_tarski('#skF_2','#skF_1') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_31])).

tff(c_648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_645])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.38  
% 2.38/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.38  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.38/1.38  
% 2.38/1.38  %Foreground sorts:
% 2.38/1.38  
% 2.38/1.38  
% 2.38/1.38  %Background operators:
% 2.38/1.38  
% 2.38/1.38  
% 2.38/1.38  %Foreground operators:
% 2.38/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.38/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.38/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.38/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.38/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.38/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.38/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.38/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.38/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.38/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.38/1.38  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.38/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.38/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.38/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.38/1.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.38/1.38  
% 2.73/1.40  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.73/1.40  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_enumset1)).
% 2.73/1.40  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.73/1.40  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.73/1.40  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.73/1.40  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.73/1.40  tff(f_49, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.73/1.40  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.73/1.40  tff(f_51, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.73/1.40  tff(f_37, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 2.73/1.40  tff(f_53, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.73/1.40  tff(f_56, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 2.73/1.40  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.73/1.40  tff(c_235, plain, (![C_68, B_69, A_70]: (k1_enumset1(C_68, B_69, A_70)=k1_enumset1(A_70, B_69, C_68))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.73/1.40  tff(c_16, plain, (![A_21, B_22]: (k1_enumset1(A_21, A_21, B_22)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.73/1.40  tff(c_251, plain, (![C_68, B_69]: (k1_enumset1(C_68, B_69, B_69)=k2_tarski(B_69, C_68))), inference(superposition, [status(thm), theory('equality')], [c_235, c_16])).
% 2.73/1.40  tff(c_14, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.73/1.40  tff(c_22, plain, (![D_33, A_30, C_32, B_31, E_34]: (k4_enumset1(A_30, A_30, B_31, C_32, D_33, E_34)=k3_enumset1(A_30, B_31, C_32, D_33, E_34))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.73/1.40  tff(c_18, plain, (![A_23, B_24, C_25]: (k2_enumset1(A_23, A_23, B_24, C_25)=k1_enumset1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.73/1.40  tff(c_24, plain, (![A_35, F_40, B_36, C_37, D_38, E_39]: (k5_enumset1(A_35, A_35, B_36, C_37, D_38, E_39, F_40)=k4_enumset1(A_35, B_36, C_37, D_38, E_39, F_40))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.73/1.40  tff(c_20, plain, (![A_26, B_27, C_28, D_29]: (k3_enumset1(A_26, A_26, B_27, C_28, D_29)=k2_enumset1(A_26, B_27, C_28, D_29))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.73/1.40  tff(c_26, plain, (![D_44, F_46, C_43, A_41, B_42, G_47, E_45]: (k6_enumset1(A_41, A_41, B_42, C_43, D_44, E_45, F_46, G_47)=k5_enumset1(A_41, B_42, C_43, D_44, E_45, F_46, G_47))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.73/1.40  tff(c_395, plain, (![H_102, E_104, F_106, B_101, A_103, G_100, D_105, C_107]: (k2_xboole_0(k4_enumset1(A_103, B_101, C_107, D_105, E_104, F_106), k2_tarski(G_100, H_102))=k6_enumset1(A_103, B_101, C_107, D_105, E_104, F_106, G_100, H_102))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.73/1.40  tff(c_410, plain, (![H_102, D_33, A_30, C_32, B_31, E_34, G_100]: (k6_enumset1(A_30, A_30, B_31, C_32, D_33, E_34, G_100, H_102)=k2_xboole_0(k3_enumset1(A_30, B_31, C_32, D_33, E_34), k2_tarski(G_100, H_102)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_395])).
% 2.73/1.40  tff(c_429, plain, (![H_109, A_112, C_108, B_110, D_114, G_111, E_113]: (k2_xboole_0(k3_enumset1(A_112, B_110, C_108, D_114, E_113), k2_tarski(G_111, H_109))=k5_enumset1(A_112, B_110, C_108, D_114, E_113, G_111, H_109))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_410])).
% 2.73/1.40  tff(c_444, plain, (![H_109, B_27, D_29, A_26, G_111, C_28]: (k5_enumset1(A_26, A_26, B_27, C_28, D_29, G_111, H_109)=k2_xboole_0(k2_enumset1(A_26, B_27, C_28, D_29), k2_tarski(G_111, H_109)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_429])).
% 2.73/1.40  tff(c_463, plain, (![G_119, D_115, A_117, H_118, B_116, C_120]: (k2_xboole_0(k2_enumset1(A_117, B_116, C_120, D_115), k2_tarski(G_119, H_118))=k4_enumset1(A_117, B_116, C_120, D_115, G_119, H_118))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_444])).
% 2.73/1.40  tff(c_478, plain, (![G_119, A_23, B_24, H_118, C_25]: (k4_enumset1(A_23, A_23, B_24, C_25, G_119, H_118)=k2_xboole_0(k1_enumset1(A_23, B_24, C_25), k2_tarski(G_119, H_118)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_463])).
% 2.73/1.40  tff(c_497, plain, (![H_121, C_122, G_124, A_125, B_123]: (k2_xboole_0(k1_enumset1(A_125, B_123, C_122), k2_tarski(G_124, H_121))=k3_enumset1(A_125, B_123, C_122, G_124, H_121))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_478])).
% 2.73/1.40  tff(c_540, plain, (![A_126, B_127, C_128, A_129]: (k3_enumset1(A_126, B_127, C_128, A_129, A_129)=k2_xboole_0(k1_enumset1(A_126, B_127, C_128), k1_tarski(A_129)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_497])).
% 2.73/1.40  tff(c_553, plain, (![B_127, C_128, A_129]: (k2_xboole_0(k1_enumset1(B_127, B_127, C_128), k1_tarski(A_129))=k2_enumset1(B_127, C_128, A_129, A_129))), inference(superposition, [status(thm), theory('equality')], [c_540, c_20])).
% 2.73/1.40  tff(c_594, plain, (![B_130, C_131, A_132]: (k2_xboole_0(k2_tarski(B_130, C_131), k1_tarski(A_132))=k2_enumset1(B_130, C_131, A_132, A_132))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_553])).
% 2.73/1.40  tff(c_607, plain, (![C_131, A_132]: (k2_xboole_0(k2_tarski(C_131, C_131), k1_tarski(A_132))=k1_enumset1(C_131, A_132, A_132))), inference(superposition, [status(thm), theory('equality')], [c_594, c_18])).
% 2.73/1.40  tff(c_641, plain, (![C_131, A_132]: (k2_xboole_0(k1_tarski(C_131), k1_tarski(A_132))=k2_tarski(A_132, C_131))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_14, c_607])).
% 2.73/1.40  tff(c_28, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.73/1.40  tff(c_30, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.73/1.40  tff(c_31, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30])).
% 2.73/1.40  tff(c_645, plain, (k2_tarski('#skF_2', '#skF_1')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_641, c_31])).
% 2.73/1.40  tff(c_648, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_645])).
% 2.73/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.40  
% 2.73/1.40  Inference rules
% 2.73/1.40  ----------------------
% 2.73/1.40  #Ref     : 0
% 2.73/1.40  #Sup     : 158
% 2.73/1.40  #Fact    : 0
% 2.73/1.40  #Define  : 0
% 2.73/1.40  #Split   : 0
% 2.73/1.40  #Chain   : 0
% 2.73/1.40  #Close   : 0
% 2.73/1.40  
% 2.73/1.40  Ordering : KBO
% 2.73/1.40  
% 2.73/1.40  Simplification rules
% 2.73/1.40  ----------------------
% 2.73/1.40  #Subsume      : 2
% 2.73/1.40  #Demod        : 30
% 2.73/1.40  #Tautology    : 95
% 2.73/1.40  #SimpNegUnit  : 0
% 2.73/1.40  #BackRed      : 1
% 2.73/1.40  
% 2.73/1.40  #Partial instantiations: 0
% 2.73/1.40  #Strategies tried      : 1
% 2.73/1.40  
% 2.73/1.40  Timing (in seconds)
% 2.73/1.40  ----------------------
% 2.73/1.40  Preprocessing        : 0.34
% 2.73/1.40  Parsing              : 0.18
% 2.73/1.40  CNF conversion       : 0.02
% 2.73/1.40  Main loop            : 0.28
% 2.73/1.40  Inferencing          : 0.11
% 2.73/1.40  Reduction            : 0.10
% 2.73/1.40  Demodulation         : 0.08
% 2.73/1.40  BG Simplification    : 0.02
% 2.73/1.40  Subsumption          : 0.04
% 2.73/1.40  Abstraction          : 0.02
% 2.73/1.40  MUC search           : 0.00
% 2.73/1.40  Cooper               : 0.00
% 2.73/1.40  Total                : 0.65
% 2.73/1.40  Index Insertion      : 0.00
% 2.73/1.40  Index Deletion       : 0.00
% 2.73/1.40  Index Matching       : 0.00
% 2.73/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
