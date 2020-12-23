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
% DateTime   : Thu Dec  3 09:47:49 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   52 (  62 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :   15
%              Number of atoms          :   34 (  44 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_10,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_16,B_17] : k1_enumset1(A_16,A_16,B_17) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_18,B_19,C_20] : k2_enumset1(A_18,A_18,B_19,C_20) = k1_enumset1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_21,B_22,C_23,D_24] : k3_enumset1(A_21,A_21,B_22,C_23,D_24) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_25,E_29,C_27,D_28,B_26] : k4_enumset1(A_25,A_25,B_26,C_27,D_28,E_29) = k3_enumset1(A_25,B_26,C_27,D_28,E_29) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,F_35] : k5_enumset1(A_30,A_30,B_31,C_32,D_33,E_34,F_35) = k4_enumset1(A_30,B_31,C_32,D_33,E_34,F_35) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [F_41,G_42,D_39,A_36,E_40,C_38,B_37] : k6_enumset1(A_36,A_36,B_37,C_38,D_39,E_40,F_41,G_42) = k5_enumset1(A_36,B_37,C_38,D_39,E_40,F_41,G_42) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_107,plain,(
    ! [E_83,B_78,D_77,C_79,H_84,G_81,F_82,A_80] : k2_xboole_0(k5_enumset1(A_80,B_78,C_79,D_77,E_83,F_82,G_81),k1_tarski(H_84)) = k6_enumset1(A_80,B_78,C_79,D_77,E_83,F_82,G_81,H_84) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_123,plain,(
    ! [A_85,H_89,C_91,F_87,E_92,G_88,B_86,D_90] : r1_tarski(k5_enumset1(A_85,B_86,C_91,D_90,E_92,F_87,G_88),k6_enumset1(A_85,B_86,C_91,D_90,E_92,F_87,G_88,H_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_4])).

tff(c_126,plain,(
    ! [F_41,G_42,D_39,A_36,E_40,C_38,B_37] : r1_tarski(k5_enumset1(A_36,A_36,B_37,C_38,D_39,E_40,F_41),k5_enumset1(A_36,B_37,C_38,D_39,E_40,F_41,G_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_123])).

tff(c_132,plain,(
    ! [A_95,G_93,D_96,E_99,F_94,B_97,C_98] : r1_tarski(k4_enumset1(A_95,B_97,C_98,D_96,E_99,F_94),k5_enumset1(A_95,B_97,C_98,D_96,E_99,F_94,G_93)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_126])).

tff(c_135,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,F_35] : r1_tarski(k4_enumset1(A_30,A_30,B_31,C_32,D_33,E_34),k4_enumset1(A_30,B_31,C_32,D_33,E_34,F_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_132])).

tff(c_141,plain,(
    ! [E_104,F_102,B_101,A_103,D_105,C_100] : r1_tarski(k3_enumset1(A_103,B_101,C_100,D_105,E_104),k4_enumset1(A_103,B_101,C_100,D_105,E_104,F_102)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_135])).

tff(c_144,plain,(
    ! [A_25,E_29,C_27,D_28,B_26] : r1_tarski(k3_enumset1(A_25,A_25,B_26,C_27,D_28),k3_enumset1(A_25,B_26,C_27,D_28,E_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_141])).

tff(c_167,plain,(
    ! [C_115,E_117,D_113,B_116,A_114] : r1_tarski(k2_enumset1(A_114,B_116,C_115,D_113),k3_enumset1(A_114,B_116,C_115,D_113,E_117)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_144])).

tff(c_170,plain,(
    ! [A_21,B_22,C_23,D_24] : r1_tarski(k2_enumset1(A_21,A_21,B_22,C_23),k2_enumset1(A_21,B_22,C_23,D_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_167])).

tff(c_176,plain,(
    ! [A_118,B_119,C_120,D_121] : r1_tarski(k1_enumset1(A_118,B_119,C_120),k2_enumset1(A_118,B_119,C_120,D_121)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_170])).

tff(c_179,plain,(
    ! [A_18,B_19,C_20] : r1_tarski(k1_enumset1(A_18,A_18,B_19),k1_enumset1(A_18,B_19,C_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_176])).

tff(c_185,plain,(
    ! [A_122,B_123,C_124] : r1_tarski(k2_tarski(A_122,B_123),k1_enumset1(A_122,B_123,C_124)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_179])).

tff(c_188,plain,(
    ! [A_16,B_17] : r1_tarski(k2_tarski(A_16,A_16),k2_tarski(A_16,B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_185])).

tff(c_192,plain,(
    ! [A_16,B_17] : r1_tarski(k1_tarski(A_16),k2_tarski(A_16,B_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_188])).

tff(c_24,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:15:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.17  
% 1.77/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.17  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.77/1.17  
% 1.77/1.17  %Foreground sorts:
% 1.77/1.17  
% 1.77/1.17  
% 1.77/1.17  %Background operators:
% 1.77/1.17  
% 1.77/1.17  
% 1.77/1.17  %Foreground operators:
% 1.77/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.77/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.77/1.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.77/1.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.77/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.77/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.77/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.77/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.77/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.77/1.17  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.77/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.77/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.77/1.17  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.77/1.17  
% 1.77/1.18  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.77/1.18  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.77/1.18  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.77/1.18  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.77/1.18  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.77/1.18  tff(f_45, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.77/1.18  tff(f_47, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 1.77/1.18  tff(f_33, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 1.77/1.18  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.77/1.18  tff(f_50, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.77/1.18  tff(c_10, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.77/1.18  tff(c_12, plain, (![A_16, B_17]: (k1_enumset1(A_16, A_16, B_17)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.77/1.18  tff(c_14, plain, (![A_18, B_19, C_20]: (k2_enumset1(A_18, A_18, B_19, C_20)=k1_enumset1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.77/1.18  tff(c_16, plain, (![A_21, B_22, C_23, D_24]: (k3_enumset1(A_21, A_21, B_22, C_23, D_24)=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.77/1.18  tff(c_18, plain, (![A_25, E_29, C_27, D_28, B_26]: (k4_enumset1(A_25, A_25, B_26, C_27, D_28, E_29)=k3_enumset1(A_25, B_26, C_27, D_28, E_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.77/1.18  tff(c_20, plain, (![D_33, A_30, C_32, B_31, E_34, F_35]: (k5_enumset1(A_30, A_30, B_31, C_32, D_33, E_34, F_35)=k4_enumset1(A_30, B_31, C_32, D_33, E_34, F_35))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.77/1.18  tff(c_22, plain, (![F_41, G_42, D_39, A_36, E_40, C_38, B_37]: (k6_enumset1(A_36, A_36, B_37, C_38, D_39, E_40, F_41, G_42)=k5_enumset1(A_36, B_37, C_38, D_39, E_40, F_41, G_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.77/1.18  tff(c_107, plain, (![E_83, B_78, D_77, C_79, H_84, G_81, F_82, A_80]: (k2_xboole_0(k5_enumset1(A_80, B_78, C_79, D_77, E_83, F_82, G_81), k1_tarski(H_84))=k6_enumset1(A_80, B_78, C_79, D_77, E_83, F_82, G_81, H_84))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.77/1.18  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.77/1.18  tff(c_123, plain, (![A_85, H_89, C_91, F_87, E_92, G_88, B_86, D_90]: (r1_tarski(k5_enumset1(A_85, B_86, C_91, D_90, E_92, F_87, G_88), k6_enumset1(A_85, B_86, C_91, D_90, E_92, F_87, G_88, H_89)))), inference(superposition, [status(thm), theory('equality')], [c_107, c_4])).
% 1.77/1.18  tff(c_126, plain, (![F_41, G_42, D_39, A_36, E_40, C_38, B_37]: (r1_tarski(k5_enumset1(A_36, A_36, B_37, C_38, D_39, E_40, F_41), k5_enumset1(A_36, B_37, C_38, D_39, E_40, F_41, G_42)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_123])).
% 1.77/1.18  tff(c_132, plain, (![A_95, G_93, D_96, E_99, F_94, B_97, C_98]: (r1_tarski(k4_enumset1(A_95, B_97, C_98, D_96, E_99, F_94), k5_enumset1(A_95, B_97, C_98, D_96, E_99, F_94, G_93)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_126])).
% 1.77/1.18  tff(c_135, plain, (![D_33, A_30, C_32, B_31, E_34, F_35]: (r1_tarski(k4_enumset1(A_30, A_30, B_31, C_32, D_33, E_34), k4_enumset1(A_30, B_31, C_32, D_33, E_34, F_35)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_132])).
% 1.77/1.18  tff(c_141, plain, (![E_104, F_102, B_101, A_103, D_105, C_100]: (r1_tarski(k3_enumset1(A_103, B_101, C_100, D_105, E_104), k4_enumset1(A_103, B_101, C_100, D_105, E_104, F_102)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_135])).
% 1.77/1.18  tff(c_144, plain, (![A_25, E_29, C_27, D_28, B_26]: (r1_tarski(k3_enumset1(A_25, A_25, B_26, C_27, D_28), k3_enumset1(A_25, B_26, C_27, D_28, E_29)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_141])).
% 1.77/1.18  tff(c_167, plain, (![C_115, E_117, D_113, B_116, A_114]: (r1_tarski(k2_enumset1(A_114, B_116, C_115, D_113), k3_enumset1(A_114, B_116, C_115, D_113, E_117)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_144])).
% 1.77/1.18  tff(c_170, plain, (![A_21, B_22, C_23, D_24]: (r1_tarski(k2_enumset1(A_21, A_21, B_22, C_23), k2_enumset1(A_21, B_22, C_23, D_24)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_167])).
% 1.77/1.18  tff(c_176, plain, (![A_118, B_119, C_120, D_121]: (r1_tarski(k1_enumset1(A_118, B_119, C_120), k2_enumset1(A_118, B_119, C_120, D_121)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_170])).
% 1.77/1.18  tff(c_179, plain, (![A_18, B_19, C_20]: (r1_tarski(k1_enumset1(A_18, A_18, B_19), k1_enumset1(A_18, B_19, C_20)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_176])).
% 1.77/1.18  tff(c_185, plain, (![A_122, B_123, C_124]: (r1_tarski(k2_tarski(A_122, B_123), k1_enumset1(A_122, B_123, C_124)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_179])).
% 1.77/1.18  tff(c_188, plain, (![A_16, B_17]: (r1_tarski(k2_tarski(A_16, A_16), k2_tarski(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_185])).
% 1.77/1.18  tff(c_192, plain, (![A_16, B_17]: (r1_tarski(k1_tarski(A_16), k2_tarski(A_16, B_17)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_188])).
% 1.77/1.18  tff(c_24, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.77/1.18  tff(c_196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_192, c_24])).
% 1.77/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.18  
% 1.77/1.18  Inference rules
% 1.77/1.18  ----------------------
% 1.77/1.18  #Ref     : 0
% 1.77/1.18  #Sup     : 38
% 1.77/1.18  #Fact    : 0
% 1.77/1.18  #Define  : 0
% 1.77/1.18  #Split   : 0
% 1.77/1.18  #Chain   : 0
% 1.77/1.18  #Close   : 0
% 1.77/1.18  
% 1.77/1.18  Ordering : KBO
% 1.77/1.18  
% 1.77/1.18  Simplification rules
% 1.77/1.18  ----------------------
% 1.77/1.18  #Subsume      : 0
% 1.77/1.18  #Demod        : 16
% 1.77/1.18  #Tautology    : 23
% 1.77/1.18  #SimpNegUnit  : 0
% 1.77/1.18  #BackRed      : 1
% 1.77/1.18  
% 1.77/1.18  #Partial instantiations: 0
% 1.77/1.18  #Strategies tried      : 1
% 1.77/1.18  
% 1.77/1.18  Timing (in seconds)
% 1.77/1.18  ----------------------
% 2.05/1.19  Preprocessing        : 0.29
% 2.05/1.19  Parsing              : 0.16
% 2.05/1.19  CNF conversion       : 0.02
% 2.05/1.19  Main loop            : 0.14
% 2.05/1.19  Inferencing          : 0.06
% 2.05/1.19  Reduction            : 0.05
% 2.05/1.19  Demodulation         : 0.04
% 2.05/1.19  BG Simplification    : 0.01
% 2.05/1.19  Subsumption          : 0.02
% 2.05/1.19  Abstraction          : 0.01
% 2.05/1.19  MUC search           : 0.00
% 2.05/1.19  Cooper               : 0.00
% 2.05/1.19  Total                : 0.46
% 2.05/1.19  Index Insertion      : 0.00
% 2.05/1.19  Index Deletion       : 0.00
% 2.05/1.19  Index Matching       : 0.00
% 2.05/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
