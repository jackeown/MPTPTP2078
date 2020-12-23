%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:48 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   49 (  53 expanded)
%              Number of leaves         :   28 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :   31 (  35 expanded)
%              Number of equality atoms :   16 (  20 expanded)
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

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

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
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_12,plain,(
    ! [A_16,B_17] : k1_enumset1(A_16,A_16,B_17) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_18,B_19,C_20] : k2_enumset1(A_18,A_18,B_19,C_20) = k1_enumset1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_21,B_22,C_23,D_24] : k3_enumset1(A_21,A_21,B_22,C_23,D_24) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

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
    ! [E_83,B_78,D_77,C_79,H_84,G_81,F_82,A_80] : k2_xboole_0(k2_enumset1(A_80,B_78,C_79,D_77),k2_enumset1(E_83,F_82,G_81,H_84)) = k6_enumset1(A_80,B_78,C_79,D_77,E_83,F_82,G_81,H_84) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_126,plain,(
    ! [A_85,H_89,C_91,F_87,E_92,G_88,B_86,D_90] : r1_tarski(k2_enumset1(A_85,B_86,C_91,D_90),k6_enumset1(A_85,B_86,C_91,D_90,E_92,F_87,G_88,H_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_4])).

tff(c_129,plain,(
    ! [F_41,G_42,D_39,A_36,E_40,C_38,B_37] : r1_tarski(k2_enumset1(A_36,A_36,B_37,C_38),k5_enumset1(A_36,B_37,C_38,D_39,E_40,F_41,G_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_126])).

tff(c_135,plain,(
    ! [A_95,G_93,D_96,E_99,F_94,B_97,C_98] : r1_tarski(k1_enumset1(A_95,B_97,C_98),k5_enumset1(A_95,B_97,C_98,D_96,E_99,F_94,G_93)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_129])).

tff(c_138,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,F_35] : r1_tarski(k1_enumset1(A_30,A_30,B_31),k4_enumset1(A_30,B_31,C_32,D_33,E_34,F_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_135])).

tff(c_144,plain,(
    ! [E_104,F_102,B_101,A_103,D_105,C_100] : r1_tarski(k2_tarski(A_103,B_101),k4_enumset1(A_103,B_101,C_100,D_105,E_104,F_102)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_138])).

tff(c_147,plain,(
    ! [A_25,E_29,C_27,D_28,B_26] : r1_tarski(k2_tarski(A_25,A_25),k3_enumset1(A_25,B_26,C_27,D_28,E_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_144])).

tff(c_173,plain,(
    ! [C_115,E_117,D_113,B_116,A_114] : r1_tarski(k1_tarski(A_114),k3_enumset1(A_114,B_116,C_115,D_113,E_117)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_147])).

tff(c_177,plain,(
    ! [A_118,B_119,C_120,D_121] : r1_tarski(k1_tarski(A_118),k2_enumset1(A_118,B_119,C_120,D_121)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_173])).

tff(c_181,plain,(
    ! [A_122,B_123,C_124] : r1_tarski(k1_tarski(A_122),k1_enumset1(A_122,B_123,C_124)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_177])).

tff(c_184,plain,(
    ! [A_16,B_17] : r1_tarski(k1_tarski(A_16),k2_tarski(A_16,B_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_181])).

tff(c_24,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:33:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.17  
% 1.97/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.18  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.97/1.18  
% 1.97/1.18  %Foreground sorts:
% 1.97/1.18  
% 1.97/1.18  
% 1.97/1.18  %Background operators:
% 1.97/1.18  
% 1.97/1.18  
% 1.97/1.18  %Foreground operators:
% 1.97/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.97/1.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.97/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.97/1.18  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.18  
% 2.01/1.19  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.01/1.19  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.01/1.19  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.01/1.19  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.01/1.19  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.01/1.19  tff(f_45, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.01/1.19  tff(f_47, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.01/1.19  tff(f_33, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 2.01/1.19  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.01/1.19  tff(f_50, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.01/1.19  tff(c_12, plain, (![A_16, B_17]: (k1_enumset1(A_16, A_16, B_17)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.01/1.19  tff(c_14, plain, (![A_18, B_19, C_20]: (k2_enumset1(A_18, A_18, B_19, C_20)=k1_enumset1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.01/1.19  tff(c_16, plain, (![A_21, B_22, C_23, D_24]: (k3_enumset1(A_21, A_21, B_22, C_23, D_24)=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.01/1.19  tff(c_10, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.01/1.19  tff(c_18, plain, (![A_25, E_29, C_27, D_28, B_26]: (k4_enumset1(A_25, A_25, B_26, C_27, D_28, E_29)=k3_enumset1(A_25, B_26, C_27, D_28, E_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.01/1.19  tff(c_20, plain, (![D_33, A_30, C_32, B_31, E_34, F_35]: (k5_enumset1(A_30, A_30, B_31, C_32, D_33, E_34, F_35)=k4_enumset1(A_30, B_31, C_32, D_33, E_34, F_35))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.01/1.19  tff(c_22, plain, (![F_41, G_42, D_39, A_36, E_40, C_38, B_37]: (k6_enumset1(A_36, A_36, B_37, C_38, D_39, E_40, F_41, G_42)=k5_enumset1(A_36, B_37, C_38, D_39, E_40, F_41, G_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.01/1.19  tff(c_107, plain, (![E_83, B_78, D_77, C_79, H_84, G_81, F_82, A_80]: (k2_xboole_0(k2_enumset1(A_80, B_78, C_79, D_77), k2_enumset1(E_83, F_82, G_81, H_84))=k6_enumset1(A_80, B_78, C_79, D_77, E_83, F_82, G_81, H_84))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.01/1.19  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.01/1.19  tff(c_126, plain, (![A_85, H_89, C_91, F_87, E_92, G_88, B_86, D_90]: (r1_tarski(k2_enumset1(A_85, B_86, C_91, D_90), k6_enumset1(A_85, B_86, C_91, D_90, E_92, F_87, G_88, H_89)))), inference(superposition, [status(thm), theory('equality')], [c_107, c_4])).
% 2.01/1.19  tff(c_129, plain, (![F_41, G_42, D_39, A_36, E_40, C_38, B_37]: (r1_tarski(k2_enumset1(A_36, A_36, B_37, C_38), k5_enumset1(A_36, B_37, C_38, D_39, E_40, F_41, G_42)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_126])).
% 2.01/1.19  tff(c_135, plain, (![A_95, G_93, D_96, E_99, F_94, B_97, C_98]: (r1_tarski(k1_enumset1(A_95, B_97, C_98), k5_enumset1(A_95, B_97, C_98, D_96, E_99, F_94, G_93)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_129])).
% 2.01/1.19  tff(c_138, plain, (![D_33, A_30, C_32, B_31, E_34, F_35]: (r1_tarski(k1_enumset1(A_30, A_30, B_31), k4_enumset1(A_30, B_31, C_32, D_33, E_34, F_35)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_135])).
% 2.01/1.19  tff(c_144, plain, (![E_104, F_102, B_101, A_103, D_105, C_100]: (r1_tarski(k2_tarski(A_103, B_101), k4_enumset1(A_103, B_101, C_100, D_105, E_104, F_102)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_138])).
% 2.01/1.19  tff(c_147, plain, (![A_25, E_29, C_27, D_28, B_26]: (r1_tarski(k2_tarski(A_25, A_25), k3_enumset1(A_25, B_26, C_27, D_28, E_29)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_144])).
% 2.01/1.19  tff(c_173, plain, (![C_115, E_117, D_113, B_116, A_114]: (r1_tarski(k1_tarski(A_114), k3_enumset1(A_114, B_116, C_115, D_113, E_117)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_147])).
% 2.01/1.19  tff(c_177, plain, (![A_118, B_119, C_120, D_121]: (r1_tarski(k1_tarski(A_118), k2_enumset1(A_118, B_119, C_120, D_121)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_173])).
% 2.01/1.19  tff(c_181, plain, (![A_122, B_123, C_124]: (r1_tarski(k1_tarski(A_122), k1_enumset1(A_122, B_123, C_124)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_177])).
% 2.01/1.19  tff(c_184, plain, (![A_16, B_17]: (r1_tarski(k1_tarski(A_16), k2_tarski(A_16, B_17)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_181])).
% 2.01/1.19  tff(c_24, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.01/1.19  tff(c_187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_184, c_24])).
% 2.01/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.19  
% 2.01/1.19  Inference rules
% 2.01/1.19  ----------------------
% 2.01/1.19  #Ref     : 0
% 2.01/1.19  #Sup     : 37
% 2.01/1.19  #Fact    : 0
% 2.01/1.19  #Define  : 0
% 2.01/1.19  #Split   : 0
% 2.01/1.19  #Chain   : 0
% 2.01/1.19  #Close   : 0
% 2.01/1.19  
% 2.01/1.19  Ordering : KBO
% 2.01/1.19  
% 2.01/1.19  Simplification rules
% 2.01/1.19  ----------------------
% 2.01/1.19  #Subsume      : 0
% 2.01/1.19  #Demod        : 10
% 2.01/1.19  #Tautology    : 23
% 2.01/1.19  #SimpNegUnit  : 0
% 2.01/1.19  #BackRed      : 1
% 2.01/1.19  
% 2.01/1.19  #Partial instantiations: 0
% 2.01/1.19  #Strategies tried      : 1
% 2.01/1.19  
% 2.01/1.19  Timing (in seconds)
% 2.01/1.19  ----------------------
% 2.01/1.19  Preprocessing        : 0.29
% 2.01/1.19  Parsing              : 0.16
% 2.01/1.19  CNF conversion       : 0.02
% 2.01/1.19  Main loop            : 0.14
% 2.01/1.19  Inferencing          : 0.06
% 2.01/1.19  Reduction            : 0.04
% 2.01/1.19  Demodulation         : 0.03
% 2.01/1.19  BG Simplification    : 0.01
% 2.01/1.19  Subsumption          : 0.01
% 2.01/1.19  Abstraction          : 0.01
% 2.01/1.19  MUC search           : 0.00
% 2.01/1.19  Cooper               : 0.00
% 2.01/1.19  Total                : 0.45
% 2.01/1.19  Index Insertion      : 0.00
% 2.01/1.19  Index Deletion       : 0.00
% 2.01/1.19  Index Matching       : 0.00
% 2.01/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
