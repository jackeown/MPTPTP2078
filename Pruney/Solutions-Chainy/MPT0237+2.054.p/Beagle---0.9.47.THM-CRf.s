%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:52 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   49 (  59 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :   14
%              Number of atoms          :   34 (  44 expanded)
%              Number of equality atoms :   33 (  43 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(c_6,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_12,B_13,C_14] : k2_enumset1(A_12,A_12,B_13,C_14) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_15,B_16,C_17,D_18] : k3_enumset1(A_15,A_15,B_16,C_17,D_18) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_19,C_21,D_22,B_20,E_23] : k4_enumset1(A_19,A_19,B_20,C_21,D_22,E_23) = k3_enumset1(A_19,B_20,C_21,D_22,E_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,E_28] : k5_enumset1(A_24,A_24,B_25,C_26,D_27,E_28,F_29) = k4_enumset1(A_24,B_25,C_26,D_27,E_28,F_29) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,G_36,F_35] : k6_enumset1(A_30,A_30,B_31,C_32,D_33,E_34,F_35,G_36) = k5_enumset1(A_30,B_31,C_32,D_33,E_34,F_35,G_36) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_114,plain,(
    ! [E_72,A_76,F_70,G_71,D_73,C_75,B_74,H_77] : k2_xboole_0(k5_enumset1(A_76,B_74,C_75,D_73,E_72,F_70,G_71),k1_tarski(H_77)) = k6_enumset1(A_76,B_74,C_75,D_73,E_72,F_70,G_71,H_77) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_123,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,H_77,E_28] : k6_enumset1(A_24,A_24,B_25,C_26,D_27,E_28,F_29,H_77) = k2_xboole_0(k4_enumset1(A_24,B_25,C_26,D_27,E_28,F_29),k1_tarski(H_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_114])).

tff(c_127,plain,(
    ! [C_78,A_82,E_80,D_84,B_79,F_81,H_83] : k2_xboole_0(k4_enumset1(A_82,B_79,C_78,D_84,E_80,F_81),k1_tarski(H_83)) = k5_enumset1(A_82,B_79,C_78,D_84,E_80,F_81,H_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_123])).

tff(c_136,plain,(
    ! [A_19,C_21,D_22,B_20,H_83,E_23] : k5_enumset1(A_19,A_19,B_20,C_21,D_22,E_23,H_83) = k2_xboole_0(k3_enumset1(A_19,B_20,C_21,D_22,E_23),k1_tarski(H_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_127])).

tff(c_140,plain,(
    ! [C_85,B_88,A_89,H_87,E_86,D_90] : k2_xboole_0(k3_enumset1(A_89,B_88,C_85,D_90,E_86),k1_tarski(H_87)) = k4_enumset1(A_89,B_88,C_85,D_90,E_86,H_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_136])).

tff(c_149,plain,(
    ! [B_16,A_15,D_18,H_87,C_17] : k4_enumset1(A_15,A_15,B_16,C_17,D_18,H_87) = k2_xboole_0(k2_enumset1(A_15,B_16,C_17,D_18),k1_tarski(H_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_140])).

tff(c_153,plain,(
    ! [A_95,B_94,C_91,H_92,D_93] : k2_xboole_0(k2_enumset1(A_95,B_94,C_91,D_93),k1_tarski(H_92)) = k3_enumset1(A_95,B_94,C_91,D_93,H_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_149])).

tff(c_162,plain,(
    ! [A_12,B_13,C_14,H_92] : k3_enumset1(A_12,A_12,B_13,C_14,H_92) = k2_xboole_0(k1_enumset1(A_12,B_13,C_14),k1_tarski(H_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_153])).

tff(c_166,plain,(
    ! [A_96,B_97,C_98,H_99] : k2_xboole_0(k1_enumset1(A_96,B_97,C_98),k1_tarski(H_99)) = k2_enumset1(A_96,B_97,C_98,H_99) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_162])).

tff(c_175,plain,(
    ! [A_10,B_11,H_99] : k2_xboole_0(k2_tarski(A_10,B_11),k1_tarski(H_99)) = k2_enumset1(A_10,A_10,B_11,H_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_166])).

tff(c_179,plain,(
    ! [A_100,B_101,H_102] : k2_xboole_0(k2_tarski(A_100,B_101),k1_tarski(H_102)) = k1_enumset1(A_100,B_101,H_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_175])).

tff(c_188,plain,(
    ! [A_9,H_102] : k2_xboole_0(k1_tarski(A_9),k1_tarski(H_102)) = k1_enumset1(A_9,A_9,H_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_179])).

tff(c_191,plain,(
    ! [A_9,H_102] : k2_xboole_0(k1_tarski(A_9),k1_tarski(H_102)) = k2_tarski(A_9,H_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_188])).

tff(c_18,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_21,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:46:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.20  
% 2.01/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.21  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.01/1.21  
% 2.01/1.21  %Foreground sorts:
% 2.01/1.21  
% 2.01/1.21  
% 2.01/1.21  %Background operators:
% 2.01/1.21  
% 2.01/1.21  
% 2.01/1.21  %Foreground operators:
% 2.01/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.01/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.01/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.01/1.21  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.21  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.01/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.01/1.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.01/1.21  
% 2.01/1.22  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.01/1.22  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.01/1.22  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.01/1.22  tff(f_35, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.01/1.22  tff(f_37, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.01/1.22  tff(f_39, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.01/1.22  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 2.01/1.22  tff(f_27, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_enumset1)).
% 2.01/1.22  tff(f_43, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.01/1.22  tff(f_46, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 2.01/1.22  tff(c_6, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.01/1.22  tff(c_4, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.01/1.22  tff(c_8, plain, (![A_12, B_13, C_14]: (k2_enumset1(A_12, A_12, B_13, C_14)=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.01/1.22  tff(c_10, plain, (![A_15, B_16, C_17, D_18]: (k3_enumset1(A_15, A_15, B_16, C_17, D_18)=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.01/1.22  tff(c_12, plain, (![A_19, C_21, D_22, B_20, E_23]: (k4_enumset1(A_19, A_19, B_20, C_21, D_22, E_23)=k3_enumset1(A_19, B_20, C_21, D_22, E_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.01/1.22  tff(c_14, plain, (![A_24, B_25, F_29, D_27, C_26, E_28]: (k5_enumset1(A_24, A_24, B_25, C_26, D_27, E_28, F_29)=k4_enumset1(A_24, B_25, C_26, D_27, E_28, F_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.01/1.22  tff(c_16, plain, (![D_33, A_30, C_32, B_31, E_34, G_36, F_35]: (k6_enumset1(A_30, A_30, B_31, C_32, D_33, E_34, F_35, G_36)=k5_enumset1(A_30, B_31, C_32, D_33, E_34, F_35, G_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.01/1.22  tff(c_114, plain, (![E_72, A_76, F_70, G_71, D_73, C_75, B_74, H_77]: (k2_xboole_0(k5_enumset1(A_76, B_74, C_75, D_73, E_72, F_70, G_71), k1_tarski(H_77))=k6_enumset1(A_76, B_74, C_75, D_73, E_72, F_70, G_71, H_77))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.01/1.22  tff(c_123, plain, (![A_24, B_25, F_29, D_27, C_26, H_77, E_28]: (k6_enumset1(A_24, A_24, B_25, C_26, D_27, E_28, F_29, H_77)=k2_xboole_0(k4_enumset1(A_24, B_25, C_26, D_27, E_28, F_29), k1_tarski(H_77)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_114])).
% 2.01/1.22  tff(c_127, plain, (![C_78, A_82, E_80, D_84, B_79, F_81, H_83]: (k2_xboole_0(k4_enumset1(A_82, B_79, C_78, D_84, E_80, F_81), k1_tarski(H_83))=k5_enumset1(A_82, B_79, C_78, D_84, E_80, F_81, H_83))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_123])).
% 2.01/1.22  tff(c_136, plain, (![A_19, C_21, D_22, B_20, H_83, E_23]: (k5_enumset1(A_19, A_19, B_20, C_21, D_22, E_23, H_83)=k2_xboole_0(k3_enumset1(A_19, B_20, C_21, D_22, E_23), k1_tarski(H_83)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_127])).
% 2.01/1.22  tff(c_140, plain, (![C_85, B_88, A_89, H_87, E_86, D_90]: (k2_xboole_0(k3_enumset1(A_89, B_88, C_85, D_90, E_86), k1_tarski(H_87))=k4_enumset1(A_89, B_88, C_85, D_90, E_86, H_87))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_136])).
% 2.01/1.22  tff(c_149, plain, (![B_16, A_15, D_18, H_87, C_17]: (k4_enumset1(A_15, A_15, B_16, C_17, D_18, H_87)=k2_xboole_0(k2_enumset1(A_15, B_16, C_17, D_18), k1_tarski(H_87)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_140])).
% 2.01/1.22  tff(c_153, plain, (![A_95, B_94, C_91, H_92, D_93]: (k2_xboole_0(k2_enumset1(A_95, B_94, C_91, D_93), k1_tarski(H_92))=k3_enumset1(A_95, B_94, C_91, D_93, H_92))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_149])).
% 2.01/1.22  tff(c_162, plain, (![A_12, B_13, C_14, H_92]: (k3_enumset1(A_12, A_12, B_13, C_14, H_92)=k2_xboole_0(k1_enumset1(A_12, B_13, C_14), k1_tarski(H_92)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_153])).
% 2.01/1.22  tff(c_166, plain, (![A_96, B_97, C_98, H_99]: (k2_xboole_0(k1_enumset1(A_96, B_97, C_98), k1_tarski(H_99))=k2_enumset1(A_96, B_97, C_98, H_99))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_162])).
% 2.01/1.22  tff(c_175, plain, (![A_10, B_11, H_99]: (k2_xboole_0(k2_tarski(A_10, B_11), k1_tarski(H_99))=k2_enumset1(A_10, A_10, B_11, H_99))), inference(superposition, [status(thm), theory('equality')], [c_6, c_166])).
% 2.01/1.22  tff(c_179, plain, (![A_100, B_101, H_102]: (k2_xboole_0(k2_tarski(A_100, B_101), k1_tarski(H_102))=k1_enumset1(A_100, B_101, H_102))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_175])).
% 2.01/1.22  tff(c_188, plain, (![A_9, H_102]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(H_102))=k1_enumset1(A_9, A_9, H_102))), inference(superposition, [status(thm), theory('equality')], [c_4, c_179])).
% 2.01/1.22  tff(c_191, plain, (![A_9, H_102]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(H_102))=k2_tarski(A_9, H_102))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_188])).
% 2.01/1.22  tff(c_18, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.01/1.22  tff(c_20, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.01/1.22  tff(c_21, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20])).
% 2.01/1.22  tff(c_194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_191, c_21])).
% 2.01/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.22  
% 2.01/1.22  Inference rules
% 2.01/1.22  ----------------------
% 2.01/1.22  #Ref     : 0
% 2.01/1.22  #Sup     : 39
% 2.01/1.22  #Fact    : 0
% 2.01/1.22  #Define  : 0
% 2.01/1.22  #Split   : 0
% 2.01/1.22  #Chain   : 0
% 2.01/1.22  #Close   : 0
% 2.01/1.22  
% 2.01/1.22  Ordering : KBO
% 2.01/1.22  
% 2.01/1.22  Simplification rules
% 2.01/1.22  ----------------------
% 2.01/1.22  #Subsume      : 0
% 2.01/1.22  #Demod        : 8
% 2.01/1.22  #Tautology    : 32
% 2.01/1.22  #SimpNegUnit  : 0
% 2.01/1.22  #BackRed      : 1
% 2.01/1.22  
% 2.01/1.22  #Partial instantiations: 0
% 2.01/1.22  #Strategies tried      : 1
% 2.01/1.22  
% 2.01/1.22  Timing (in seconds)
% 2.01/1.22  ----------------------
% 2.01/1.22  Preprocessing        : 0.29
% 2.01/1.22  Parsing              : 0.16
% 2.01/1.22  CNF conversion       : 0.02
% 2.01/1.22  Main loop            : 0.14
% 2.01/1.22  Inferencing          : 0.07
% 2.01/1.22  Reduction            : 0.04
% 2.01/1.22  Demodulation         : 0.04
% 2.01/1.22  BG Simplification    : 0.01
% 2.01/1.22  Subsumption          : 0.01
% 2.01/1.22  Abstraction          : 0.01
% 2.01/1.22  MUC search           : 0.00
% 2.01/1.22  Cooper               : 0.00
% 2.01/1.22  Total                : 0.46
% 2.01/1.22  Index Insertion      : 0.00
% 2.01/1.22  Index Deletion       : 0.00
% 2.01/1.22  Index Matching       : 0.00
% 2.01/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
