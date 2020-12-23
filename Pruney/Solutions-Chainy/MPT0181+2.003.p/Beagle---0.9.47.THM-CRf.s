%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:41 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   49 (  85 expanded)
%              Number of leaves         :   26 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :   32 (  68 expanded)
%              Number of equality atoms :   31 (  67 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_20,B_21,C_22,D_23] : k3_enumset1(A_20,A_20,B_21,C_22,D_23) = k2_enumset1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_15,B_16] : k1_enumset1(A_15,A_15,B_16) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_24,B_25,D_27,C_26,E_28] : k4_enumset1(A_24,A_24,B_25,C_26,D_27,E_28) = k3_enumset1(A_24,B_25,C_26,D_27,E_28) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_17,B_18,C_19] : k2_enumset1(A_17,A_17,B_18,C_19) = k1_enumset1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [E_33,A_29,F_34,D_32,C_31,B_30] : k5_enumset1(A_29,A_29,B_30,C_31,D_32,E_33,F_34) = k4_enumset1(A_29,B_30,C_31,D_32,E_33,F_34) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39,G_41] : k6_enumset1(A_35,A_35,B_36,C_37,D_38,E_39,F_40,G_41) = k5_enumset1(A_35,B_36,C_37,D_38,E_39,F_40,G_41) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_128,plain,(
    ! [H_82,F_80,G_79,A_78,E_81,D_75,C_77,B_76] : k2_xboole_0(k4_enumset1(A_78,B_76,C_77,D_75,E_81,F_80),k2_tarski(G_79,H_82)) = k6_enumset1(A_78,B_76,C_77,D_75,E_81,F_80,G_79,H_82) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_137,plain,(
    ! [H_82,A_24,B_25,D_27,C_26,G_79,E_28] : k6_enumset1(A_24,A_24,B_25,C_26,D_27,E_28,G_79,H_82) = k2_xboole_0(k3_enumset1(A_24,B_25,C_26,D_27,E_28),k2_tarski(G_79,H_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_128])).

tff(c_147,plain,(
    ! [G_87,H_86,A_88,D_89,B_84,E_85,C_83] : k2_xboole_0(k3_enumset1(A_88,B_84,C_83,D_89,E_85),k2_tarski(G_87,H_86)) = k5_enumset1(A_88,B_84,C_83,D_89,E_85,G_87,H_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_137])).

tff(c_156,plain,(
    ! [G_87,H_86,C_22,D_23,A_20,B_21] : k5_enumset1(A_20,A_20,B_21,C_22,D_23,G_87,H_86) = k2_xboole_0(k2_enumset1(A_20,B_21,C_22,D_23),k2_tarski(G_87,H_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_147])).

tff(c_166,plain,(
    ! [H_93,A_95,B_92,D_94,G_91,C_90] : k2_xboole_0(k2_enumset1(A_95,B_92,C_90,D_94),k2_tarski(G_91,H_93)) = k4_enumset1(A_95,B_92,C_90,D_94,G_91,H_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_156])).

tff(c_175,plain,(
    ! [H_93,C_19,B_18,A_17,G_91] : k4_enumset1(A_17,A_17,B_18,C_19,G_91,H_93) = k2_xboole_0(k1_enumset1(A_17,B_18,C_19),k2_tarski(G_91,H_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_166])).

tff(c_185,plain,(
    ! [B_98,H_100,C_96,G_99,A_97] : k2_xboole_0(k1_enumset1(A_97,B_98,C_96),k2_tarski(G_99,H_100)) = k3_enumset1(A_97,B_98,C_96,G_99,H_100) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_175])).

tff(c_194,plain,(
    ! [A_15,B_16,G_99,H_100] : k3_enumset1(A_15,A_15,B_16,G_99,H_100) = k2_xboole_0(k2_tarski(A_15,B_16),k2_tarski(G_99,H_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_185])).

tff(c_204,plain,(
    ! [A_101,B_102,G_103,H_104] : k2_xboole_0(k2_tarski(A_101,B_102),k2_tarski(G_103,H_104)) = k2_enumset1(A_101,B_102,G_103,H_104) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_194])).

tff(c_321,plain,(
    ! [A_121,B_122,A_123,B_124] : k2_xboole_0(k2_tarski(A_121,B_122),k2_tarski(A_123,B_124)) = k2_enumset1(A_121,B_122,B_124,A_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_204])).

tff(c_213,plain,(
    ! [B_6,A_5,G_103,H_104] : k2_xboole_0(k2_tarski(B_6,A_5),k2_tarski(G_103,H_104)) = k2_enumset1(A_5,B_6,G_103,H_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_204])).

tff(c_356,plain,(
    ! [B_125,A_126,A_127,B_128] : k2_enumset1(B_125,A_126,A_127,B_128) = k2_enumset1(A_126,B_125,B_128,A_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_213])).

tff(c_433,plain,(
    ! [B_129,A_130,B_131] : k2_enumset1(B_129,B_129,A_130,B_131) = k1_enumset1(B_129,B_131,A_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_12])).

tff(c_448,plain,(
    ! [B_129,B_131,A_130] : k1_enumset1(B_129,B_131,A_130) = k1_enumset1(B_129,A_130,B_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_12])).

tff(c_22,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.30  
% 2.19/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.30  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.19/1.30  
% 2.19/1.30  %Foreground sorts:
% 2.19/1.30  
% 2.19/1.30  
% 2.19/1.30  %Background operators:
% 2.19/1.30  
% 2.19/1.30  
% 2.19/1.30  %Foreground operators:
% 2.19/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.19/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.19/1.30  
% 2.19/1.31  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.19/1.31  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.19/1.31  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.19/1.31  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.19/1.31  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.19/1.31  tff(f_43, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 2.19/1.31  tff(f_45, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 2.19/1.31  tff(f_33, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 2.19/1.31  tff(f_48, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 2.19/1.31  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.31  tff(c_14, plain, (![A_20, B_21, C_22, D_23]: (k3_enumset1(A_20, A_20, B_21, C_22, D_23)=k2_enumset1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.19/1.31  tff(c_10, plain, (![A_15, B_16]: (k1_enumset1(A_15, A_15, B_16)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.19/1.31  tff(c_16, plain, (![A_24, B_25, D_27, C_26, E_28]: (k4_enumset1(A_24, A_24, B_25, C_26, D_27, E_28)=k3_enumset1(A_24, B_25, C_26, D_27, E_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.19/1.31  tff(c_12, plain, (![A_17, B_18, C_19]: (k2_enumset1(A_17, A_17, B_18, C_19)=k1_enumset1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.31  tff(c_18, plain, (![E_33, A_29, F_34, D_32, C_31, B_30]: (k5_enumset1(A_29, A_29, B_30, C_31, D_32, E_33, F_34)=k4_enumset1(A_29, B_30, C_31, D_32, E_33, F_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.19/1.31  tff(c_20, plain, (![A_35, F_40, B_36, C_37, D_38, E_39, G_41]: (k6_enumset1(A_35, A_35, B_36, C_37, D_38, E_39, F_40, G_41)=k5_enumset1(A_35, B_36, C_37, D_38, E_39, F_40, G_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.19/1.31  tff(c_128, plain, (![H_82, F_80, G_79, A_78, E_81, D_75, C_77, B_76]: (k2_xboole_0(k4_enumset1(A_78, B_76, C_77, D_75, E_81, F_80), k2_tarski(G_79, H_82))=k6_enumset1(A_78, B_76, C_77, D_75, E_81, F_80, G_79, H_82))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.19/1.31  tff(c_137, plain, (![H_82, A_24, B_25, D_27, C_26, G_79, E_28]: (k6_enumset1(A_24, A_24, B_25, C_26, D_27, E_28, G_79, H_82)=k2_xboole_0(k3_enumset1(A_24, B_25, C_26, D_27, E_28), k2_tarski(G_79, H_82)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_128])).
% 2.19/1.31  tff(c_147, plain, (![G_87, H_86, A_88, D_89, B_84, E_85, C_83]: (k2_xboole_0(k3_enumset1(A_88, B_84, C_83, D_89, E_85), k2_tarski(G_87, H_86))=k5_enumset1(A_88, B_84, C_83, D_89, E_85, G_87, H_86))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_137])).
% 2.19/1.31  tff(c_156, plain, (![G_87, H_86, C_22, D_23, A_20, B_21]: (k5_enumset1(A_20, A_20, B_21, C_22, D_23, G_87, H_86)=k2_xboole_0(k2_enumset1(A_20, B_21, C_22, D_23), k2_tarski(G_87, H_86)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_147])).
% 2.19/1.31  tff(c_166, plain, (![H_93, A_95, B_92, D_94, G_91, C_90]: (k2_xboole_0(k2_enumset1(A_95, B_92, C_90, D_94), k2_tarski(G_91, H_93))=k4_enumset1(A_95, B_92, C_90, D_94, G_91, H_93))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_156])).
% 2.19/1.31  tff(c_175, plain, (![H_93, C_19, B_18, A_17, G_91]: (k4_enumset1(A_17, A_17, B_18, C_19, G_91, H_93)=k2_xboole_0(k1_enumset1(A_17, B_18, C_19), k2_tarski(G_91, H_93)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_166])).
% 2.19/1.31  tff(c_185, plain, (![B_98, H_100, C_96, G_99, A_97]: (k2_xboole_0(k1_enumset1(A_97, B_98, C_96), k2_tarski(G_99, H_100))=k3_enumset1(A_97, B_98, C_96, G_99, H_100))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_175])).
% 2.19/1.31  tff(c_194, plain, (![A_15, B_16, G_99, H_100]: (k3_enumset1(A_15, A_15, B_16, G_99, H_100)=k2_xboole_0(k2_tarski(A_15, B_16), k2_tarski(G_99, H_100)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_185])).
% 2.19/1.31  tff(c_204, plain, (![A_101, B_102, G_103, H_104]: (k2_xboole_0(k2_tarski(A_101, B_102), k2_tarski(G_103, H_104))=k2_enumset1(A_101, B_102, G_103, H_104))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_194])).
% 2.19/1.31  tff(c_321, plain, (![A_121, B_122, A_123, B_124]: (k2_xboole_0(k2_tarski(A_121, B_122), k2_tarski(A_123, B_124))=k2_enumset1(A_121, B_122, B_124, A_123))), inference(superposition, [status(thm), theory('equality')], [c_6, c_204])).
% 2.19/1.31  tff(c_213, plain, (![B_6, A_5, G_103, H_104]: (k2_xboole_0(k2_tarski(B_6, A_5), k2_tarski(G_103, H_104))=k2_enumset1(A_5, B_6, G_103, H_104))), inference(superposition, [status(thm), theory('equality')], [c_6, c_204])).
% 2.19/1.31  tff(c_356, plain, (![B_125, A_126, A_127, B_128]: (k2_enumset1(B_125, A_126, A_127, B_128)=k2_enumset1(A_126, B_125, B_128, A_127))), inference(superposition, [status(thm), theory('equality')], [c_321, c_213])).
% 2.19/1.31  tff(c_433, plain, (![B_129, A_130, B_131]: (k2_enumset1(B_129, B_129, A_130, B_131)=k1_enumset1(B_129, B_131, A_130))), inference(superposition, [status(thm), theory('equality')], [c_356, c_12])).
% 2.19/1.31  tff(c_448, plain, (![B_129, B_131, A_130]: (k1_enumset1(B_129, B_131, A_130)=k1_enumset1(B_129, A_130, B_131))), inference(superposition, [status(thm), theory('equality')], [c_433, c_12])).
% 2.19/1.31  tff(c_22, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.19/1.31  tff(c_472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_448, c_22])).
% 2.19/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.31  
% 2.19/1.31  Inference rules
% 2.19/1.31  ----------------------
% 2.19/1.31  #Ref     : 0
% 2.19/1.31  #Sup     : 116
% 2.19/1.31  #Fact    : 0
% 2.19/1.31  #Define  : 0
% 2.19/1.31  #Split   : 0
% 2.19/1.31  #Chain   : 0
% 2.19/1.31  #Close   : 0
% 2.19/1.31  
% 2.19/1.31  Ordering : KBO
% 2.19/1.31  
% 2.19/1.31  Simplification rules
% 2.19/1.31  ----------------------
% 2.19/1.31  #Subsume      : 1
% 2.19/1.31  #Demod        : 20
% 2.19/1.31  #Tautology    : 69
% 2.19/1.31  #SimpNegUnit  : 0
% 2.19/1.31  #BackRed      : 1
% 2.19/1.31  
% 2.19/1.31  #Partial instantiations: 0
% 2.19/1.31  #Strategies tried      : 1
% 2.19/1.31  
% 2.19/1.31  Timing (in seconds)
% 2.19/1.31  ----------------------
% 2.19/1.32  Preprocessing        : 0.30
% 2.19/1.32  Parsing              : 0.16
% 2.19/1.32  CNF conversion       : 0.02
% 2.19/1.32  Main loop            : 0.27
% 2.19/1.32  Inferencing          : 0.11
% 2.19/1.32  Reduction            : 0.10
% 2.19/1.32  Demodulation         : 0.08
% 2.19/1.32  BG Simplification    : 0.02
% 2.19/1.32  Subsumption          : 0.03
% 2.19/1.32  Abstraction          : 0.02
% 2.19/1.32  MUC search           : 0.00
% 2.19/1.32  Cooper               : 0.00
% 2.19/1.32  Total                : 0.59
% 2.19/1.32  Index Insertion      : 0.00
% 2.19/1.32  Index Deletion       : 0.00
% 2.19/1.32  Index Matching       : 0.00
% 2.19/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
