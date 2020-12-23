%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:47 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 176 expanded)
%              Number of leaves         :   30 (  75 expanded)
%              Depth                    :   21
%              Number of atoms          :   51 ( 160 expanded)
%              Number of equality atoms :   46 ( 155 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E,F] : k6_enumset1(A,A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(c_16,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_19,B_20,C_21] : k2_enumset1(A_19,A_19,B_20,C_21) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_22,B_23,C_24,D_25] : k3_enumset1(A_22,A_22,B_23,C_24,D_25) = k2_enumset1(A_22,B_23,C_24,D_25) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [B_27,D_29,A_26,E_30,C_28] : k4_enumset1(A_26,A_26,B_27,C_28,D_29,E_30) = k3_enumset1(A_26,B_27,C_28,D_29,E_30) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,D_34] : k6_enumset1(A_31,A_31,A_31,B_32,C_33,D_34,E_35,F_36) = k4_enumset1(A_31,B_32,C_33,D_34,E_35,F_36) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_127,plain,(
    ! [H_75,C_73,A_70,B_72,F_69,E_71,G_74,D_76] : k2_xboole_0(k4_enumset1(A_70,B_72,C_73,D_76,E_71,F_69),k2_tarski(G_74,H_75)) = k6_enumset1(A_70,B_72,C_73,D_76,E_71,F_69,G_74,H_75) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_148,plain,(
    ! [D_81,E_77,A_78,B_80,A_79,C_82,F_83] : k6_enumset1(A_78,B_80,C_82,D_81,E_77,F_83,A_79,A_79) = k2_xboole_0(k4_enumset1(A_78,B_80,C_82,D_81,E_77,F_83),k1_tarski(A_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_127])).

tff(c_158,plain,(
    ! [D_81,E_77,A_79,C_82,F_83] : k4_enumset1(C_82,D_81,E_77,F_83,A_79,A_79) = k2_xboole_0(k4_enumset1(C_82,C_82,C_82,D_81,E_77,F_83),k1_tarski(A_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_24])).

tff(c_184,plain,(
    ! [A_85,E_88,C_84,D_86,F_87] : k4_enumset1(C_84,D_86,E_88,F_87,A_85,A_85) = k2_xboole_0(k2_enumset1(C_84,D_86,E_88,F_87),k1_tarski(A_85)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_158])).

tff(c_200,plain,(
    ! [D_86,E_88,F_87,A_85] : k3_enumset1(D_86,E_88,F_87,A_85,A_85) = k2_xboole_0(k2_enumset1(D_86,D_86,E_88,F_87),k1_tarski(A_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_22])).

tff(c_226,plain,(
    ! [D_89,E_90,F_91,A_92] : k3_enumset1(D_89,E_90,F_91,A_92,A_92) = k2_xboole_0(k1_enumset1(D_89,E_90,F_91),k1_tarski(A_92)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_200])).

tff(c_236,plain,(
    ! [E_90,F_91,A_92] : k2_xboole_0(k1_enumset1(E_90,E_90,F_91),k1_tarski(A_92)) = k2_enumset1(E_90,F_91,A_92,A_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_20])).

tff(c_262,plain,(
    ! [E_93,F_94,A_95] : k2_xboole_0(k2_tarski(E_93,F_94),k1_tarski(A_95)) = k2_enumset1(E_93,F_94,A_95,A_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_236])).

tff(c_291,plain,(
    ! [A_19,C_21] : k2_xboole_0(k2_tarski(A_19,A_19),k1_tarski(C_21)) = k1_enumset1(A_19,C_21,C_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_262])).

tff(c_364,plain,(
    ! [A_101,C_102] : k2_xboole_0(k1_tarski(A_101),k1_tarski(C_102)) = k1_enumset1(A_101,C_102,C_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_291])).

tff(c_386,plain,(
    ! [C_102] : k2_xboole_0(k1_tarski(C_102),k1_tarski(C_102)) = k2_tarski(C_102,C_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_16])).

tff(c_413,plain,(
    ! [C_103] : k2_xboole_0(k1_tarski(C_103),k1_tarski(C_103)) = k1_tarski(C_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_386])).

tff(c_294,plain,(
    ! [A_16,A_95] : k2_xboole_0(k1_tarski(A_16),k1_tarski(A_95)) = k2_enumset1(A_16,A_16,A_95,A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_262])).

tff(c_544,plain,(
    ! [C_113] : k2_enumset1(C_113,C_113,C_113,C_113) = k1_tarski(C_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_294])).

tff(c_180,plain,(
    ! [D_81,E_77,A_79,C_82,F_83] : k4_enumset1(C_82,D_81,E_77,F_83,A_79,A_79) = k2_xboole_0(k2_enumset1(C_82,D_81,E_77,F_83),k1_tarski(A_79)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_158])).

tff(c_984,plain,(
    ! [C_142,A_143] : k4_enumset1(C_142,C_142,C_142,C_142,A_143,A_143) = k2_xboole_0(k1_tarski(C_142),k1_tarski(A_143)) ),
    inference(superposition,[status(thm),theory(equality)],[c_544,c_180])).

tff(c_408,plain,(
    ! [C_102] : k2_xboole_0(k1_tarski(C_102),k1_tarski(C_102)) = k1_tarski(C_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_386])).

tff(c_1064,plain,(
    ! [A_144] : k4_enumset1(A_144,A_144,A_144,A_144,A_144,A_144) = k1_tarski(A_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_984,c_408])).

tff(c_8,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_136,plain,(
    ! [H_75,C_73,A_70,B_72,F_69,E_71,G_74,D_76] : k3_xboole_0(k4_enumset1(A_70,B_72,C_73,D_76,E_71,F_69),k6_enumset1(A_70,B_72,C_73,D_76,E_71,F_69,G_74,H_75)) = k4_enumset1(A_70,B_72,C_73,D_76,E_71,F_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_8])).

tff(c_1073,plain,(
    ! [A_144,G_74,H_75] : k3_xboole_0(k1_tarski(A_144),k6_enumset1(A_144,A_144,A_144,A_144,A_144,A_144,G_74,H_75)) = k4_enumset1(A_144,A_144,A_144,A_144,A_144,A_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_1064,c_136])).

tff(c_1143,plain,(
    ! [A_151,G_152,H_153] : k3_xboole_0(k1_tarski(A_151),k1_enumset1(A_151,G_152,H_153)) = k1_tarski(A_151) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_22,c_24,c_14,c_16,c_18,c_20,c_22,c_1073])).

tff(c_6,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1149,plain,(
    ! [A_151,G_152,H_153] : k5_xboole_0(k1_tarski(A_151),k1_tarski(A_151)) = k4_xboole_0(k1_tarski(A_151),k1_enumset1(A_151,G_152,H_153)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1143,c_6])).

tff(c_1168,plain,(
    ! [A_154,G_155,H_156] : k4_xboole_0(k1_tarski(A_154),k1_enumset1(A_154,G_155,H_156)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1149])).

tff(c_1181,plain,(
    ! [A_17,B_18] : k4_xboole_0(k1_tarski(A_17),k2_tarski(A_17,B_18)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1168])).

tff(c_52,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | k4_xboole_0(A_41,B_42) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_56,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52,c_26])).

tff(c_1188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1181,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:00:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.48  
% 3.19/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.48  %$ r1_tarski > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 3.19/1.48  
% 3.19/1.48  %Foreground sorts:
% 3.19/1.48  
% 3.19/1.48  
% 3.19/1.48  %Background operators:
% 3.19/1.48  
% 3.19/1.48  
% 3.19/1.48  %Foreground operators:
% 3.19/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.19/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.19/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.19/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.19/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.19/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.19/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.19/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.19/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.19/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.19/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.19/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.19/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.19/1.48  
% 3.19/1.49  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.19/1.49  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.19/1.49  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.19/1.49  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.19/1.49  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.19/1.49  tff(f_49, axiom, (![A, B, C, D, E, F]: (k6_enumset1(A, A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_enumset1)).
% 3.19/1.49  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.19/1.49  tff(f_37, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 3.19/1.49  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 3.19/1.49  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.19/1.49  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.19/1.49  tff(f_52, negated_conjecture, ~(![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 3.19/1.49  tff(c_16, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.19/1.49  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.19/1.49  tff(c_18, plain, (![A_19, B_20, C_21]: (k2_enumset1(A_19, A_19, B_20, C_21)=k1_enumset1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.19/1.49  tff(c_20, plain, (![A_22, B_23, C_24, D_25]: (k3_enumset1(A_22, A_22, B_23, C_24, D_25)=k2_enumset1(A_22, B_23, C_24, D_25))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.19/1.49  tff(c_22, plain, (![B_27, D_29, A_26, E_30, C_28]: (k4_enumset1(A_26, A_26, B_27, C_28, D_29, E_30)=k3_enumset1(A_26, B_27, C_28, D_29, E_30))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.19/1.49  tff(c_24, plain, (![A_31, C_33, B_32, F_36, E_35, D_34]: (k6_enumset1(A_31, A_31, A_31, B_32, C_33, D_34, E_35, F_36)=k4_enumset1(A_31, B_32, C_33, D_34, E_35, F_36))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.19/1.49  tff(c_14, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.19/1.49  tff(c_127, plain, (![H_75, C_73, A_70, B_72, F_69, E_71, G_74, D_76]: (k2_xboole_0(k4_enumset1(A_70, B_72, C_73, D_76, E_71, F_69), k2_tarski(G_74, H_75))=k6_enumset1(A_70, B_72, C_73, D_76, E_71, F_69, G_74, H_75))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.19/1.49  tff(c_148, plain, (![D_81, E_77, A_78, B_80, A_79, C_82, F_83]: (k6_enumset1(A_78, B_80, C_82, D_81, E_77, F_83, A_79, A_79)=k2_xboole_0(k4_enumset1(A_78, B_80, C_82, D_81, E_77, F_83), k1_tarski(A_79)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_127])).
% 3.19/1.49  tff(c_158, plain, (![D_81, E_77, A_79, C_82, F_83]: (k4_enumset1(C_82, D_81, E_77, F_83, A_79, A_79)=k2_xboole_0(k4_enumset1(C_82, C_82, C_82, D_81, E_77, F_83), k1_tarski(A_79)))), inference(superposition, [status(thm), theory('equality')], [c_148, c_24])).
% 3.19/1.49  tff(c_184, plain, (![A_85, E_88, C_84, D_86, F_87]: (k4_enumset1(C_84, D_86, E_88, F_87, A_85, A_85)=k2_xboole_0(k2_enumset1(C_84, D_86, E_88, F_87), k1_tarski(A_85)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_158])).
% 3.19/1.49  tff(c_200, plain, (![D_86, E_88, F_87, A_85]: (k3_enumset1(D_86, E_88, F_87, A_85, A_85)=k2_xboole_0(k2_enumset1(D_86, D_86, E_88, F_87), k1_tarski(A_85)))), inference(superposition, [status(thm), theory('equality')], [c_184, c_22])).
% 3.19/1.49  tff(c_226, plain, (![D_89, E_90, F_91, A_92]: (k3_enumset1(D_89, E_90, F_91, A_92, A_92)=k2_xboole_0(k1_enumset1(D_89, E_90, F_91), k1_tarski(A_92)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_200])).
% 3.19/1.49  tff(c_236, plain, (![E_90, F_91, A_92]: (k2_xboole_0(k1_enumset1(E_90, E_90, F_91), k1_tarski(A_92))=k2_enumset1(E_90, F_91, A_92, A_92))), inference(superposition, [status(thm), theory('equality')], [c_226, c_20])).
% 3.19/1.49  tff(c_262, plain, (![E_93, F_94, A_95]: (k2_xboole_0(k2_tarski(E_93, F_94), k1_tarski(A_95))=k2_enumset1(E_93, F_94, A_95, A_95))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_236])).
% 3.19/1.49  tff(c_291, plain, (![A_19, C_21]: (k2_xboole_0(k2_tarski(A_19, A_19), k1_tarski(C_21))=k1_enumset1(A_19, C_21, C_21))), inference(superposition, [status(thm), theory('equality')], [c_18, c_262])).
% 3.19/1.49  tff(c_364, plain, (![A_101, C_102]: (k2_xboole_0(k1_tarski(A_101), k1_tarski(C_102))=k1_enumset1(A_101, C_102, C_102))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_291])).
% 3.19/1.49  tff(c_386, plain, (![C_102]: (k2_xboole_0(k1_tarski(C_102), k1_tarski(C_102))=k2_tarski(C_102, C_102))), inference(superposition, [status(thm), theory('equality')], [c_364, c_16])).
% 3.19/1.49  tff(c_413, plain, (![C_103]: (k2_xboole_0(k1_tarski(C_103), k1_tarski(C_103))=k1_tarski(C_103))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_386])).
% 3.19/1.49  tff(c_294, plain, (![A_16, A_95]: (k2_xboole_0(k1_tarski(A_16), k1_tarski(A_95))=k2_enumset1(A_16, A_16, A_95, A_95))), inference(superposition, [status(thm), theory('equality')], [c_14, c_262])).
% 3.19/1.49  tff(c_544, plain, (![C_113]: (k2_enumset1(C_113, C_113, C_113, C_113)=k1_tarski(C_113))), inference(superposition, [status(thm), theory('equality')], [c_413, c_294])).
% 3.19/1.49  tff(c_180, plain, (![D_81, E_77, A_79, C_82, F_83]: (k4_enumset1(C_82, D_81, E_77, F_83, A_79, A_79)=k2_xboole_0(k2_enumset1(C_82, D_81, E_77, F_83), k1_tarski(A_79)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_158])).
% 3.19/1.49  tff(c_984, plain, (![C_142, A_143]: (k4_enumset1(C_142, C_142, C_142, C_142, A_143, A_143)=k2_xboole_0(k1_tarski(C_142), k1_tarski(A_143)))), inference(superposition, [status(thm), theory('equality')], [c_544, c_180])).
% 3.19/1.49  tff(c_408, plain, (![C_102]: (k2_xboole_0(k1_tarski(C_102), k1_tarski(C_102))=k1_tarski(C_102))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_386])).
% 3.19/1.49  tff(c_1064, plain, (![A_144]: (k4_enumset1(A_144, A_144, A_144, A_144, A_144, A_144)=k1_tarski(A_144))), inference(superposition, [status(thm), theory('equality')], [c_984, c_408])).
% 3.19/1.49  tff(c_8, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.19/1.49  tff(c_136, plain, (![H_75, C_73, A_70, B_72, F_69, E_71, G_74, D_76]: (k3_xboole_0(k4_enumset1(A_70, B_72, C_73, D_76, E_71, F_69), k6_enumset1(A_70, B_72, C_73, D_76, E_71, F_69, G_74, H_75))=k4_enumset1(A_70, B_72, C_73, D_76, E_71, F_69))), inference(superposition, [status(thm), theory('equality')], [c_127, c_8])).
% 3.19/1.49  tff(c_1073, plain, (![A_144, G_74, H_75]: (k3_xboole_0(k1_tarski(A_144), k6_enumset1(A_144, A_144, A_144, A_144, A_144, A_144, G_74, H_75))=k4_enumset1(A_144, A_144, A_144, A_144, A_144, A_144))), inference(superposition, [status(thm), theory('equality')], [c_1064, c_136])).
% 3.19/1.49  tff(c_1143, plain, (![A_151, G_152, H_153]: (k3_xboole_0(k1_tarski(A_151), k1_enumset1(A_151, G_152, H_153))=k1_tarski(A_151))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_22, c_24, c_14, c_16, c_18, c_20, c_22, c_1073])).
% 3.19/1.49  tff(c_6, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.19/1.49  tff(c_1149, plain, (![A_151, G_152, H_153]: (k5_xboole_0(k1_tarski(A_151), k1_tarski(A_151))=k4_xboole_0(k1_tarski(A_151), k1_enumset1(A_151, G_152, H_153)))), inference(superposition, [status(thm), theory('equality')], [c_1143, c_6])).
% 3.19/1.49  tff(c_1168, plain, (![A_154, G_155, H_156]: (k4_xboole_0(k1_tarski(A_154), k1_enumset1(A_154, G_155, H_156))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1149])).
% 3.19/1.49  tff(c_1181, plain, (![A_17, B_18]: (k4_xboole_0(k1_tarski(A_17), k2_tarski(A_17, B_18))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_1168])).
% 3.19/1.49  tff(c_52, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | k4_xboole_0(A_41, B_42)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.19/1.49  tff(c_26, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.19/1.49  tff(c_56, plain, (k4_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_52, c_26])).
% 3.19/1.49  tff(c_1188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1181, c_56])).
% 3.19/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.49  
% 3.19/1.49  Inference rules
% 3.19/1.49  ----------------------
% 3.19/1.49  #Ref     : 0
% 3.19/1.49  #Sup     : 286
% 3.19/1.49  #Fact    : 0
% 3.19/1.49  #Define  : 0
% 3.19/1.49  #Split   : 0
% 3.19/1.49  #Chain   : 0
% 3.19/1.49  #Close   : 0
% 3.19/1.49  
% 3.19/1.49  Ordering : KBO
% 3.19/1.49  
% 3.19/1.49  Simplification rules
% 3.19/1.49  ----------------------
% 3.19/1.49  #Subsume      : 19
% 3.19/1.49  #Demod        : 242
% 3.19/1.49  #Tautology    : 192
% 3.19/1.49  #SimpNegUnit  : 0
% 3.19/1.49  #BackRed      : 1
% 3.19/1.49  
% 3.19/1.49  #Partial instantiations: 0
% 3.19/1.49  #Strategies tried      : 1
% 3.19/1.49  
% 3.19/1.49  Timing (in seconds)
% 3.19/1.49  ----------------------
% 3.19/1.50  Preprocessing        : 0.31
% 3.19/1.50  Parsing              : 0.16
% 3.19/1.50  CNF conversion       : 0.02
% 3.19/1.50  Main loop            : 0.43
% 3.19/1.50  Inferencing          : 0.19
% 3.19/1.50  Reduction            : 0.16
% 3.19/1.50  Demodulation         : 0.13
% 3.19/1.50  BG Simplification    : 0.02
% 3.19/1.50  Subsumption          : 0.04
% 3.19/1.50  Abstraction          : 0.03
% 3.19/1.50  MUC search           : 0.00
% 3.19/1.50  Cooper               : 0.00
% 3.19/1.50  Total                : 0.77
% 3.19/1.50  Index Insertion      : 0.00
% 3.19/1.50  Index Deletion       : 0.00
% 3.19/1.50  Index Matching       : 0.00
% 3.19/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
