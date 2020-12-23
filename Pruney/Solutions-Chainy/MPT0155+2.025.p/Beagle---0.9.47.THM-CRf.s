%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:12 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   60 (  93 expanded)
%              Number of leaves         :   25 (  42 expanded)
%              Depth                    :   16
%              Number of atoms          :   44 (  77 expanded)
%              Number of equality atoms :   43 (  76 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_6,plain,(
    ! [A_9,B_10,C_11] : k2_xboole_0(k2_tarski(A_9,B_10),k1_tarski(C_11)) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_55,B_56] : k1_enumset1(A_55,A_55,B_56) = k2_tarski(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_21,B_22,D_24,C_23,E_25] : k2_xboole_0(k2_tarski(A_21,B_22),k1_enumset1(C_23,D_24,E_25)) = k3_enumset1(A_21,B_22,C_23,D_24,E_25) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_337,plain,(
    ! [A_108,B_110,E_105,F_107,C_109,D_106] : k2_xboole_0(k1_enumset1(A_108,B_110,C_109),k1_enumset1(D_106,E_105,F_107)) = k4_enumset1(A_108,B_110,C_109,D_106,E_105,F_107) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_346,plain,(
    ! [B_56,E_105,F_107,A_55,D_106] : k4_enumset1(A_55,A_55,B_56,D_106,E_105,F_107) = k2_xboole_0(k2_tarski(A_55,B_56),k1_enumset1(D_106,E_105,F_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_337])).

tff(c_943,plain,(
    ! [F_166,A_165,E_163,B_162,D_164] : k4_enumset1(A_165,A_165,B_162,D_164,E_163,F_166) = k3_enumset1(A_165,B_162,D_164,E_163,F_166) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_346])).

tff(c_22,plain,(
    ! [A_54] : k2_tarski(A_54,A_54) = k1_tarski(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_54,plain,(
    ! [A_62,B_63,C_64] : k2_xboole_0(k2_tarski(A_62,B_63),k1_tarski(C_64)) = k1_enumset1(A_62,B_63,C_64) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [A_54,C_64] : k2_xboole_0(k1_tarski(A_54),k1_tarski(C_64)) = k1_enumset1(A_54,A_54,C_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_54])).

tff(c_66,plain,(
    ! [A_54,C_64] : k2_xboole_0(k1_tarski(A_54),k1_tarski(C_64)) = k2_tarski(A_54,C_64) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_63])).

tff(c_67,plain,(
    ! [A_65,B_66,C_67,D_68] : k2_xboole_0(k1_tarski(A_65),k1_enumset1(B_66,C_67,D_68)) = k2_enumset1(A_65,B_66,C_67,D_68) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_88,plain,(
    ! [A_71,A_72,B_73] : k2_xboole_0(k1_tarski(A_71),k2_tarski(A_72,B_73)) = k2_enumset1(A_71,A_72,A_72,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_67])).

tff(c_103,plain,(
    ! [A_71,A_54] : k2_xboole_0(k1_tarski(A_71),k1_tarski(A_54)) = k2_enumset1(A_71,A_54,A_54,A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_88])).

tff(c_108,plain,(
    ! [A_71,A_54] : k2_enumset1(A_71,A_54,A_54,A_54) = k2_tarski(A_71,A_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_103])).

tff(c_127,plain,(
    ! [C_80,E_77,D_79,A_78,B_76] : k2_xboole_0(k1_tarski(A_78),k2_enumset1(B_76,C_80,D_79,E_77)) = k3_enumset1(A_78,B_76,C_80,D_79,E_77) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_142,plain,(
    ! [A_81,A_82,A_83] : k3_enumset1(A_81,A_82,A_83,A_83,A_83) = k2_xboole_0(k1_tarski(A_81),k2_tarski(A_82,A_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_127])).

tff(c_163,plain,(
    ! [A_81,A_54] : k3_enumset1(A_81,A_54,A_54,A_54,A_54) = k2_xboole_0(k1_tarski(A_81),k1_tarski(A_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_142])).

tff(c_168,plain,(
    ! [A_81,A_54] : k3_enumset1(A_81,A_54,A_54,A_54,A_54) = k2_tarski(A_81,A_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_163])).

tff(c_244,plain,(
    ! [A_98,E_94,F_96,D_99,B_95,C_97] : k2_xboole_0(k3_enumset1(A_98,B_95,C_97,D_99,E_94),k1_tarski(F_96)) = k4_enumset1(A_98,B_95,C_97,D_99,E_94,F_96) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_256,plain,(
    ! [A_81,A_54,F_96] : k4_enumset1(A_81,A_54,A_54,A_54,A_54,F_96) = k2_xboole_0(k2_tarski(A_81,A_54),k1_tarski(F_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_244])).

tff(c_262,plain,(
    ! [A_81,A_54,F_96] : k4_enumset1(A_81,A_54,A_54,A_54,A_54,F_96) = k1_enumset1(A_81,A_54,F_96) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_256])).

tff(c_958,plain,(
    ! [E_163,F_166] : k3_enumset1(E_163,E_163,E_163,E_163,F_166) = k1_enumset1(E_163,E_163,F_166) ),
    inference(superposition,[status(thm),theory(equality)],[c_943,c_262])).

tff(c_982,plain,(
    ! [E_167,F_168] : k3_enumset1(E_167,E_167,E_167,E_167,F_168) = k2_tarski(E_167,F_168) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_958])).

tff(c_16,plain,(
    ! [B_33,C_34,E_36,F_37,A_32,D_35] : k2_xboole_0(k3_enumset1(A_32,B_33,C_34,D_35,E_36),k1_tarski(F_37)) = k4_enumset1(A_32,B_33,C_34,D_35,E_36,F_37) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1002,plain,(
    ! [E_167,F_168,F_37] : k4_enumset1(E_167,E_167,E_167,E_167,F_168,F_37) = k2_xboole_0(k2_tarski(E_167,F_168),k1_tarski(F_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_982,c_16])).

tff(c_1481,plain,(
    ! [E_188,F_189,F_190] : k4_enumset1(E_188,E_188,E_188,E_188,F_189,F_190) = k1_enumset1(E_188,F_189,F_190) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1002])).

tff(c_352,plain,(
    ! [B_56,E_105,F_107,A_55,D_106] : k4_enumset1(A_55,A_55,B_56,D_106,E_105,F_107) = k3_enumset1(A_55,B_56,D_106,E_105,F_107) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_346])).

tff(c_1531,plain,(
    ! [E_191,F_192,F_193] : k3_enumset1(E_191,E_191,E_191,F_192,F_193) = k1_enumset1(E_191,F_192,F_193) ),
    inference(superposition,[status(thm),theory(equality)],[c_1481,c_352])).

tff(c_8,plain,(
    ! [A_12,B_13,C_14,D_15] : k2_xboole_0(k1_tarski(A_12),k1_enumset1(B_13,C_14,D_15)) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_228,plain,(
    ! [B_92,C_91,A_89,E_93,D_90] : k2_xboole_0(k2_tarski(A_89,B_92),k1_enumset1(C_91,D_90,E_93)) = k3_enumset1(A_89,B_92,C_91,D_90,E_93) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_240,plain,(
    ! [A_54,C_91,D_90,E_93] : k3_enumset1(A_54,A_54,C_91,D_90,E_93) = k2_xboole_0(k1_tarski(A_54),k1_enumset1(C_91,D_90,E_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_228])).

tff(c_243,plain,(
    ! [A_54,C_91,D_90,E_93] : k3_enumset1(A_54,A_54,C_91,D_90,E_93) = k2_enumset1(A_54,C_91,D_90,E_93) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_240])).

tff(c_1560,plain,(
    ! [E_191,F_192,F_193] : k2_enumset1(E_191,E_191,F_192,F_193) = k1_enumset1(E_191,F_192,F_193) ),
    inference(superposition,[status(thm),theory(equality)],[c_1531,c_243])).

tff(c_26,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1560,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:57:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.46  
% 3.10/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.46  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.10/1.46  
% 3.10/1.46  %Foreground sorts:
% 3.10/1.46  
% 3.10/1.46  
% 3.10/1.46  %Background operators:
% 3.10/1.46  
% 3.10/1.46  
% 3.10/1.46  %Foreground operators:
% 3.10/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.10/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.10/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.10/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.10/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.10/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.10/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.10/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.10/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.10/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.10/1.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.10/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.10/1.46  
% 3.23/1.48  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 3.23/1.48  tff(f_49, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.23/1.48  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 3.23/1.48  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 3.23/1.48  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.23/1.48  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 3.23/1.48  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 3.23/1.48  tff(f_41, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 3.23/1.48  tff(f_52, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.23/1.48  tff(c_6, plain, (![A_9, B_10, C_11]: (k2_xboole_0(k2_tarski(A_9, B_10), k1_tarski(C_11))=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.48  tff(c_24, plain, (![A_55, B_56]: (k1_enumset1(A_55, A_55, B_56)=k2_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.23/1.48  tff(c_12, plain, (![A_21, B_22, D_24, C_23, E_25]: (k2_xboole_0(k2_tarski(A_21, B_22), k1_enumset1(C_23, D_24, E_25))=k3_enumset1(A_21, B_22, C_23, D_24, E_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.23/1.48  tff(c_337, plain, (![A_108, B_110, E_105, F_107, C_109, D_106]: (k2_xboole_0(k1_enumset1(A_108, B_110, C_109), k1_enumset1(D_106, E_105, F_107))=k4_enumset1(A_108, B_110, C_109, D_106, E_105, F_107))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.23/1.48  tff(c_346, plain, (![B_56, E_105, F_107, A_55, D_106]: (k4_enumset1(A_55, A_55, B_56, D_106, E_105, F_107)=k2_xboole_0(k2_tarski(A_55, B_56), k1_enumset1(D_106, E_105, F_107)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_337])).
% 3.23/1.48  tff(c_943, plain, (![F_166, A_165, E_163, B_162, D_164]: (k4_enumset1(A_165, A_165, B_162, D_164, E_163, F_166)=k3_enumset1(A_165, B_162, D_164, E_163, F_166))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_346])).
% 3.23/1.48  tff(c_22, plain, (![A_54]: (k2_tarski(A_54, A_54)=k1_tarski(A_54))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.23/1.48  tff(c_54, plain, (![A_62, B_63, C_64]: (k2_xboole_0(k2_tarski(A_62, B_63), k1_tarski(C_64))=k1_enumset1(A_62, B_63, C_64))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.48  tff(c_63, plain, (![A_54, C_64]: (k2_xboole_0(k1_tarski(A_54), k1_tarski(C_64))=k1_enumset1(A_54, A_54, C_64))), inference(superposition, [status(thm), theory('equality')], [c_22, c_54])).
% 3.23/1.48  tff(c_66, plain, (![A_54, C_64]: (k2_xboole_0(k1_tarski(A_54), k1_tarski(C_64))=k2_tarski(A_54, C_64))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_63])).
% 3.23/1.48  tff(c_67, plain, (![A_65, B_66, C_67, D_68]: (k2_xboole_0(k1_tarski(A_65), k1_enumset1(B_66, C_67, D_68))=k2_enumset1(A_65, B_66, C_67, D_68))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.23/1.48  tff(c_88, plain, (![A_71, A_72, B_73]: (k2_xboole_0(k1_tarski(A_71), k2_tarski(A_72, B_73))=k2_enumset1(A_71, A_72, A_72, B_73))), inference(superposition, [status(thm), theory('equality')], [c_24, c_67])).
% 3.23/1.48  tff(c_103, plain, (![A_71, A_54]: (k2_xboole_0(k1_tarski(A_71), k1_tarski(A_54))=k2_enumset1(A_71, A_54, A_54, A_54))), inference(superposition, [status(thm), theory('equality')], [c_22, c_88])).
% 3.23/1.48  tff(c_108, plain, (![A_71, A_54]: (k2_enumset1(A_71, A_54, A_54, A_54)=k2_tarski(A_71, A_54))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_103])).
% 3.23/1.48  tff(c_127, plain, (![C_80, E_77, D_79, A_78, B_76]: (k2_xboole_0(k1_tarski(A_78), k2_enumset1(B_76, C_80, D_79, E_77))=k3_enumset1(A_78, B_76, C_80, D_79, E_77))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.23/1.48  tff(c_142, plain, (![A_81, A_82, A_83]: (k3_enumset1(A_81, A_82, A_83, A_83, A_83)=k2_xboole_0(k1_tarski(A_81), k2_tarski(A_82, A_83)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_127])).
% 3.23/1.48  tff(c_163, plain, (![A_81, A_54]: (k3_enumset1(A_81, A_54, A_54, A_54, A_54)=k2_xboole_0(k1_tarski(A_81), k1_tarski(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_142])).
% 3.23/1.48  tff(c_168, plain, (![A_81, A_54]: (k3_enumset1(A_81, A_54, A_54, A_54, A_54)=k2_tarski(A_81, A_54))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_163])).
% 3.23/1.48  tff(c_244, plain, (![A_98, E_94, F_96, D_99, B_95, C_97]: (k2_xboole_0(k3_enumset1(A_98, B_95, C_97, D_99, E_94), k1_tarski(F_96))=k4_enumset1(A_98, B_95, C_97, D_99, E_94, F_96))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.23/1.48  tff(c_256, plain, (![A_81, A_54, F_96]: (k4_enumset1(A_81, A_54, A_54, A_54, A_54, F_96)=k2_xboole_0(k2_tarski(A_81, A_54), k1_tarski(F_96)))), inference(superposition, [status(thm), theory('equality')], [c_168, c_244])).
% 3.23/1.48  tff(c_262, plain, (![A_81, A_54, F_96]: (k4_enumset1(A_81, A_54, A_54, A_54, A_54, F_96)=k1_enumset1(A_81, A_54, F_96))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_256])).
% 3.23/1.48  tff(c_958, plain, (![E_163, F_166]: (k3_enumset1(E_163, E_163, E_163, E_163, F_166)=k1_enumset1(E_163, E_163, F_166))), inference(superposition, [status(thm), theory('equality')], [c_943, c_262])).
% 3.23/1.48  tff(c_982, plain, (![E_167, F_168]: (k3_enumset1(E_167, E_167, E_167, E_167, F_168)=k2_tarski(E_167, F_168))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_958])).
% 3.23/1.48  tff(c_16, plain, (![B_33, C_34, E_36, F_37, A_32, D_35]: (k2_xboole_0(k3_enumset1(A_32, B_33, C_34, D_35, E_36), k1_tarski(F_37))=k4_enumset1(A_32, B_33, C_34, D_35, E_36, F_37))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.23/1.48  tff(c_1002, plain, (![E_167, F_168, F_37]: (k4_enumset1(E_167, E_167, E_167, E_167, F_168, F_37)=k2_xboole_0(k2_tarski(E_167, F_168), k1_tarski(F_37)))), inference(superposition, [status(thm), theory('equality')], [c_982, c_16])).
% 3.23/1.48  tff(c_1481, plain, (![E_188, F_189, F_190]: (k4_enumset1(E_188, E_188, E_188, E_188, F_189, F_190)=k1_enumset1(E_188, F_189, F_190))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1002])).
% 3.23/1.48  tff(c_352, plain, (![B_56, E_105, F_107, A_55, D_106]: (k4_enumset1(A_55, A_55, B_56, D_106, E_105, F_107)=k3_enumset1(A_55, B_56, D_106, E_105, F_107))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_346])).
% 3.23/1.48  tff(c_1531, plain, (![E_191, F_192, F_193]: (k3_enumset1(E_191, E_191, E_191, F_192, F_193)=k1_enumset1(E_191, F_192, F_193))), inference(superposition, [status(thm), theory('equality')], [c_1481, c_352])).
% 3.23/1.48  tff(c_8, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k1_tarski(A_12), k1_enumset1(B_13, C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.23/1.48  tff(c_228, plain, (![B_92, C_91, A_89, E_93, D_90]: (k2_xboole_0(k2_tarski(A_89, B_92), k1_enumset1(C_91, D_90, E_93))=k3_enumset1(A_89, B_92, C_91, D_90, E_93))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.23/1.48  tff(c_240, plain, (![A_54, C_91, D_90, E_93]: (k3_enumset1(A_54, A_54, C_91, D_90, E_93)=k2_xboole_0(k1_tarski(A_54), k1_enumset1(C_91, D_90, E_93)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_228])).
% 3.23/1.48  tff(c_243, plain, (![A_54, C_91, D_90, E_93]: (k3_enumset1(A_54, A_54, C_91, D_90, E_93)=k2_enumset1(A_54, C_91, D_90, E_93))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_240])).
% 3.23/1.48  tff(c_1560, plain, (![E_191, F_192, F_193]: (k2_enumset1(E_191, E_191, F_192, F_193)=k1_enumset1(E_191, F_192, F_193))), inference(superposition, [status(thm), theory('equality')], [c_1531, c_243])).
% 3.23/1.48  tff(c_26, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.23/1.48  tff(c_1615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1560, c_26])).
% 3.23/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.48  
% 3.23/1.48  Inference rules
% 3.23/1.48  ----------------------
% 3.23/1.48  #Ref     : 0
% 3.23/1.48  #Sup     : 365
% 3.23/1.48  #Fact    : 0
% 3.23/1.48  #Define  : 0
% 3.23/1.48  #Split   : 0
% 3.23/1.48  #Chain   : 0
% 3.23/1.48  #Close   : 0
% 3.23/1.48  
% 3.23/1.48  Ordering : KBO
% 3.23/1.48  
% 3.23/1.48  Simplification rules
% 3.23/1.48  ----------------------
% 3.23/1.48  #Subsume      : 14
% 3.23/1.48  #Demod        : 335
% 3.23/1.48  #Tautology    : 268
% 3.23/1.48  #SimpNegUnit  : 0
% 3.23/1.48  #BackRed      : 7
% 3.23/1.48  
% 3.23/1.48  #Partial instantiations: 0
% 3.23/1.48  #Strategies tried      : 1
% 3.23/1.48  
% 3.23/1.48  Timing (in seconds)
% 3.23/1.48  ----------------------
% 3.23/1.48  Preprocessing        : 0.30
% 3.23/1.48  Parsing              : 0.16
% 3.23/1.48  CNF conversion       : 0.02
% 3.23/1.48  Main loop            : 0.42
% 3.23/1.48  Inferencing          : 0.17
% 3.23/1.48  Reduction            : 0.16
% 3.23/1.48  Demodulation         : 0.13
% 3.23/1.48  BG Simplification    : 0.03
% 3.23/1.48  Subsumption          : 0.04
% 3.23/1.48  Abstraction          : 0.03
% 3.23/1.48  MUC search           : 0.00
% 3.23/1.48  Cooper               : 0.00
% 3.23/1.48  Total                : 0.75
% 3.23/1.48  Index Insertion      : 0.00
% 3.23/1.48  Index Deletion       : 0.00
% 3.23/1.48  Index Matching       : 0.00
% 3.23/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
