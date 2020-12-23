%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:48 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   62 (  99 expanded)
%              Number of leaves         :   28 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   42 (  79 expanded)
%              Number of equality atoms :   41 (  78 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_40,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_42,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

tff(c_20,plain,(
    ! [E_22,G_24,D_21,F_23,A_18,C_20,B_19] : k2_xboole_0(k2_enumset1(A_18,B_19,C_20,D_21),k1_enumset1(E_22,F_23,G_24)) = k5_enumset1(A_18,B_19,C_20,D_21,E_22,F_23,G_24) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [A_25,B_26] : k2_xboole_0(k1_tarski(A_25),k1_tarski(B_26)) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_54,plain,(
    ! [A_43,B_44,C_45] : k2_xboole_0(k2_xboole_0(A_43,B_44),C_45) = k2_xboole_0(A_43,k2_xboole_0(B_44,C_45)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    ! [A_25,B_26,C_45] : k2_xboole_0(k1_tarski(A_25),k2_xboole_0(k1_tarski(B_26),C_45)) = k2_xboole_0(k2_tarski(A_25,B_26),C_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_54])).

tff(c_18,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] : k2_xboole_0(k1_enumset1(A_13,B_14,C_15),k2_tarski(D_16,E_17)) = k3_enumset1(A_13,B_14,C_15,D_16,E_17) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [A_9,B_10,C_11,D_12] : k2_xboole_0(k2_tarski(A_9,B_10),k2_tarski(C_11,D_12)) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_24,plain,(
    ! [A_27,B_28,C_29] : k2_xboole_0(k1_tarski(A_27),k2_tarski(B_28,C_29)) = k1_enumset1(A_27,B_28,C_29) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_204,plain,(
    ! [A_80,B_81,C_82,C_83] : k2_xboole_0(k1_tarski(A_80),k2_xboole_0(k2_tarski(B_81,C_82),C_83)) = k2_xboole_0(k1_enumset1(A_80,B_81,C_82),C_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_54])).

tff(c_222,plain,(
    ! [C_11,B_10,A_80,D_12,A_9] : k2_xboole_0(k1_enumset1(A_80,A_9,B_10),k2_tarski(C_11,D_12)) = k2_xboole_0(k1_tarski(A_80),k2_enumset1(A_9,B_10,C_11,D_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_204])).

tff(c_252,plain,(
    ! [A_95,A_99,C_97,B_96,D_98] : k2_xboole_0(k1_tarski(A_95),k2_enumset1(A_99,B_96,C_97,D_98)) = k3_enumset1(A_95,A_99,B_96,C_97,D_98) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_222])).

tff(c_258,plain,(
    ! [A_95,A_25,A_99,C_97,B_96,D_98] : k2_xboole_0(k2_tarski(A_25,A_95),k2_enumset1(A_99,B_96,C_97,D_98)) = k2_xboole_0(k1_tarski(A_25),k3_enumset1(A_95,A_99,B_96,C_97,D_98)) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_72])).

tff(c_78,plain,(
    ! [A_48,B_49,C_50,D_51] : k2_xboole_0(k2_tarski(A_48,B_49),k2_tarski(C_50,D_51)) = k2_enumset1(A_48,B_49,C_50,D_51) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_318,plain,(
    ! [D_109,B_110,A_111,C_112,C_113] : k2_xboole_0(k2_tarski(A_111,B_110),k2_xboole_0(k2_tarski(C_112,D_109),C_113)) = k2_xboole_0(k2_enumset1(A_111,B_110,C_112,D_109),C_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_2])).

tff(c_348,plain,(
    ! [C_11,B_110,A_111,B_10,D_12,A_9] : k2_xboole_0(k2_enumset1(A_111,B_110,A_9,B_10),k2_tarski(C_11,D_12)) = k2_xboole_0(k2_tarski(A_111,B_110),k2_enumset1(A_9,B_10,C_11,D_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_318])).

tff(c_169,plain,(
    ! [D_77,C_73,B_74,E_76,A_75] : k2_xboole_0(k2_enumset1(A_75,B_74,C_73,D_77),k1_tarski(E_76)) = k3_enumset1(A_75,B_74,C_73,D_77,E_76) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_355,plain,(
    ! [E_121,D_116,B_118,A_117,C_119,C_120] : k2_xboole_0(k2_enumset1(A_117,B_118,C_119,D_116),k2_xboole_0(k1_tarski(E_121),C_120)) = k2_xboole_0(k3_enumset1(A_117,B_118,C_119,D_116,E_121),C_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_2])).

tff(c_382,plain,(
    ! [D_116,B_118,A_25,A_117,C_119,B_26] : k2_xboole_0(k3_enumset1(A_117,B_118,C_119,D_116,A_25),k1_tarski(B_26)) = k2_xboole_0(k2_enumset1(A_117,B_118,C_119,D_116),k2_tarski(A_25,B_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_355])).

tff(c_505,plain,(
    ! [D_116,B_118,A_25,A_117,C_119,B_26] : k2_xboole_0(k3_enumset1(A_117,B_118,C_119,D_116,A_25),k1_tarski(B_26)) = k2_xboole_0(k2_tarski(A_117,B_118),k2_enumset1(C_119,D_116,A_25,B_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_382])).

tff(c_97,plain,(
    ! [A_56,B_57,C_58] : k2_xboole_0(k1_tarski(A_56),k2_xboole_0(k1_tarski(B_57),C_58)) = k2_xboole_0(k2_tarski(A_56,B_57),C_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_54])).

tff(c_118,plain,(
    ! [A_56,A_25,B_26] : k2_xboole_0(k2_tarski(A_56,A_25),k1_tarski(B_26)) = k2_xboole_0(k1_tarski(A_56),k2_tarski(A_25,B_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_97])).

tff(c_123,plain,(
    ! [A_56,A_25,B_26] : k2_xboole_0(k2_tarski(A_56,A_25),k1_tarski(B_26)) = k1_enumset1(A_56,A_25,B_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_118])).

tff(c_157,plain,(
    ! [E_70,C_72,D_68,B_69,A_71] : k2_xboole_0(k1_enumset1(A_71,B_69,C_72),k2_tarski(D_68,E_70)) = k3_enumset1(A_71,B_69,C_72,D_68,E_70) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_460,plain,(
    ! [B_133,C_136,E_137,D_132,C_134,A_135] : k2_xboole_0(k1_enumset1(A_135,B_133,C_134),k2_xboole_0(k2_tarski(D_132,E_137),C_136)) = k2_xboole_0(k3_enumset1(A_135,B_133,C_134,D_132,E_137),C_136) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_2])).

tff(c_484,plain,(
    ! [B_133,A_25,A_56,C_134,B_26,A_135] : k2_xboole_0(k3_enumset1(A_135,B_133,C_134,A_56,A_25),k1_tarski(B_26)) = k2_xboole_0(k1_enumset1(A_135,B_133,C_134),k1_enumset1(A_56,A_25,B_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_460])).

tff(c_597,plain,(
    ! [B_133,A_25,A_56,C_134,B_26,A_135] : k2_xboole_0(k1_enumset1(A_135,B_133,C_134),k1_enumset1(A_56,A_25,B_26)) = k2_xboole_0(k2_tarski(A_135,B_133),k2_enumset1(C_134,A_56,A_25,B_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_484])).

tff(c_663,plain,(
    ! [C_190,B_191,A_194,A_192,A_189,B_193] : k2_xboole_0(k1_enumset1(A_192,B_191,C_190),k1_enumset1(A_194,A_189,B_193)) = k2_xboole_0(k1_tarski(A_192),k3_enumset1(B_191,C_190,A_194,A_189,B_193)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_597])).

tff(c_115,plain,(
    ! [A_56,A_27,B_28,C_29] : k2_xboole_0(k2_tarski(A_56,A_27),k2_tarski(B_28,C_29)) = k2_xboole_0(k1_tarski(A_56),k1_enumset1(A_27,B_28,C_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_97])).

tff(c_136,plain,(
    ! [A_62,A_63,B_64,C_65] : k2_xboole_0(k1_tarski(A_62),k1_enumset1(A_63,B_64,C_65)) = k2_enumset1(A_62,A_63,B_64,C_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_115])).

tff(c_145,plain,(
    ! [C_3,B_64,C_65,A_63,A_62] : k2_xboole_0(k1_tarski(A_62),k2_xboole_0(k1_enumset1(A_63,B_64,C_65),C_3)) = k2_xboole_0(k2_enumset1(A_62,A_63,B_64,C_65),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_2])).

tff(c_672,plain,(
    ! [C_190,B_191,A_194,A_192,A_62,A_189,B_193] : k2_xboole_0(k1_tarski(A_62),k2_xboole_0(k1_tarski(A_192),k3_enumset1(B_191,C_190,A_194,A_189,B_193))) = k2_xboole_0(k2_enumset1(A_62,A_192,B_191,C_190),k1_enumset1(A_194,A_189,B_193)) ),
    inference(superposition,[status(thm),theory(equality)],[c_663,c_145])).

tff(c_681,plain,(
    ! [C_190,B_191,A_194,A_192,A_62,A_189,B_193] : k2_xboole_0(k2_tarski(A_62,A_192),k3_enumset1(B_191,C_190,A_194,A_189,B_193)) = k5_enumset1(A_62,A_192,B_191,C_190,A_194,A_189,B_193) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_72,c_672])).

tff(c_28,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),k3_enumset1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')) != k5_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_720,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n017.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 17:34:31 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.32  
% 2.86/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.33  %$ r2_hidden > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 2.86/1.33  
% 2.86/1.33  %Foreground sorts:
% 2.86/1.33  
% 2.86/1.33  
% 2.86/1.33  %Background operators:
% 2.86/1.33  
% 2.86/1.33  
% 2.86/1.33  %Foreground operators:
% 2.86/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.86/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.86/1.33  tff('#skF_7', type, '#skF_7': $i).
% 2.86/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.86/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.86/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.86/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.86/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.86/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.33  tff('#skF_9', type, '#skF_9': $i).
% 2.86/1.33  tff('#skF_8', type, '#skF_8': $i).
% 2.86/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.86/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.86/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.86/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.86/1.33  
% 2.86/1.34  tff(f_40, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 2.86/1.34  tff(f_42, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.86/1.34  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.86/1.34  tff(f_38, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 2.86/1.34  tff(f_36, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 2.86/1.34  tff(f_44, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.86/1.34  tff(f_46, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 2.86/1.34  tff(f_49, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_enumset1)).
% 2.86/1.34  tff(c_20, plain, (![E_22, G_24, D_21, F_23, A_18, C_20, B_19]: (k2_xboole_0(k2_enumset1(A_18, B_19, C_20, D_21), k1_enumset1(E_22, F_23, G_24))=k5_enumset1(A_18, B_19, C_20, D_21, E_22, F_23, G_24))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.86/1.34  tff(c_22, plain, (![A_25, B_26]: (k2_xboole_0(k1_tarski(A_25), k1_tarski(B_26))=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.86/1.34  tff(c_54, plain, (![A_43, B_44, C_45]: (k2_xboole_0(k2_xboole_0(A_43, B_44), C_45)=k2_xboole_0(A_43, k2_xboole_0(B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.86/1.34  tff(c_72, plain, (![A_25, B_26, C_45]: (k2_xboole_0(k1_tarski(A_25), k2_xboole_0(k1_tarski(B_26), C_45))=k2_xboole_0(k2_tarski(A_25, B_26), C_45))), inference(superposition, [status(thm), theory('equality')], [c_22, c_54])).
% 2.86/1.34  tff(c_18, plain, (![E_17, A_13, B_14, C_15, D_16]: (k2_xboole_0(k1_enumset1(A_13, B_14, C_15), k2_tarski(D_16, E_17))=k3_enumset1(A_13, B_14, C_15, D_16, E_17))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.86/1.34  tff(c_16, plain, (![A_9, B_10, C_11, D_12]: (k2_xboole_0(k2_tarski(A_9, B_10), k2_tarski(C_11, D_12))=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.86/1.34  tff(c_24, plain, (![A_27, B_28, C_29]: (k2_xboole_0(k1_tarski(A_27), k2_tarski(B_28, C_29))=k1_enumset1(A_27, B_28, C_29))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.86/1.34  tff(c_204, plain, (![A_80, B_81, C_82, C_83]: (k2_xboole_0(k1_tarski(A_80), k2_xboole_0(k2_tarski(B_81, C_82), C_83))=k2_xboole_0(k1_enumset1(A_80, B_81, C_82), C_83))), inference(superposition, [status(thm), theory('equality')], [c_24, c_54])).
% 2.86/1.34  tff(c_222, plain, (![C_11, B_10, A_80, D_12, A_9]: (k2_xboole_0(k1_enumset1(A_80, A_9, B_10), k2_tarski(C_11, D_12))=k2_xboole_0(k1_tarski(A_80), k2_enumset1(A_9, B_10, C_11, D_12)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_204])).
% 2.86/1.34  tff(c_252, plain, (![A_95, A_99, C_97, B_96, D_98]: (k2_xboole_0(k1_tarski(A_95), k2_enumset1(A_99, B_96, C_97, D_98))=k3_enumset1(A_95, A_99, B_96, C_97, D_98))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_222])).
% 2.86/1.34  tff(c_258, plain, (![A_95, A_25, A_99, C_97, B_96, D_98]: (k2_xboole_0(k2_tarski(A_25, A_95), k2_enumset1(A_99, B_96, C_97, D_98))=k2_xboole_0(k1_tarski(A_25), k3_enumset1(A_95, A_99, B_96, C_97, D_98)))), inference(superposition, [status(thm), theory('equality')], [c_252, c_72])).
% 2.86/1.34  tff(c_78, plain, (![A_48, B_49, C_50, D_51]: (k2_xboole_0(k2_tarski(A_48, B_49), k2_tarski(C_50, D_51))=k2_enumset1(A_48, B_49, C_50, D_51))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.86/1.34  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.86/1.34  tff(c_318, plain, (![D_109, B_110, A_111, C_112, C_113]: (k2_xboole_0(k2_tarski(A_111, B_110), k2_xboole_0(k2_tarski(C_112, D_109), C_113))=k2_xboole_0(k2_enumset1(A_111, B_110, C_112, D_109), C_113))), inference(superposition, [status(thm), theory('equality')], [c_78, c_2])).
% 2.86/1.34  tff(c_348, plain, (![C_11, B_110, A_111, B_10, D_12, A_9]: (k2_xboole_0(k2_enumset1(A_111, B_110, A_9, B_10), k2_tarski(C_11, D_12))=k2_xboole_0(k2_tarski(A_111, B_110), k2_enumset1(A_9, B_10, C_11, D_12)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_318])).
% 2.86/1.34  tff(c_169, plain, (![D_77, C_73, B_74, E_76, A_75]: (k2_xboole_0(k2_enumset1(A_75, B_74, C_73, D_77), k1_tarski(E_76))=k3_enumset1(A_75, B_74, C_73, D_77, E_76))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.86/1.34  tff(c_355, plain, (![E_121, D_116, B_118, A_117, C_119, C_120]: (k2_xboole_0(k2_enumset1(A_117, B_118, C_119, D_116), k2_xboole_0(k1_tarski(E_121), C_120))=k2_xboole_0(k3_enumset1(A_117, B_118, C_119, D_116, E_121), C_120))), inference(superposition, [status(thm), theory('equality')], [c_169, c_2])).
% 2.86/1.34  tff(c_382, plain, (![D_116, B_118, A_25, A_117, C_119, B_26]: (k2_xboole_0(k3_enumset1(A_117, B_118, C_119, D_116, A_25), k1_tarski(B_26))=k2_xboole_0(k2_enumset1(A_117, B_118, C_119, D_116), k2_tarski(A_25, B_26)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_355])).
% 2.86/1.34  tff(c_505, plain, (![D_116, B_118, A_25, A_117, C_119, B_26]: (k2_xboole_0(k3_enumset1(A_117, B_118, C_119, D_116, A_25), k1_tarski(B_26))=k2_xboole_0(k2_tarski(A_117, B_118), k2_enumset1(C_119, D_116, A_25, B_26)))), inference(demodulation, [status(thm), theory('equality')], [c_348, c_382])).
% 2.86/1.34  tff(c_97, plain, (![A_56, B_57, C_58]: (k2_xboole_0(k1_tarski(A_56), k2_xboole_0(k1_tarski(B_57), C_58))=k2_xboole_0(k2_tarski(A_56, B_57), C_58))), inference(superposition, [status(thm), theory('equality')], [c_22, c_54])).
% 2.86/1.34  tff(c_118, plain, (![A_56, A_25, B_26]: (k2_xboole_0(k2_tarski(A_56, A_25), k1_tarski(B_26))=k2_xboole_0(k1_tarski(A_56), k2_tarski(A_25, B_26)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_97])).
% 2.86/1.34  tff(c_123, plain, (![A_56, A_25, B_26]: (k2_xboole_0(k2_tarski(A_56, A_25), k1_tarski(B_26))=k1_enumset1(A_56, A_25, B_26))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_118])).
% 2.86/1.34  tff(c_157, plain, (![E_70, C_72, D_68, B_69, A_71]: (k2_xboole_0(k1_enumset1(A_71, B_69, C_72), k2_tarski(D_68, E_70))=k3_enumset1(A_71, B_69, C_72, D_68, E_70))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.86/1.34  tff(c_460, plain, (![B_133, C_136, E_137, D_132, C_134, A_135]: (k2_xboole_0(k1_enumset1(A_135, B_133, C_134), k2_xboole_0(k2_tarski(D_132, E_137), C_136))=k2_xboole_0(k3_enumset1(A_135, B_133, C_134, D_132, E_137), C_136))), inference(superposition, [status(thm), theory('equality')], [c_157, c_2])).
% 2.86/1.34  tff(c_484, plain, (![B_133, A_25, A_56, C_134, B_26, A_135]: (k2_xboole_0(k3_enumset1(A_135, B_133, C_134, A_56, A_25), k1_tarski(B_26))=k2_xboole_0(k1_enumset1(A_135, B_133, C_134), k1_enumset1(A_56, A_25, B_26)))), inference(superposition, [status(thm), theory('equality')], [c_123, c_460])).
% 2.86/1.34  tff(c_597, plain, (![B_133, A_25, A_56, C_134, B_26, A_135]: (k2_xboole_0(k1_enumset1(A_135, B_133, C_134), k1_enumset1(A_56, A_25, B_26))=k2_xboole_0(k2_tarski(A_135, B_133), k2_enumset1(C_134, A_56, A_25, B_26)))), inference(demodulation, [status(thm), theory('equality')], [c_505, c_484])).
% 2.86/1.34  tff(c_663, plain, (![C_190, B_191, A_194, A_192, A_189, B_193]: (k2_xboole_0(k1_enumset1(A_192, B_191, C_190), k1_enumset1(A_194, A_189, B_193))=k2_xboole_0(k1_tarski(A_192), k3_enumset1(B_191, C_190, A_194, A_189, B_193)))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_597])).
% 2.86/1.34  tff(c_115, plain, (![A_56, A_27, B_28, C_29]: (k2_xboole_0(k2_tarski(A_56, A_27), k2_tarski(B_28, C_29))=k2_xboole_0(k1_tarski(A_56), k1_enumset1(A_27, B_28, C_29)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_97])).
% 2.86/1.34  tff(c_136, plain, (![A_62, A_63, B_64, C_65]: (k2_xboole_0(k1_tarski(A_62), k1_enumset1(A_63, B_64, C_65))=k2_enumset1(A_62, A_63, B_64, C_65))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_115])).
% 2.86/1.34  tff(c_145, plain, (![C_3, B_64, C_65, A_63, A_62]: (k2_xboole_0(k1_tarski(A_62), k2_xboole_0(k1_enumset1(A_63, B_64, C_65), C_3))=k2_xboole_0(k2_enumset1(A_62, A_63, B_64, C_65), C_3))), inference(superposition, [status(thm), theory('equality')], [c_136, c_2])).
% 2.86/1.34  tff(c_672, plain, (![C_190, B_191, A_194, A_192, A_62, A_189, B_193]: (k2_xboole_0(k1_tarski(A_62), k2_xboole_0(k1_tarski(A_192), k3_enumset1(B_191, C_190, A_194, A_189, B_193)))=k2_xboole_0(k2_enumset1(A_62, A_192, B_191, C_190), k1_enumset1(A_194, A_189, B_193)))), inference(superposition, [status(thm), theory('equality')], [c_663, c_145])).
% 2.86/1.34  tff(c_681, plain, (![C_190, B_191, A_194, A_192, A_62, A_189, B_193]: (k2_xboole_0(k2_tarski(A_62, A_192), k3_enumset1(B_191, C_190, A_194, A_189, B_193))=k5_enumset1(A_62, A_192, B_191, C_190, A_194, A_189, B_193))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_72, c_672])).
% 2.86/1.34  tff(c_28, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), k3_enumset1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'))!=k5_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.86/1.34  tff(c_720, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_681, c_28])).
% 2.86/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.34  
% 2.86/1.34  Inference rules
% 2.86/1.34  ----------------------
% 2.86/1.34  #Ref     : 0
% 2.86/1.34  #Sup     : 174
% 2.86/1.34  #Fact    : 0
% 2.86/1.34  #Define  : 0
% 2.86/1.34  #Split   : 0
% 2.86/1.34  #Chain   : 0
% 2.86/1.34  #Close   : 0
% 2.86/1.34  
% 2.86/1.34  Ordering : KBO
% 2.86/1.34  
% 2.86/1.34  Simplification rules
% 2.86/1.34  ----------------------
% 2.86/1.34  #Subsume      : 0
% 2.86/1.34  #Demod        : 94
% 2.86/1.34  #Tautology    : 91
% 2.86/1.34  #SimpNegUnit  : 0
% 2.86/1.34  #BackRed      : 4
% 2.86/1.34  
% 2.86/1.34  #Partial instantiations: 0
% 2.86/1.34  #Strategies tried      : 1
% 2.86/1.34  
% 2.86/1.34  Timing (in seconds)
% 2.86/1.34  ----------------------
% 2.86/1.35  Preprocessing        : 0.27
% 2.86/1.35  Parsing              : 0.15
% 2.86/1.35  CNF conversion       : 0.02
% 2.86/1.35  Main loop            : 0.40
% 2.86/1.35  Inferencing          : 0.18
% 2.86/1.35  Reduction            : 0.13
% 2.86/1.35  Demodulation         : 0.10
% 2.86/1.35  BG Simplification    : 0.03
% 2.86/1.35  Subsumption          : 0.05
% 2.86/1.35  Abstraction          : 0.03
% 2.86/1.35  MUC search           : 0.00
% 2.86/1.35  Cooper               : 0.00
% 2.86/1.35  Total                : 0.70
% 2.86/1.35  Index Insertion      : 0.00
% 2.86/1.35  Index Deletion       : 0.00
% 2.86/1.35  Index Matching       : 0.00
% 2.86/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
