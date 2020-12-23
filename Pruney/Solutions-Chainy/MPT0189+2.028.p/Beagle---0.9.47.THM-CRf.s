%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:54 EST 2020

% Result     : Theorem 4.05s
% Output     : CNFRefutation 4.05s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 187 expanded)
%              Number of leaves         :   28 (  77 expanded)
%              Depth                    :   11
%              Number of atoms          :   33 ( 168 expanded)
%              Number of equality atoms :   32 ( 167 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_8,plain,(
    ! [A_8,B_9,D_11,C_10] : k2_enumset1(A_8,B_9,D_11,C_10) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_12,C_14,D_15,B_13] : k2_enumset1(A_12,C_14,D_15,B_13) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ! [A_61,B_62,C_63,D_64] : k3_enumset1(A_61,A_61,B_62,C_63,D_64) = k2_enumset1(A_61,B_62,C_63,D_64) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_213,plain,(
    ! [A_100,B_101,D_102,C_103] : k2_enumset1(A_100,B_101,D_102,C_103) = k2_enumset1(A_100,B_101,C_103,D_102) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [A_58,B_59,C_60] : k2_enumset1(A_58,A_58,B_59,C_60) = k1_enumset1(A_58,B_59,C_60) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_229,plain,(
    ! [B_101,D_102,C_103] : k2_enumset1(B_101,B_101,D_102,C_103) = k1_enumset1(B_101,C_103,D_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_26])).

tff(c_30,plain,(
    ! [B_66,A_65,C_67,D_68,E_69] : k4_enumset1(A_65,A_65,B_66,C_67,D_68,E_69) = k3_enumset1(A_65,B_66,C_67,D_68,E_69) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32,plain,(
    ! [F_75,D_73,A_70,E_74,C_72,B_71] : k5_enumset1(A_70,A_70,B_71,C_72,D_73,E_74,F_75) = k4_enumset1(A_70,B_71,C_72,D_73,E_74,F_75) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_894,plain,(
    ! [A_152,B_150,C_154,E_151,G_149,D_153,F_148] : k2_xboole_0(k4_enumset1(A_152,B_150,C_154,D_153,E_151,F_148),k1_tarski(G_149)) = k5_enumset1(A_152,B_150,C_154,D_153,E_151,F_148,G_149) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_903,plain,(
    ! [B_66,A_65,C_67,G_149,D_68,E_69] : k5_enumset1(A_65,A_65,B_66,C_67,D_68,E_69,G_149) = k2_xboole_0(k3_enumset1(A_65,B_66,C_67,D_68,E_69),k1_tarski(G_149)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_894])).

tff(c_1617,plain,(
    ! [C_203,B_204,E_206,D_201,G_202,A_205] : k2_xboole_0(k3_enumset1(A_205,B_204,C_203,D_201,E_206),k1_tarski(G_202)) = k4_enumset1(A_205,B_204,C_203,D_201,E_206,G_202) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_903])).

tff(c_1626,plain,(
    ! [A_61,B_62,C_63,D_64,G_202] : k4_enumset1(A_61,A_61,B_62,C_63,D_64,G_202) = k2_xboole_0(k2_enumset1(A_61,B_62,C_63,D_64),k1_tarski(G_202)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1617])).

tff(c_1649,plain,(
    ! [C_215,A_218,G_214,D_216,B_217] : k2_xboole_0(k2_enumset1(A_218,B_217,C_215,D_216),k1_tarski(G_214)) = k3_enumset1(A_218,B_217,C_215,D_216,G_214) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1626])).

tff(c_1688,plain,(
    ! [B_101,D_102,C_103,G_214] : k3_enumset1(B_101,B_101,D_102,C_103,G_214) = k2_xboole_0(k1_enumset1(B_101,C_103,D_102),k1_tarski(G_214)) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_1649])).

tff(c_1700,plain,(
    ! [B_101,C_103,D_102,G_214] : k2_xboole_0(k1_enumset1(B_101,C_103,D_102),k1_tarski(G_214)) = k2_enumset1(B_101,D_102,C_103,G_214) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1688])).

tff(c_6,plain,(
    ! [B_6,C_7,A_5] : k1_enumset1(B_6,C_7,A_5) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1702,plain,(
    ! [B_219,C_220,D_221,G_222] : k2_xboole_0(k1_enumset1(B_219,C_220,D_221),k1_tarski(G_222)) = k2_enumset1(B_219,D_221,C_220,G_222) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1688])).

tff(c_1759,plain,(
    ! [B_226,C_227,A_228,G_229] : k2_xboole_0(k1_enumset1(B_226,C_227,A_228),k1_tarski(G_229)) = k2_enumset1(A_228,C_227,B_226,G_229) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1702])).

tff(c_1771,plain,(
    ! [D_102,C_103,B_101,G_214] : k2_enumset1(D_102,C_103,B_101,G_214) = k2_enumset1(B_101,D_102,C_103,G_214) ),
    inference(superposition,[status(thm),theory(equality)],[c_1700,c_1759])).

tff(c_36,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_37,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_36])).

tff(c_38,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_37])).

tff(c_2439,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1771,c_1771,c_1771,c_38])).

tff(c_2442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10,c_8,c_2439])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:25:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.05/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/1.84  
% 4.05/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/1.85  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.05/1.85  
% 4.05/1.85  %Foreground sorts:
% 4.05/1.85  
% 4.05/1.85  
% 4.05/1.85  %Background operators:
% 4.05/1.85  
% 4.05/1.85  
% 4.05/1.85  %Foreground operators:
% 4.05/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.05/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.05/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.05/1.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.05/1.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.05/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.05/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.05/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.05/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.05/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.05/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.05/1.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.05/1.85  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.05/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.05/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.05/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.05/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.05/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.05/1.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.05/1.85  
% 4.05/1.86  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 4.05/1.86  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 4.05/1.86  tff(f_53, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.05/1.86  tff(f_51, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.05/1.86  tff(f_55, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 4.05/1.86  tff(f_57, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 4.05/1.86  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 4.05/1.86  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 4.05/1.86  tff(f_62, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 4.05/1.86  tff(c_8, plain, (![A_8, B_9, D_11, C_10]: (k2_enumset1(A_8, B_9, D_11, C_10)=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.05/1.86  tff(c_10, plain, (![A_12, C_14, D_15, B_13]: (k2_enumset1(A_12, C_14, D_15, B_13)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.05/1.86  tff(c_28, plain, (![A_61, B_62, C_63, D_64]: (k3_enumset1(A_61, A_61, B_62, C_63, D_64)=k2_enumset1(A_61, B_62, C_63, D_64))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.05/1.86  tff(c_213, plain, (![A_100, B_101, D_102, C_103]: (k2_enumset1(A_100, B_101, D_102, C_103)=k2_enumset1(A_100, B_101, C_103, D_102))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.05/1.86  tff(c_26, plain, (![A_58, B_59, C_60]: (k2_enumset1(A_58, A_58, B_59, C_60)=k1_enumset1(A_58, B_59, C_60))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.05/1.86  tff(c_229, plain, (![B_101, D_102, C_103]: (k2_enumset1(B_101, B_101, D_102, C_103)=k1_enumset1(B_101, C_103, D_102))), inference(superposition, [status(thm), theory('equality')], [c_213, c_26])).
% 4.05/1.86  tff(c_30, plain, (![B_66, A_65, C_67, D_68, E_69]: (k4_enumset1(A_65, A_65, B_66, C_67, D_68, E_69)=k3_enumset1(A_65, B_66, C_67, D_68, E_69))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.05/1.86  tff(c_32, plain, (![F_75, D_73, A_70, E_74, C_72, B_71]: (k5_enumset1(A_70, A_70, B_71, C_72, D_73, E_74, F_75)=k4_enumset1(A_70, B_71, C_72, D_73, E_74, F_75))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.05/1.86  tff(c_894, plain, (![A_152, B_150, C_154, E_151, G_149, D_153, F_148]: (k2_xboole_0(k4_enumset1(A_152, B_150, C_154, D_153, E_151, F_148), k1_tarski(G_149))=k5_enumset1(A_152, B_150, C_154, D_153, E_151, F_148, G_149))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.05/1.86  tff(c_903, plain, (![B_66, A_65, C_67, G_149, D_68, E_69]: (k5_enumset1(A_65, A_65, B_66, C_67, D_68, E_69, G_149)=k2_xboole_0(k3_enumset1(A_65, B_66, C_67, D_68, E_69), k1_tarski(G_149)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_894])).
% 4.05/1.86  tff(c_1617, plain, (![C_203, B_204, E_206, D_201, G_202, A_205]: (k2_xboole_0(k3_enumset1(A_205, B_204, C_203, D_201, E_206), k1_tarski(G_202))=k4_enumset1(A_205, B_204, C_203, D_201, E_206, G_202))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_903])).
% 4.05/1.86  tff(c_1626, plain, (![A_61, B_62, C_63, D_64, G_202]: (k4_enumset1(A_61, A_61, B_62, C_63, D_64, G_202)=k2_xboole_0(k2_enumset1(A_61, B_62, C_63, D_64), k1_tarski(G_202)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1617])).
% 4.05/1.86  tff(c_1649, plain, (![C_215, A_218, G_214, D_216, B_217]: (k2_xboole_0(k2_enumset1(A_218, B_217, C_215, D_216), k1_tarski(G_214))=k3_enumset1(A_218, B_217, C_215, D_216, G_214))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1626])).
% 4.05/1.86  tff(c_1688, plain, (![B_101, D_102, C_103, G_214]: (k3_enumset1(B_101, B_101, D_102, C_103, G_214)=k2_xboole_0(k1_enumset1(B_101, C_103, D_102), k1_tarski(G_214)))), inference(superposition, [status(thm), theory('equality')], [c_229, c_1649])).
% 4.05/1.86  tff(c_1700, plain, (![B_101, C_103, D_102, G_214]: (k2_xboole_0(k1_enumset1(B_101, C_103, D_102), k1_tarski(G_214))=k2_enumset1(B_101, D_102, C_103, G_214))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1688])).
% 4.05/1.86  tff(c_6, plain, (![B_6, C_7, A_5]: (k1_enumset1(B_6, C_7, A_5)=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.05/1.86  tff(c_1702, plain, (![B_219, C_220, D_221, G_222]: (k2_xboole_0(k1_enumset1(B_219, C_220, D_221), k1_tarski(G_222))=k2_enumset1(B_219, D_221, C_220, G_222))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1688])).
% 4.05/1.86  tff(c_1759, plain, (![B_226, C_227, A_228, G_229]: (k2_xboole_0(k1_enumset1(B_226, C_227, A_228), k1_tarski(G_229))=k2_enumset1(A_228, C_227, B_226, G_229))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1702])).
% 4.05/1.86  tff(c_1771, plain, (![D_102, C_103, B_101, G_214]: (k2_enumset1(D_102, C_103, B_101, G_214)=k2_enumset1(B_101, D_102, C_103, G_214))), inference(superposition, [status(thm), theory('equality')], [c_1700, c_1759])).
% 4.05/1.86  tff(c_36, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.05/1.86  tff(c_37, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_36])).
% 4.05/1.86  tff(c_38, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_37])).
% 4.05/1.86  tff(c_2439, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1771, c_1771, c_1771, c_38])).
% 4.05/1.86  tff(c_2442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_10, c_8, c_2439])).
% 4.05/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/1.86  
% 4.05/1.86  Inference rules
% 4.05/1.86  ----------------------
% 4.05/1.86  #Ref     : 0
% 4.05/1.86  #Sup     : 602
% 4.05/1.86  #Fact    : 0
% 4.05/1.86  #Define  : 0
% 4.05/1.86  #Split   : 0
% 4.05/1.86  #Chain   : 0
% 4.05/1.86  #Close   : 0
% 4.05/1.86  
% 4.05/1.86  Ordering : KBO
% 4.05/1.86  
% 4.05/1.86  Simplification rules
% 4.05/1.86  ----------------------
% 4.05/1.86  #Subsume      : 119
% 4.05/1.86  #Demod        : 343
% 4.05/1.86  #Tautology    : 357
% 4.05/1.86  #SimpNegUnit  : 0
% 4.05/1.86  #BackRed      : 1
% 4.05/1.86  
% 4.05/1.86  #Partial instantiations: 0
% 4.05/1.86  #Strategies tried      : 1
% 4.05/1.86  
% 4.05/1.86  Timing (in seconds)
% 4.05/1.86  ----------------------
% 4.05/1.86  Preprocessing        : 0.45
% 4.05/1.86  Parsing              : 0.27
% 4.05/1.86  CNF conversion       : 0.02
% 4.05/1.86  Main loop            : 0.60
% 4.05/1.86  Inferencing          : 0.20
% 4.05/1.86  Reduction            : 0.27
% 4.05/1.86  Demodulation         : 0.23
% 4.05/1.86  BG Simplification    : 0.03
% 4.05/1.86  Subsumption          : 0.07
% 4.05/1.86  Abstraction          : 0.04
% 4.05/1.86  MUC search           : 0.00
% 4.05/1.86  Cooper               : 0.00
% 4.05/1.86  Total                : 1.07
% 4.05/1.86  Index Insertion      : 0.00
% 4.05/1.86  Index Deletion       : 0.00
% 4.05/1.86  Index Matching       : 0.00
% 4.05/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
