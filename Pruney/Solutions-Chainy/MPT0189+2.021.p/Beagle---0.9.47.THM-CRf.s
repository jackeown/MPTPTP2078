%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:53 EST 2020

% Result     : Theorem 4.29s
% Output     : CNFRefutation 4.29s
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

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_37,axiom,(
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

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_10,plain,(
    ! [A_16,B_17,D_19,C_18] : k2_enumset1(A_16,B_17,D_19,C_18) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_20,C_22,D_23,B_21] : k2_enumset1(A_20,C_22,D_23,B_21) = k2_enumset1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [A_61,B_62,C_63,D_64] : k3_enumset1(A_61,A_61,B_62,C_63,D_64) = k2_enumset1(A_61,B_62,C_63,D_64) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_213,plain,(
    ! [A_100,B_101,D_102,C_103] : k2_enumset1(A_100,B_101,D_102,C_103) = k2_enumset1(A_100,B_101,C_103,D_102) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

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
    ! [B_150,E_151,G_148,A_153,F_152,C_149,D_154] : k2_xboole_0(k4_enumset1(A_153,B_150,C_149,D_154,E_151,F_152),k1_tarski(G_148)) = k5_enumset1(A_153,B_150,C_149,D_154,E_151,F_152,G_148) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_903,plain,(
    ! [B_66,A_65,C_67,G_148,D_68,E_69] : k5_enumset1(A_65,A_65,B_66,C_67,D_68,E_69,G_148) = k2_xboole_0(k3_enumset1(A_65,B_66,C_67,D_68,E_69),k1_tarski(G_148)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_894])).

tff(c_1666,plain,(
    ! [E_205,D_201,B_203,C_202,G_206,A_204] : k2_xboole_0(k3_enumset1(A_204,B_203,C_202,D_201,E_205),k1_tarski(G_206)) = k4_enumset1(A_204,B_203,C_202,D_201,E_205,G_206) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_903])).

tff(c_1675,plain,(
    ! [A_61,B_62,C_63,D_64,G_206] : k4_enumset1(A_61,A_61,B_62,C_63,D_64,G_206) = k2_xboole_0(k2_enumset1(A_61,B_62,C_63,D_64),k1_tarski(G_206)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1666])).

tff(c_1698,plain,(
    ! [C_215,A_218,G_214,D_216,B_217] : k2_xboole_0(k2_enumset1(A_218,B_217,C_215,D_216),k1_tarski(G_214)) = k3_enumset1(A_218,B_217,C_215,D_216,G_214) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1675])).

tff(c_1737,plain,(
    ! [B_101,D_102,C_103,G_214] : k3_enumset1(B_101,B_101,D_102,C_103,G_214) = k2_xboole_0(k1_enumset1(B_101,C_103,D_102),k1_tarski(G_214)) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_1698])).

tff(c_1749,plain,(
    ! [B_101,C_103,D_102,G_214] : k2_xboole_0(k1_enumset1(B_101,C_103,D_102),k1_tarski(G_214)) = k2_enumset1(B_101,D_102,C_103,G_214) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1737])).

tff(c_8,plain,(
    ! [B_14,C_15,A_13] : k1_enumset1(B_14,C_15,A_13) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1751,plain,(
    ! [B_219,C_220,D_221,G_222] : k2_xboole_0(k1_enumset1(B_219,C_220,D_221),k1_tarski(G_222)) = k2_enumset1(B_219,D_221,C_220,G_222) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1737])).

tff(c_1808,plain,(
    ! [B_226,C_227,A_228,G_229] : k2_xboole_0(k1_enumset1(B_226,C_227,A_228),k1_tarski(G_229)) = k2_enumset1(A_228,C_227,B_226,G_229) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1751])).

tff(c_1820,plain,(
    ! [D_102,C_103,B_101,G_214] : k2_enumset1(D_102,C_103,B_101,G_214) = k2_enumset1(B_101,D_102,C_103,G_214) ),
    inference(superposition,[status(thm),theory(equality)],[c_1749,c_1808])).

tff(c_36,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_37,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_36])).

tff(c_38,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_37])).

tff(c_2506,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1820,c_1820,c_1820,c_38])).

tff(c_2509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_10,c_2506])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.29/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.29/1.78  
% 4.29/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.29/1.78  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.29/1.78  
% 4.29/1.78  %Foreground sorts:
% 4.29/1.78  
% 4.29/1.78  
% 4.29/1.78  %Background operators:
% 4.29/1.78  
% 4.29/1.78  
% 4.29/1.78  %Foreground operators:
% 4.29/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.29/1.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.29/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.29/1.78  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.29/1.78  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.29/1.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.29/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.29/1.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.29/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.29/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.29/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.29/1.78  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.29/1.78  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.29/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.29/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.29/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.29/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.29/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.29/1.78  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.29/1.78  
% 4.29/1.79  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 4.29/1.79  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 4.29/1.79  tff(f_53, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.29/1.79  tff(f_51, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.29/1.79  tff(f_55, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 4.29/1.79  tff(f_57, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 4.29/1.79  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 4.29/1.79  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 4.29/1.79  tff(f_62, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 4.29/1.79  tff(c_10, plain, (![A_16, B_17, D_19, C_18]: (k2_enumset1(A_16, B_17, D_19, C_18)=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.29/1.79  tff(c_12, plain, (![A_20, C_22, D_23, B_21]: (k2_enumset1(A_20, C_22, D_23, B_21)=k2_enumset1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.29/1.79  tff(c_28, plain, (![A_61, B_62, C_63, D_64]: (k3_enumset1(A_61, A_61, B_62, C_63, D_64)=k2_enumset1(A_61, B_62, C_63, D_64))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.29/1.79  tff(c_213, plain, (![A_100, B_101, D_102, C_103]: (k2_enumset1(A_100, B_101, D_102, C_103)=k2_enumset1(A_100, B_101, C_103, D_102))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.29/1.79  tff(c_26, plain, (![A_58, B_59, C_60]: (k2_enumset1(A_58, A_58, B_59, C_60)=k1_enumset1(A_58, B_59, C_60))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.29/1.79  tff(c_229, plain, (![B_101, D_102, C_103]: (k2_enumset1(B_101, B_101, D_102, C_103)=k1_enumset1(B_101, C_103, D_102))), inference(superposition, [status(thm), theory('equality')], [c_213, c_26])).
% 4.29/1.79  tff(c_30, plain, (![B_66, A_65, C_67, D_68, E_69]: (k4_enumset1(A_65, A_65, B_66, C_67, D_68, E_69)=k3_enumset1(A_65, B_66, C_67, D_68, E_69))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.29/1.79  tff(c_32, plain, (![F_75, D_73, A_70, E_74, C_72, B_71]: (k5_enumset1(A_70, A_70, B_71, C_72, D_73, E_74, F_75)=k4_enumset1(A_70, B_71, C_72, D_73, E_74, F_75))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.29/1.79  tff(c_894, plain, (![B_150, E_151, G_148, A_153, F_152, C_149, D_154]: (k2_xboole_0(k4_enumset1(A_153, B_150, C_149, D_154, E_151, F_152), k1_tarski(G_148))=k5_enumset1(A_153, B_150, C_149, D_154, E_151, F_152, G_148))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.29/1.79  tff(c_903, plain, (![B_66, A_65, C_67, G_148, D_68, E_69]: (k5_enumset1(A_65, A_65, B_66, C_67, D_68, E_69, G_148)=k2_xboole_0(k3_enumset1(A_65, B_66, C_67, D_68, E_69), k1_tarski(G_148)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_894])).
% 4.29/1.79  tff(c_1666, plain, (![E_205, D_201, B_203, C_202, G_206, A_204]: (k2_xboole_0(k3_enumset1(A_204, B_203, C_202, D_201, E_205), k1_tarski(G_206))=k4_enumset1(A_204, B_203, C_202, D_201, E_205, G_206))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_903])).
% 4.29/1.79  tff(c_1675, plain, (![A_61, B_62, C_63, D_64, G_206]: (k4_enumset1(A_61, A_61, B_62, C_63, D_64, G_206)=k2_xboole_0(k2_enumset1(A_61, B_62, C_63, D_64), k1_tarski(G_206)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1666])).
% 4.29/1.79  tff(c_1698, plain, (![C_215, A_218, G_214, D_216, B_217]: (k2_xboole_0(k2_enumset1(A_218, B_217, C_215, D_216), k1_tarski(G_214))=k3_enumset1(A_218, B_217, C_215, D_216, G_214))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1675])).
% 4.29/1.79  tff(c_1737, plain, (![B_101, D_102, C_103, G_214]: (k3_enumset1(B_101, B_101, D_102, C_103, G_214)=k2_xboole_0(k1_enumset1(B_101, C_103, D_102), k1_tarski(G_214)))), inference(superposition, [status(thm), theory('equality')], [c_229, c_1698])).
% 4.29/1.79  tff(c_1749, plain, (![B_101, C_103, D_102, G_214]: (k2_xboole_0(k1_enumset1(B_101, C_103, D_102), k1_tarski(G_214))=k2_enumset1(B_101, D_102, C_103, G_214))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1737])).
% 4.29/1.79  tff(c_8, plain, (![B_14, C_15, A_13]: (k1_enumset1(B_14, C_15, A_13)=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.29/1.79  tff(c_1751, plain, (![B_219, C_220, D_221, G_222]: (k2_xboole_0(k1_enumset1(B_219, C_220, D_221), k1_tarski(G_222))=k2_enumset1(B_219, D_221, C_220, G_222))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1737])).
% 4.29/1.79  tff(c_1808, plain, (![B_226, C_227, A_228, G_229]: (k2_xboole_0(k1_enumset1(B_226, C_227, A_228), k1_tarski(G_229))=k2_enumset1(A_228, C_227, B_226, G_229))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1751])).
% 4.29/1.79  tff(c_1820, plain, (![D_102, C_103, B_101, G_214]: (k2_enumset1(D_102, C_103, B_101, G_214)=k2_enumset1(B_101, D_102, C_103, G_214))), inference(superposition, [status(thm), theory('equality')], [c_1749, c_1808])).
% 4.29/1.79  tff(c_36, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.29/1.79  tff(c_37, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_36])).
% 4.29/1.79  tff(c_38, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_37])).
% 4.29/1.79  tff(c_2506, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1820, c_1820, c_1820, c_38])).
% 4.29/1.79  tff(c_2509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_10, c_2506])).
% 4.29/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.29/1.79  
% 4.29/1.79  Inference rules
% 4.29/1.79  ----------------------
% 4.29/1.79  #Ref     : 0
% 4.29/1.79  #Sup     : 624
% 4.29/1.79  #Fact    : 0
% 4.29/1.79  #Define  : 0
% 4.29/1.79  #Split   : 0
% 4.29/1.79  #Chain   : 0
% 4.29/1.79  #Close   : 0
% 4.29/1.79  
% 4.29/1.79  Ordering : KBO
% 4.29/1.79  
% 4.29/1.79  Simplification rules
% 4.29/1.79  ----------------------
% 4.29/1.79  #Subsume      : 119
% 4.29/1.79  #Demod        : 344
% 4.29/1.79  #Tautology    : 357
% 4.29/1.79  #SimpNegUnit  : 0
% 4.29/1.79  #BackRed      : 1
% 4.29/1.79  
% 4.29/1.79  #Partial instantiations: 0
% 4.29/1.79  #Strategies tried      : 1
% 4.29/1.79  
% 4.29/1.79  Timing (in seconds)
% 4.29/1.79  ----------------------
% 4.29/1.80  Preprocessing        : 0.31
% 4.29/1.80  Parsing              : 0.15
% 4.29/1.80  CNF conversion       : 0.02
% 4.29/1.80  Main loop            : 0.68
% 4.29/1.80  Inferencing          : 0.22
% 4.29/1.80  Reduction            : 0.30
% 4.29/1.80  Demodulation         : 0.26
% 4.29/1.80  BG Simplification    : 0.04
% 4.29/1.80  Subsumption          : 0.08
% 4.29/1.80  Abstraction          : 0.04
% 4.29/1.80  MUC search           : 0.00
% 4.29/1.80  Cooper               : 0.00
% 4.29/1.80  Total                : 1.02
% 4.29/1.80  Index Insertion      : 0.00
% 4.29/1.80  Index Deletion       : 0.00
% 4.29/1.80  Index Matching       : 0.00
% 4.29/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
