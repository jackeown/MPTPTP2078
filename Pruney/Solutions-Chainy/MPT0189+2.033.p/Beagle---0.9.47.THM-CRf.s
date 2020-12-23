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

% Result     : Theorem 4.11s
% Output     : CNFRefutation 4.46s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 148 expanded)
%              Number of leaves         :   22 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :   25 ( 132 expanded)
%              Number of equality atoms :   24 ( 131 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_16,plain,(
    ! [A_27,B_28,C_29,D_30] : k3_enumset1(A_27,A_27,B_28,C_29,D_30) = k2_enumset1(A_27,B_28,C_29,D_30) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_24,B_25,C_26] : k2_enumset1(A_24,A_24,B_25,C_26) = k1_enumset1(A_24,B_25,C_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_631,plain,(
    ! [A_87,E_88,D_91,B_89,C_90] : k2_xboole_0(k2_enumset1(A_87,B_89,C_90,D_91),k1_tarski(E_88)) = k3_enumset1(A_87,B_89,C_90,D_91,E_88) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_649,plain,(
    ! [A_24,B_25,C_26,E_88] : k3_enumset1(A_24,A_24,B_25,C_26,E_88) = k2_xboole_0(k1_enumset1(A_24,B_25,C_26),k1_tarski(E_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_631])).

tff(c_653,plain,(
    ! [A_24,B_25,C_26,E_88] : k2_xboole_0(k1_enumset1(A_24,B_25,C_26),k1_tarski(E_88)) = k2_enumset1(A_24,B_25,C_26,E_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_649])).

tff(c_4,plain,(
    ! [A_4,B_5,D_7,C_6] : k2_enumset1(A_4,B_5,D_7,C_6) = k2_enumset1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_966,plain,(
    ! [C_132,D_133,B_131,E_134,A_135] : k2_xboole_0(k2_enumset1(A_135,B_131,C_132,D_133),k1_tarski(E_134)) = k3_enumset1(A_135,B_131,D_133,C_132,E_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_631])).

tff(c_999,plain,(
    ! [A_24,C_26,B_25,E_134] : k3_enumset1(A_24,A_24,C_26,B_25,E_134) = k2_xboole_0(k1_enumset1(A_24,B_25,C_26),k1_tarski(E_134)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_966])).

tff(c_1008,plain,(
    ! [A_24,C_26,B_25,E_134] : k2_enumset1(A_24,C_26,B_25,E_134) = k2_enumset1(A_24,B_25,C_26,E_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_16,c_999])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1] : k1_enumset1(B_2,C_3,A_1) = k1_enumset1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_666,plain,(
    ! [A_98,B_99,C_100,E_101] : k2_xboole_0(k1_enumset1(A_98,B_99,C_100),k1_tarski(E_101)) = k2_enumset1(A_98,B_99,C_100,E_101) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_649])).

tff(c_2850,plain,(
    ! [A_220,B_221,C_222,E_223] : k2_xboole_0(k1_enumset1(A_220,B_221,C_222),k1_tarski(E_223)) = k2_enumset1(B_221,C_222,A_220,E_223) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_666])).

tff(c_2856,plain,(
    ! [B_221,C_222,A_220,E_223] : k2_enumset1(B_221,C_222,A_220,E_223) = k2_enumset1(A_220,B_221,C_222,E_223) ),
    inference(superposition,[status(thm),theory(equality)],[c_2850,c_653])).

tff(c_24,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_25,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_4','#skF_3') != k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_24])).

tff(c_1136,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_1008,c_25])).

tff(c_1137,plain,(
    k2_enumset1('#skF_2','#skF_4','#skF_1','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1136])).

tff(c_2902,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2856,c_2856,c_2856,c_1137])).

tff(c_2905,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_4,c_2902])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:30:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.11/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.46/1.78  
% 4.46/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.46/1.78  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.46/1.78  
% 4.46/1.78  %Foreground sorts:
% 4.46/1.78  
% 4.46/1.78  
% 4.46/1.78  %Background operators:
% 4.46/1.78  
% 4.46/1.78  
% 4.46/1.78  %Foreground operators:
% 4.46/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.46/1.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.46/1.78  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.46/1.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.46/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.46/1.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.46/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.46/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.46/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.46/1.78  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.46/1.78  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.46/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.46/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.46/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.46/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.46/1.78  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.46/1.78  
% 4.46/1.79  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 4.46/1.79  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.46/1.79  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 4.46/1.79  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 4.46/1.79  tff(f_27, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 4.46/1.79  tff(f_50, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_enumset1)).
% 4.46/1.79  tff(c_16, plain, (![A_27, B_28, C_29, D_30]: (k3_enumset1(A_27, A_27, B_28, C_29, D_30)=k2_enumset1(A_27, B_28, C_29, D_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.46/1.79  tff(c_14, plain, (![A_24, B_25, C_26]: (k2_enumset1(A_24, A_24, B_25, C_26)=k1_enumset1(A_24, B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.46/1.79  tff(c_631, plain, (![A_87, E_88, D_91, B_89, C_90]: (k2_xboole_0(k2_enumset1(A_87, B_89, C_90, D_91), k1_tarski(E_88))=k3_enumset1(A_87, B_89, C_90, D_91, E_88))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.46/1.79  tff(c_649, plain, (![A_24, B_25, C_26, E_88]: (k3_enumset1(A_24, A_24, B_25, C_26, E_88)=k2_xboole_0(k1_enumset1(A_24, B_25, C_26), k1_tarski(E_88)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_631])).
% 4.46/1.79  tff(c_653, plain, (![A_24, B_25, C_26, E_88]: (k2_xboole_0(k1_enumset1(A_24, B_25, C_26), k1_tarski(E_88))=k2_enumset1(A_24, B_25, C_26, E_88))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_649])).
% 4.46/1.79  tff(c_4, plain, (![A_4, B_5, D_7, C_6]: (k2_enumset1(A_4, B_5, D_7, C_6)=k2_enumset1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.46/1.79  tff(c_966, plain, (![C_132, D_133, B_131, E_134, A_135]: (k2_xboole_0(k2_enumset1(A_135, B_131, C_132, D_133), k1_tarski(E_134))=k3_enumset1(A_135, B_131, D_133, C_132, E_134))), inference(superposition, [status(thm), theory('equality')], [c_4, c_631])).
% 4.46/1.79  tff(c_999, plain, (![A_24, C_26, B_25, E_134]: (k3_enumset1(A_24, A_24, C_26, B_25, E_134)=k2_xboole_0(k1_enumset1(A_24, B_25, C_26), k1_tarski(E_134)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_966])).
% 4.46/1.79  tff(c_1008, plain, (![A_24, C_26, B_25, E_134]: (k2_enumset1(A_24, C_26, B_25, E_134)=k2_enumset1(A_24, B_25, C_26, E_134))), inference(demodulation, [status(thm), theory('equality')], [c_653, c_16, c_999])).
% 4.46/1.79  tff(c_2, plain, (![B_2, C_3, A_1]: (k1_enumset1(B_2, C_3, A_1)=k1_enumset1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.46/1.79  tff(c_666, plain, (![A_98, B_99, C_100, E_101]: (k2_xboole_0(k1_enumset1(A_98, B_99, C_100), k1_tarski(E_101))=k2_enumset1(A_98, B_99, C_100, E_101))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_649])).
% 4.46/1.79  tff(c_2850, plain, (![A_220, B_221, C_222, E_223]: (k2_xboole_0(k1_enumset1(A_220, B_221, C_222), k1_tarski(E_223))=k2_enumset1(B_221, C_222, A_220, E_223))), inference(superposition, [status(thm), theory('equality')], [c_2, c_666])).
% 4.46/1.79  tff(c_2856, plain, (![B_221, C_222, A_220, E_223]: (k2_enumset1(B_221, C_222, A_220, E_223)=k2_enumset1(A_220, B_221, C_222, E_223))), inference(superposition, [status(thm), theory('equality')], [c_2850, c_653])).
% 4.46/1.79  tff(c_24, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.46/1.79  tff(c_25, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_4', '#skF_3')!=k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_24])).
% 4.46/1.79  tff(c_1136, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_1008, c_25])).
% 4.46/1.79  tff(c_1137, plain, (k2_enumset1('#skF_2', '#skF_4', '#skF_1', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1136])).
% 4.46/1.79  tff(c_2902, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2856, c_2856, c_2856, c_1137])).
% 4.46/1.79  tff(c_2905, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1008, c_4, c_2902])).
% 4.46/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.46/1.79  
% 4.46/1.79  Inference rules
% 4.46/1.79  ----------------------
% 4.46/1.79  #Ref     : 0
% 4.46/1.79  #Sup     : 718
% 4.46/1.79  #Fact    : 0
% 4.46/1.79  #Define  : 0
% 4.46/1.79  #Split   : 0
% 4.46/1.79  #Chain   : 0
% 4.46/1.79  #Close   : 0
% 4.46/1.79  
% 4.46/1.79  Ordering : KBO
% 4.46/1.79  
% 4.46/1.79  Simplification rules
% 4.46/1.79  ----------------------
% 4.46/1.79  #Subsume      : 126
% 4.46/1.79  #Demod        : 457
% 4.46/1.79  #Tautology    : 419
% 4.46/1.79  #SimpNegUnit  : 0
% 4.46/1.79  #BackRed      : 2
% 4.46/1.79  
% 4.46/1.79  #Partial instantiations: 0
% 4.46/1.79  #Strategies tried      : 1
% 4.46/1.79  
% 4.46/1.79  Timing (in seconds)
% 4.46/1.79  ----------------------
% 4.46/1.79  Preprocessing        : 0.31
% 4.46/1.79  Parsing              : 0.17
% 4.46/1.79  CNF conversion       : 0.02
% 4.46/1.79  Main loop            : 0.71
% 4.46/1.79  Inferencing          : 0.26
% 4.46/1.79  Reduction            : 0.31
% 4.46/1.79  Demodulation         : 0.27
% 4.46/1.79  BG Simplification    : 0.03
% 4.46/1.79  Subsumption          : 0.08
% 4.46/1.79  Abstraction          : 0.04
% 4.46/1.79  MUC search           : 0.00
% 4.46/1.79  Cooper               : 0.00
% 4.46/1.79  Total                : 1.05
% 4.55/1.79  Index Insertion      : 0.00
% 4.55/1.79  Index Deletion       : 0.00
% 4.55/1.79  Index Matching       : 0.00
% 4.55/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
