%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:46 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   38 (  38 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   20 (  20 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) = k2_xboole_0(A,k2_xboole_0(k2_xboole_0(B,C),D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(c_16,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] : k2_xboole_0(k1_enumset1(A_27,B_28,C_29),k1_enumset1(D_30,E_31,F_32)) = k4_enumset1(A_27,B_28,C_29,D_30,E_31,F_32) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11] : k2_xboole_0(k2_tarski(A_9,B_10),k1_tarski(C_11)) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [C_18,B_17,A_16,D_19,E_20] : k2_xboole_0(k2_enumset1(A_16,B_17,C_18,D_19),k1_tarski(E_20)) = k3_enumset1(A_16,B_17,C_18,D_19,E_20) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_7,B_8] : k2_xboole_0(k1_tarski(A_7),k1_tarski(B_8)) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_12,B_13,C_14,D_15] : k2_xboole_0(k1_enumset1(A_12,B_13,C_14),k1_tarski(D_15)) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_61,plain,(
    ! [A_44,B_45,C_46,D_47] : k2_xboole_0(k2_xboole_0(k2_xboole_0(A_44,B_45),C_46),D_47) = k2_xboole_0(A_44,k2_xboole_0(k2_xboole_0(B_45,C_46),D_47)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_465,plain,(
    ! [C_104,C_102,D_103,B_99,A_100,D_101] : k2_xboole_0(k1_enumset1(A_100,B_99,C_104),k2_xboole_0(k2_xboole_0(k1_tarski(D_103),C_102),D_101)) = k2_xboole_0(k2_xboole_0(k2_enumset1(A_100,B_99,C_104,D_103),C_102),D_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_61])).

tff(c_502,plain,(
    ! [C_104,A_7,B_99,A_100,D_101,B_8] : k2_xboole_0(k2_xboole_0(k2_enumset1(A_100,B_99,C_104,A_7),k1_tarski(B_8)),D_101) = k2_xboole_0(k1_enumset1(A_100,B_99,C_104),k2_xboole_0(k2_tarski(A_7,B_8),D_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_465])).

tff(c_511,plain,(
    ! [A_110,D_108,A_109,B_105,C_107,B_106] : k2_xboole_0(k1_enumset1(A_110,B_105,C_107),k2_xboole_0(k2_tarski(A_109,B_106),D_108)) = k2_xboole_0(k3_enumset1(A_110,B_105,C_107,A_109,B_106),D_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_502])).

tff(c_538,plain,(
    ! [C_11,A_110,B_10,B_105,C_107,A_9] : k2_xboole_0(k3_enumset1(A_110,B_105,C_107,A_9,B_10),k1_tarski(C_11)) = k2_xboole_0(k1_enumset1(A_110,B_105,C_107),k1_enumset1(A_9,B_10,C_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_511])).

tff(c_543,plain,(
    ! [C_11,A_110,B_10,B_105,C_107,A_9] : k2_xboole_0(k3_enumset1(A_110,B_105,C_107,A_9,B_10),k1_tarski(C_11)) = k4_enumset1(A_110,B_105,C_107,A_9,B_10,C_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_538])).

tff(c_18,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_tarski('#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_546,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 14:40:40 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.38  
% 2.71/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.38  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.71/1.38  
% 2.71/1.38  %Foreground sorts:
% 2.71/1.38  
% 2.71/1.38  
% 2.71/1.38  %Background operators:
% 2.71/1.38  
% 2.71/1.38  
% 2.71/1.38  %Foreground operators:
% 2.71/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.71/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.71/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.71/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.71/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.71/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.71/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.71/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.71/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.71/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.71/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.71/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.71/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.71/1.38  
% 2.71/1.39  tff(f_41, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_enumset1)).
% 2.71/1.39  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.71/1.39  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 2.71/1.39  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.71/1.39  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.71/1.39  tff(f_27, axiom, (![A, B, C, D]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(A, B), C), D) = k2_xboole_0(A, k2_xboole_0(k2_xboole_0(B, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_xboole_1)).
% 2.71/1.39  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 2.71/1.39  tff(c_16, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (k2_xboole_0(k1_enumset1(A_27, B_28, C_29), k1_enumset1(D_30, E_31, F_32))=k4_enumset1(A_27, B_28, C_29, D_30, E_31, F_32))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.71/1.39  tff(c_8, plain, (![A_9, B_10, C_11]: (k2_xboole_0(k2_tarski(A_9, B_10), k1_tarski(C_11))=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.71/1.39  tff(c_12, plain, (![C_18, B_17, A_16, D_19, E_20]: (k2_xboole_0(k2_enumset1(A_16, B_17, C_18, D_19), k1_tarski(E_20))=k3_enumset1(A_16, B_17, C_18, D_19, E_20))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.71/1.39  tff(c_6, plain, (![A_7, B_8]: (k2_xboole_0(k1_tarski(A_7), k1_tarski(B_8))=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.71/1.39  tff(c_10, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k1_enumset1(A_12, B_13, C_14), k1_tarski(D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.71/1.39  tff(c_61, plain, (![A_44, B_45, C_46, D_47]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(A_44, B_45), C_46), D_47)=k2_xboole_0(A_44, k2_xboole_0(k2_xboole_0(B_45, C_46), D_47)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.71/1.39  tff(c_465, plain, (![C_104, C_102, D_103, B_99, A_100, D_101]: (k2_xboole_0(k1_enumset1(A_100, B_99, C_104), k2_xboole_0(k2_xboole_0(k1_tarski(D_103), C_102), D_101))=k2_xboole_0(k2_xboole_0(k2_enumset1(A_100, B_99, C_104, D_103), C_102), D_101))), inference(superposition, [status(thm), theory('equality')], [c_10, c_61])).
% 2.71/1.39  tff(c_502, plain, (![C_104, A_7, B_99, A_100, D_101, B_8]: (k2_xboole_0(k2_xboole_0(k2_enumset1(A_100, B_99, C_104, A_7), k1_tarski(B_8)), D_101)=k2_xboole_0(k1_enumset1(A_100, B_99, C_104), k2_xboole_0(k2_tarski(A_7, B_8), D_101)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_465])).
% 2.71/1.39  tff(c_511, plain, (![A_110, D_108, A_109, B_105, C_107, B_106]: (k2_xboole_0(k1_enumset1(A_110, B_105, C_107), k2_xboole_0(k2_tarski(A_109, B_106), D_108))=k2_xboole_0(k3_enumset1(A_110, B_105, C_107, A_109, B_106), D_108))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_502])).
% 2.71/1.39  tff(c_538, plain, (![C_11, A_110, B_10, B_105, C_107, A_9]: (k2_xboole_0(k3_enumset1(A_110, B_105, C_107, A_9, B_10), k1_tarski(C_11))=k2_xboole_0(k1_enumset1(A_110, B_105, C_107), k1_enumset1(A_9, B_10, C_11)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_511])).
% 2.71/1.39  tff(c_543, plain, (![C_11, A_110, B_10, B_105, C_107, A_9]: (k2_xboole_0(k3_enumset1(A_110, B_105, C_107, A_9, B_10), k1_tarski(C_11))=k4_enumset1(A_110, B_105, C_107, A_9, B_10, C_11))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_538])).
% 2.71/1.39  tff(c_18, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_tarski('#skF_6'))!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.71/1.39  tff(c_546, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_543, c_18])).
% 2.71/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.39  
% 2.71/1.39  Inference rules
% 2.71/1.39  ----------------------
% 2.71/1.39  #Ref     : 0
% 2.71/1.39  #Sup     : 138
% 2.71/1.39  #Fact    : 0
% 2.71/1.39  #Define  : 0
% 2.71/1.39  #Split   : 0
% 2.71/1.39  #Chain   : 0
% 2.71/1.39  #Close   : 0
% 2.71/1.39  
% 2.71/1.39  Ordering : KBO
% 2.71/1.39  
% 2.71/1.39  Simplification rules
% 2.71/1.39  ----------------------
% 2.71/1.39  #Subsume      : 0
% 2.71/1.39  #Demod        : 113
% 2.71/1.39  #Tautology    : 61
% 2.71/1.39  #SimpNegUnit  : 0
% 2.71/1.39  #BackRed      : 1
% 2.71/1.39  
% 2.71/1.39  #Partial instantiations: 0
% 2.71/1.39  #Strategies tried      : 1
% 2.71/1.39  
% 2.71/1.39  Timing (in seconds)
% 2.71/1.39  ----------------------
% 2.71/1.39  Preprocessing        : 0.27
% 2.71/1.39  Parsing              : 0.15
% 2.71/1.40  CNF conversion       : 0.02
% 2.71/1.40  Main loop            : 0.35
% 2.71/1.40  Inferencing          : 0.15
% 2.71/1.40  Reduction            : 0.13
% 2.71/1.40  Demodulation         : 0.12
% 2.98/1.40  BG Simplification    : 0.03
% 2.98/1.40  Subsumption          : 0.03
% 2.98/1.40  Abstraction          : 0.03
% 2.98/1.40  MUC search           : 0.00
% 2.98/1.40  Cooper               : 0.00
% 2.98/1.40  Total                : 0.64
% 2.98/1.40  Index Insertion      : 0.00
% 2.98/1.40  Index Deletion       : 0.00
% 2.98/1.40  Index Matching       : 0.00
% 2.98/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
