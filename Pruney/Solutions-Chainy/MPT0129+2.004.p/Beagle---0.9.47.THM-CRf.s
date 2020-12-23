%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:39 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   31 (  37 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   17 (  23 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_enumset1)).

tff(c_12,plain,(
    ! [A_14,B_15,C_16,D_17] : k2_xboole_0(k1_tarski(A_14),k1_enumset1(B_15,C_16,D_17)) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] : k2_xboole_0(k2_tarski(A_11,B_12),k1_tarski(C_13)) = k1_enumset1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_9,B_10] : k2_xboole_0(k1_tarski(A_9),k1_tarski(B_10)) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_33,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k2_xboole_0(A_22,B_23),C_24) = k2_xboole_0(A_22,k2_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_138,plain,(
    ! [A_38,B_39,C_40] : k2_xboole_0(k1_tarski(A_38),k2_xboole_0(k1_tarski(B_39),C_40)) = k2_xboole_0(k2_tarski(A_38,B_39),C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_33])).

tff(c_159,plain,(
    ! [A_38,A_9,B_10] : k2_xboole_0(k2_tarski(A_38,A_9),k1_tarski(B_10)) = k2_xboole_0(k1_tarski(A_38),k2_tarski(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_138])).

tff(c_225,plain,(
    ! [A_44,A_45,B_46] : k2_xboole_0(k1_tarski(A_44),k2_tarski(A_45,B_46)) = k1_enumset1(A_44,A_45,B_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_159])).

tff(c_48,plain,(
    ! [A_9,B_10,C_24] : k2_xboole_0(k1_tarski(A_9),k2_xboole_0(k1_tarski(B_10),C_24)) = k2_xboole_0(k2_tarski(A_9,B_10),C_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_33])).

tff(c_231,plain,(
    ! [A_9,A_44,A_45,B_46] : k2_xboole_0(k2_tarski(A_9,A_44),k2_tarski(A_45,B_46)) = k2_xboole_0(k1_tarski(A_9),k1_enumset1(A_44,A_45,B_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_48])).

tff(c_239,plain,(
    ! [A_9,A_44,A_45,B_46] : k2_xboole_0(k2_tarski(A_9,A_44),k2_tarski(A_45,B_46)) = k2_enumset1(A_9,A_44,A_45,B_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_231])).

tff(c_14,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.19  
% 1.98/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.19  %$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.98/1.19  
% 1.98/1.19  %Foreground sorts:
% 1.98/1.19  
% 1.98/1.19  
% 1.98/1.19  %Background operators:
% 1.98/1.19  
% 1.98/1.19  
% 1.98/1.19  %Foreground operators:
% 1.98/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.98/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.98/1.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.98/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.98/1.19  
% 1.98/1.20  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 1.98/1.20  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 1.98/1.20  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.98/1.20  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.98/1.20  tff(f_40, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_enumset1)).
% 1.98/1.20  tff(c_12, plain, (![A_14, B_15, C_16, D_17]: (k2_xboole_0(k1_tarski(A_14), k1_enumset1(B_15, C_16, D_17))=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.98/1.20  tff(c_10, plain, (![A_11, B_12, C_13]: (k2_xboole_0(k2_tarski(A_11, B_12), k1_tarski(C_13))=k1_enumset1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.98/1.20  tff(c_8, plain, (![A_9, B_10]: (k2_xboole_0(k1_tarski(A_9), k1_tarski(B_10))=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.98/1.20  tff(c_33, plain, (![A_22, B_23, C_24]: (k2_xboole_0(k2_xboole_0(A_22, B_23), C_24)=k2_xboole_0(A_22, k2_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.98/1.20  tff(c_138, plain, (![A_38, B_39, C_40]: (k2_xboole_0(k1_tarski(A_38), k2_xboole_0(k1_tarski(B_39), C_40))=k2_xboole_0(k2_tarski(A_38, B_39), C_40))), inference(superposition, [status(thm), theory('equality')], [c_8, c_33])).
% 1.98/1.20  tff(c_159, plain, (![A_38, A_9, B_10]: (k2_xboole_0(k2_tarski(A_38, A_9), k1_tarski(B_10))=k2_xboole_0(k1_tarski(A_38), k2_tarski(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_138])).
% 1.98/1.20  tff(c_225, plain, (![A_44, A_45, B_46]: (k2_xboole_0(k1_tarski(A_44), k2_tarski(A_45, B_46))=k1_enumset1(A_44, A_45, B_46))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_159])).
% 1.98/1.20  tff(c_48, plain, (![A_9, B_10, C_24]: (k2_xboole_0(k1_tarski(A_9), k2_xboole_0(k1_tarski(B_10), C_24))=k2_xboole_0(k2_tarski(A_9, B_10), C_24))), inference(superposition, [status(thm), theory('equality')], [c_8, c_33])).
% 1.98/1.20  tff(c_231, plain, (![A_9, A_44, A_45, B_46]: (k2_xboole_0(k2_tarski(A_9, A_44), k2_tarski(A_45, B_46))=k2_xboole_0(k1_tarski(A_9), k1_enumset1(A_44, A_45, B_46)))), inference(superposition, [status(thm), theory('equality')], [c_225, c_48])).
% 1.98/1.20  tff(c_239, plain, (![A_9, A_44, A_45, B_46]: (k2_xboole_0(k2_tarski(A_9, A_44), k2_tarski(A_45, B_46))=k2_enumset1(A_9, A_44, A_45, B_46))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_231])).
% 1.98/1.20  tff(c_14, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.98/1.20  tff(c_243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_239, c_14])).
% 1.98/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.20  
% 1.98/1.20  Inference rules
% 1.98/1.20  ----------------------
% 1.98/1.20  #Ref     : 0
% 1.98/1.20  #Sup     : 55
% 1.98/1.20  #Fact    : 0
% 1.98/1.20  #Define  : 0
% 1.98/1.20  #Split   : 0
% 1.98/1.20  #Chain   : 0
% 1.98/1.20  #Close   : 0
% 1.98/1.20  
% 1.98/1.20  Ordering : KBO
% 1.98/1.20  
% 1.98/1.20  Simplification rules
% 1.98/1.20  ----------------------
% 1.98/1.20  #Subsume      : 0
% 1.98/1.20  #Demod        : 45
% 1.98/1.20  #Tautology    : 29
% 1.98/1.20  #SimpNegUnit  : 0
% 1.98/1.20  #BackRed      : 1
% 1.98/1.20  
% 1.98/1.20  #Partial instantiations: 0
% 1.98/1.20  #Strategies tried      : 1
% 1.98/1.20  
% 1.98/1.20  Timing (in seconds)
% 1.98/1.20  ----------------------
% 1.98/1.20  Preprocessing        : 0.25
% 1.98/1.20  Parsing              : 0.14
% 1.98/1.20  CNF conversion       : 0.02
% 1.98/1.20  Main loop            : 0.18
% 1.98/1.20  Inferencing          : 0.07
% 1.98/1.20  Reduction            : 0.06
% 1.98/1.20  Demodulation         : 0.06
% 1.98/1.20  BG Simplification    : 0.01
% 1.98/1.20  Subsumption          : 0.02
% 1.98/1.20  Abstraction          : 0.01
% 1.98/1.20  MUC search           : 0.00
% 1.98/1.20  Cooper               : 0.00
% 1.98/1.20  Total                : 0.45
% 1.98/1.20  Index Insertion      : 0.00
% 1.98/1.20  Index Deletion       : 0.00
% 1.98/1.20  Index Matching       : 0.00
% 1.98/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
