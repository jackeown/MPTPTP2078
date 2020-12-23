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
% DateTime   : Thu Dec  3 09:45:42 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(c_14,plain,(
    ! [E_21,D_20,C_19,B_18,A_17] : k2_xboole_0(k1_enumset1(A_17,B_18,C_19),k2_tarski(D_20,E_21)) = k3_enumset1(A_17,B_18,C_19,D_20,E_21) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),k1_tarski(B_9)) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_88,plain,(
    ! [A_34,B_35,C_36,D_37] : k2_xboole_0(k1_enumset1(A_34,B_35,C_36),k1_tarski(D_37)) = k2_enumset1(A_34,B_35,C_36,D_37) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k2_xboole_0(A_3,B_4),C_5) = k2_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_232,plain,(
    ! [B_63,A_61,D_62,C_65,C_64] : k2_xboole_0(k1_enumset1(A_61,B_63,C_65),k2_xboole_0(k1_tarski(D_62),C_64)) = k2_xboole_0(k2_enumset1(A_61,B_63,C_65,D_62),C_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_4])).

tff(c_250,plain,(
    ! [B_63,A_61,A_8,C_65,B_9] : k2_xboole_0(k2_enumset1(A_61,B_63,C_65,A_8),k1_tarski(B_9)) = k2_xboole_0(k1_enumset1(A_61,B_63,C_65),k2_tarski(A_8,B_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_232])).

tff(c_254,plain,(
    ! [B_63,A_61,A_8,C_65,B_9] : k2_xboole_0(k2_enumset1(A_61,B_63,C_65,A_8),k1_tarski(B_9)) = k3_enumset1(A_61,B_63,C_65,A_8,B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_250])).

tff(c_16,plain,(
    k2_xboole_0(k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_tarski('#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:21:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.33  
% 2.20/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.34  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.20/1.34  
% 2.20/1.34  %Foreground sorts:
% 2.20/1.34  
% 2.20/1.34  
% 2.20/1.34  %Background operators:
% 2.20/1.34  
% 2.20/1.34  
% 2.20/1.34  %Foreground operators:
% 2.20/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.20/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.20/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.20/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.20/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.20/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.20/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.20/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.20/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.20/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.20/1.34  
% 2.20/1.35  tff(f_39, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_enumset1)).
% 2.20/1.35  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.20/1.35  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.20/1.35  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.20/1.35  tff(f_42, negated_conjecture, ~(![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 2.20/1.35  tff(c_14, plain, (![E_21, D_20, C_19, B_18, A_17]: (k2_xboole_0(k1_enumset1(A_17, B_18, C_19), k2_tarski(D_20, E_21))=k3_enumset1(A_17, B_18, C_19, D_20, E_21))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.20/1.35  tff(c_8, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(B_9))=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.20/1.35  tff(c_88, plain, (![A_34, B_35, C_36, D_37]: (k2_xboole_0(k1_enumset1(A_34, B_35, C_36), k1_tarski(D_37))=k2_enumset1(A_34, B_35, C_36, D_37))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.20/1.35  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k2_xboole_0(A_3, B_4), C_5)=k2_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.35  tff(c_232, plain, (![B_63, A_61, D_62, C_65, C_64]: (k2_xboole_0(k1_enumset1(A_61, B_63, C_65), k2_xboole_0(k1_tarski(D_62), C_64))=k2_xboole_0(k2_enumset1(A_61, B_63, C_65, D_62), C_64))), inference(superposition, [status(thm), theory('equality')], [c_88, c_4])).
% 2.20/1.35  tff(c_250, plain, (![B_63, A_61, A_8, C_65, B_9]: (k2_xboole_0(k2_enumset1(A_61, B_63, C_65, A_8), k1_tarski(B_9))=k2_xboole_0(k1_enumset1(A_61, B_63, C_65), k2_tarski(A_8, B_9)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_232])).
% 2.20/1.35  tff(c_254, plain, (![B_63, A_61, A_8, C_65, B_9]: (k2_xboole_0(k2_enumset1(A_61, B_63, C_65, A_8), k1_tarski(B_9))=k3_enumset1(A_61, B_63, C_65, A_8, B_9))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_250])).
% 2.20/1.35  tff(c_16, plain, (k2_xboole_0(k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_tarski('#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.20/1.35  tff(c_257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_254, c_16])).
% 2.20/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.35  
% 2.20/1.35  Inference rules
% 2.20/1.35  ----------------------
% 2.20/1.35  #Ref     : 0
% 2.20/1.35  #Sup     : 61
% 2.20/1.35  #Fact    : 0
% 2.20/1.35  #Define  : 0
% 2.20/1.35  #Split   : 0
% 2.20/1.35  #Chain   : 0
% 2.20/1.35  #Close   : 0
% 2.20/1.35  
% 2.20/1.35  Ordering : KBO
% 2.20/1.35  
% 2.20/1.35  Simplification rules
% 2.20/1.35  ----------------------
% 2.20/1.35  #Subsume      : 0
% 2.20/1.35  #Demod        : 23
% 2.20/1.35  #Tautology    : 36
% 2.20/1.35  #SimpNegUnit  : 0
% 2.20/1.35  #BackRed      : 1
% 2.20/1.35  
% 2.20/1.35  #Partial instantiations: 0
% 2.20/1.35  #Strategies tried      : 1
% 2.20/1.35  
% 2.20/1.35  Timing (in seconds)
% 2.20/1.35  ----------------------
% 2.20/1.36  Preprocessing        : 0.32
% 2.20/1.36  Parsing              : 0.17
% 2.20/1.36  CNF conversion       : 0.02
% 2.20/1.36  Main loop            : 0.23
% 2.20/1.36  Inferencing          : 0.10
% 2.20/1.36  Reduction            : 0.07
% 2.20/1.36  Demodulation         : 0.06
% 2.20/1.36  BG Simplification    : 0.02
% 2.20/1.36  Subsumption          : 0.03
% 2.20/1.36  Abstraction          : 0.02
% 2.20/1.36  MUC search           : 0.00
% 2.20/1.36  Cooper               : 0.00
% 2.20/1.36  Total                : 0.58
% 2.20/1.36  Index Insertion      : 0.00
% 2.20/1.36  Index Deletion       : 0.00
% 2.20/1.36  Index Matching       : 0.00
% 2.20/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
