%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:42 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   34 (  36 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) = k2_xboole_0(A,k2_xboole_0(k2_xboole_0(B,C),D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(c_14,plain,(
    ! [A_21,B_22,D_24,C_23,E_25] : k2_xboole_0(k2_tarski(A_21,B_22),k1_enumset1(C_23,D_24,E_25)) = k3_enumset1(A_21,B_22,C_23,D_24,E_25) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11] : k2_xboole_0(k2_tarski(A_9,B_10),k1_tarski(C_11)) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_12,B_13,C_14,D_15] : k2_xboole_0(k1_enumset1(A_12,B_13,C_14),k1_tarski(D_15)) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_7,B_8] : k2_xboole_0(k1_tarski(A_7),k1_tarski(B_8)) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_47,B_48,C_49,D_50] : k2_xboole_0(k2_xboole_0(k2_xboole_0(A_47,B_48),C_49),D_50) = k2_xboole_0(A_47,k2_xboole_0(k2_xboole_0(B_48,C_49),D_50)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_283,plain,(
    ! [C_70,C_72,D_68,B_69,A_71] : k2_xboole_0(k2_tarski(A_71,B_69),k2_xboole_0(k2_xboole_0(k1_tarski(C_70),C_72),D_68)) = k2_xboole_0(k2_xboole_0(k1_enumset1(A_71,B_69,C_70),C_72),D_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_77])).

tff(c_320,plain,(
    ! [A_7,D_68,B_69,A_71,B_8] : k2_xboole_0(k2_xboole_0(k1_enumset1(A_71,B_69,A_7),k1_tarski(B_8)),D_68) = k2_xboole_0(k2_tarski(A_71,B_69),k2_xboole_0(k2_tarski(A_7,B_8),D_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_283])).

tff(c_329,plain,(
    ! [D_74,B_73,A_77,A_75,B_76] : k2_xboole_0(k2_tarski(A_77,B_76),k2_xboole_0(k2_tarski(A_75,B_73),D_74)) = k2_xboole_0(k2_enumset1(A_77,B_76,A_75,B_73),D_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_320])).

tff(c_359,plain,(
    ! [C_11,A_77,B_10,A_9,B_76] : k2_xboole_0(k2_enumset1(A_77,B_76,A_9,B_10),k1_tarski(C_11)) = k2_xboole_0(k2_tarski(A_77,B_76),k1_enumset1(A_9,B_10,C_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_329])).

tff(c_364,plain,(
    ! [C_11,A_77,B_10,A_9,B_76] : k2_xboole_0(k2_enumset1(A_77,B_76,A_9,B_10),k1_tarski(C_11)) = k3_enumset1(A_77,B_76,A_9,B_10,C_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_359])).

tff(c_16,plain,(
    k2_xboole_0(k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_tarski('#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:55:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.35  
% 2.58/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.35  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.58/1.35  
% 2.58/1.35  %Foreground sorts:
% 2.58/1.35  
% 2.58/1.35  
% 2.58/1.35  %Background operators:
% 2.58/1.35  
% 2.58/1.35  
% 2.58/1.35  %Foreground operators:
% 2.58/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.58/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.58/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.58/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.58/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.58/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.58/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.58/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.58/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.58/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.58/1.35  
% 2.58/1.36  tff(f_39, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 2.58/1.36  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.58/1.36  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.58/1.36  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.58/1.36  tff(f_27, axiom, (![A, B, C, D]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(A, B), C), D) = k2_xboole_0(A, k2_xboole_0(k2_xboole_0(B, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_xboole_1)).
% 2.58/1.36  tff(f_42, negated_conjecture, ~(![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 2.58/1.36  tff(c_14, plain, (![A_21, B_22, D_24, C_23, E_25]: (k2_xboole_0(k2_tarski(A_21, B_22), k1_enumset1(C_23, D_24, E_25))=k3_enumset1(A_21, B_22, C_23, D_24, E_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.58/1.36  tff(c_8, plain, (![A_9, B_10, C_11]: (k2_xboole_0(k2_tarski(A_9, B_10), k1_tarski(C_11))=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.58/1.36  tff(c_10, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k1_enumset1(A_12, B_13, C_14), k1_tarski(D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.58/1.36  tff(c_6, plain, (![A_7, B_8]: (k2_xboole_0(k1_tarski(A_7), k1_tarski(B_8))=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.36  tff(c_77, plain, (![A_47, B_48, C_49, D_50]: (k2_xboole_0(k2_xboole_0(k2_xboole_0(A_47, B_48), C_49), D_50)=k2_xboole_0(A_47, k2_xboole_0(k2_xboole_0(B_48, C_49), D_50)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.58/1.36  tff(c_283, plain, (![C_70, C_72, D_68, B_69, A_71]: (k2_xboole_0(k2_tarski(A_71, B_69), k2_xboole_0(k2_xboole_0(k1_tarski(C_70), C_72), D_68))=k2_xboole_0(k2_xboole_0(k1_enumset1(A_71, B_69, C_70), C_72), D_68))), inference(superposition, [status(thm), theory('equality')], [c_8, c_77])).
% 2.58/1.36  tff(c_320, plain, (![A_7, D_68, B_69, A_71, B_8]: (k2_xboole_0(k2_xboole_0(k1_enumset1(A_71, B_69, A_7), k1_tarski(B_8)), D_68)=k2_xboole_0(k2_tarski(A_71, B_69), k2_xboole_0(k2_tarski(A_7, B_8), D_68)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_283])).
% 2.58/1.36  tff(c_329, plain, (![D_74, B_73, A_77, A_75, B_76]: (k2_xboole_0(k2_tarski(A_77, B_76), k2_xboole_0(k2_tarski(A_75, B_73), D_74))=k2_xboole_0(k2_enumset1(A_77, B_76, A_75, B_73), D_74))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_320])).
% 2.58/1.36  tff(c_359, plain, (![C_11, A_77, B_10, A_9, B_76]: (k2_xboole_0(k2_enumset1(A_77, B_76, A_9, B_10), k1_tarski(C_11))=k2_xboole_0(k2_tarski(A_77, B_76), k1_enumset1(A_9, B_10, C_11)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_329])).
% 2.58/1.36  tff(c_364, plain, (![C_11, A_77, B_10, A_9, B_76]: (k2_xboole_0(k2_enumset1(A_77, B_76, A_9, B_10), k1_tarski(C_11))=k3_enumset1(A_77, B_76, A_9, B_10, C_11))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_359])).
% 2.58/1.36  tff(c_16, plain, (k2_xboole_0(k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_tarski('#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.58/1.36  tff(c_427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_364, c_16])).
% 2.58/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.36  
% 2.58/1.36  Inference rules
% 2.58/1.36  ----------------------
% 2.58/1.36  #Ref     : 0
% 2.58/1.36  #Sup     : 107
% 2.58/1.36  #Fact    : 0
% 2.58/1.36  #Define  : 0
% 2.58/1.36  #Split   : 0
% 2.58/1.36  #Chain   : 0
% 2.58/1.36  #Close   : 0
% 2.58/1.36  
% 2.58/1.36  Ordering : KBO
% 2.58/1.36  
% 2.58/1.36  Simplification rules
% 2.58/1.36  ----------------------
% 2.58/1.36  #Subsume      : 0
% 2.58/1.36  #Demod        : 90
% 2.58/1.36  #Tautology    : 47
% 2.58/1.36  #SimpNegUnit  : 0
% 2.58/1.36  #BackRed      : 1
% 2.58/1.36  
% 2.58/1.36  #Partial instantiations: 0
% 2.58/1.36  #Strategies tried      : 1
% 2.58/1.36  
% 2.58/1.36  Timing (in seconds)
% 2.58/1.36  ----------------------
% 2.58/1.37  Preprocessing        : 0.28
% 2.58/1.37  Parsing              : 0.16
% 2.58/1.37  CNF conversion       : 0.02
% 2.58/1.37  Main loop            : 0.32
% 2.58/1.37  Inferencing          : 0.13
% 2.58/1.37  Reduction            : 0.13
% 2.58/1.37  Demodulation         : 0.11
% 2.58/1.37  BG Simplification    : 0.02
% 2.58/1.37  Subsumption          : 0.03
% 2.58/1.37  Abstraction          : 0.03
% 2.58/1.37  MUC search           : 0.00
% 2.58/1.37  Cooper               : 0.00
% 2.58/1.37  Total                : 0.63
% 2.58/1.37  Index Insertion      : 0.00
% 2.58/1.37  Index Deletion       : 0.00
% 2.58/1.37  Index Matching       : 0.00
% 2.58/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
