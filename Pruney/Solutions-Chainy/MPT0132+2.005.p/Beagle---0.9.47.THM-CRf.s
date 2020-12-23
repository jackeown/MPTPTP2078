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
% DateTime   : Thu Dec  3 09:45:41 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.55s
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
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(c_14,plain,(
    ! [E_21,D_20,C_19,B_18,A_17] : k2_xboole_0(k1_tarski(A_17),k2_enumset1(B_18,C_19,D_20,E_21)) = k3_enumset1(A_17,B_18,C_19,D_20,E_21) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_13,B_14,C_15,D_16] : k2_xboole_0(k1_tarski(A_13),k1_enumset1(B_14,C_15,D_16)) = k2_enumset1(A_13,B_14,C_15,D_16) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    ! [A_28,B_29,C_30] : k2_xboole_0(k2_xboole_0(A_28,B_29),C_30) = k2_xboole_0(A_28,k2_xboole_0(B_29,C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_197,plain,(
    ! [A_44,B_45,C_46] : k2_xboole_0(k1_tarski(A_44),k2_xboole_0(k1_tarski(B_45),C_46)) = k2_xboole_0(k2_tarski(A_44,B_45),C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_44])).

tff(c_215,plain,(
    ! [A_13,B_14,A_44,C_15,D_16] : k2_xboole_0(k2_tarski(A_44,A_13),k1_enumset1(B_14,C_15,D_16)) = k2_xboole_0(k1_tarski(A_44),k2_enumset1(A_13,B_14,C_15,D_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_197])).

tff(c_517,plain,(
    ! [A_13,B_14,A_44,C_15,D_16] : k2_xboole_0(k2_tarski(A_44,A_13),k1_enumset1(B_14,C_15,D_16)) = k3_enumset1(A_44,A_13,B_14,C_15,D_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_215])).

tff(c_16,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_enumset1('#skF_3','#skF_4','#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:15:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.45  
% 2.55/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.45  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.55/1.45  
% 2.55/1.45  %Foreground sorts:
% 2.55/1.45  
% 2.55/1.45  
% 2.55/1.45  %Background operators:
% 2.55/1.45  
% 2.55/1.45  
% 2.55/1.45  %Foreground operators:
% 2.55/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.55/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.55/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.55/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.55/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.55/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.55/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.55/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.55/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.55/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.55/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.55/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.55/1.45  
% 2.55/1.46  tff(f_39, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 2.55/1.46  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 2.55/1.46  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.55/1.46  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.55/1.46  tff(f_42, negated_conjecture, ~(![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 2.55/1.46  tff(c_14, plain, (![E_21, D_20, C_19, B_18, A_17]: (k2_xboole_0(k1_tarski(A_17), k2_enumset1(B_18, C_19, D_20, E_21))=k3_enumset1(A_17, B_18, C_19, D_20, E_21))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.55/1.46  tff(c_12, plain, (![A_13, B_14, C_15, D_16]: (k2_xboole_0(k1_tarski(A_13), k1_enumset1(B_14, C_15, D_16))=k2_enumset1(A_13, B_14, C_15, D_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.55/1.46  tff(c_10, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(B_12))=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.55/1.46  tff(c_44, plain, (![A_28, B_29, C_30]: (k2_xboole_0(k2_xboole_0(A_28, B_29), C_30)=k2_xboole_0(A_28, k2_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.55/1.46  tff(c_197, plain, (![A_44, B_45, C_46]: (k2_xboole_0(k1_tarski(A_44), k2_xboole_0(k1_tarski(B_45), C_46))=k2_xboole_0(k2_tarski(A_44, B_45), C_46))), inference(superposition, [status(thm), theory('equality')], [c_10, c_44])).
% 2.55/1.46  tff(c_215, plain, (![A_13, B_14, A_44, C_15, D_16]: (k2_xboole_0(k2_tarski(A_44, A_13), k1_enumset1(B_14, C_15, D_16))=k2_xboole_0(k1_tarski(A_44), k2_enumset1(A_13, B_14, C_15, D_16)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_197])).
% 2.55/1.46  tff(c_517, plain, (![A_13, B_14, A_44, C_15, D_16]: (k2_xboole_0(k2_tarski(A_44, A_13), k1_enumset1(B_14, C_15, D_16))=k3_enumset1(A_44, A_13, B_14, C_15, D_16))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_215])).
% 2.55/1.46  tff(c_16, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_enumset1('#skF_3', '#skF_4', '#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.55/1.46  tff(c_520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_517, c_16])).
% 2.55/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.46  
% 2.55/1.46  Inference rules
% 2.55/1.46  ----------------------
% 2.55/1.46  #Ref     : 0
% 2.55/1.46  #Sup     : 123
% 2.55/1.46  #Fact    : 0
% 2.55/1.46  #Define  : 0
% 2.55/1.46  #Split   : 0
% 2.55/1.46  #Chain   : 0
% 2.55/1.46  #Close   : 0
% 2.55/1.46  
% 2.55/1.46  Ordering : KBO
% 2.55/1.46  
% 2.55/1.46  Simplification rules
% 2.55/1.46  ----------------------
% 2.55/1.46  #Subsume      : 0
% 2.55/1.46  #Demod        : 111
% 2.55/1.46  #Tautology    : 57
% 2.55/1.46  #SimpNegUnit  : 0
% 2.55/1.46  #BackRed      : 1
% 2.55/1.46  
% 2.55/1.46  #Partial instantiations: 0
% 2.55/1.46  #Strategies tried      : 1
% 2.55/1.46  
% 2.55/1.46  Timing (in seconds)
% 2.55/1.46  ----------------------
% 2.55/1.47  Preprocessing        : 0.34
% 2.55/1.47  Parsing              : 0.20
% 2.55/1.47  CNF conversion       : 0.02
% 2.55/1.47  Main loop            : 0.29
% 2.55/1.47  Inferencing          : 0.12
% 2.55/1.47  Reduction            : 0.10
% 2.55/1.47  Demodulation         : 0.09
% 2.55/1.47  BG Simplification    : 0.02
% 2.55/1.47  Subsumption          : 0.03
% 2.55/1.47  Abstraction          : 0.02
% 2.55/1.47  MUC search           : 0.00
% 2.55/1.47  Cooper               : 0.00
% 2.55/1.47  Total                : 0.65
% 2.55/1.47  Index Insertion      : 0.00
% 2.55/1.47  Index Deletion       : 0.00
% 2.55/1.47  Index Matching       : 0.00
% 2.55/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
