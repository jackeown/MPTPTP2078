%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:42 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(c_12,plain,(
    ! [B_16,A_15,D_18,E_19,C_17] : k2_xboole_0(k1_tarski(A_15),k2_enumset1(B_16,C_17,D_18,E_19)) = k3_enumset1(A_15,B_16,C_17,D_18,E_19) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13,D_14] : k2_xboole_0(k1_tarski(A_11),k1_enumset1(B_12,C_13,D_14)) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),k1_tarski(B_7)) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [A_27,B_28,C_29] : k2_xboole_0(k2_xboole_0(A_27,B_28),C_29) = k2_xboole_0(A_27,k2_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_89,plain,(
    ! [A_39,B_40,C_41] : k2_xboole_0(k1_tarski(A_39),k2_xboole_0(k1_tarski(B_40),C_41)) = k2_xboole_0(k2_tarski(A_39,B_40),C_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_42])).

tff(c_110,plain,(
    ! [D_14,A_39,B_12,A_11,C_13] : k2_xboole_0(k2_tarski(A_39,A_11),k1_enumset1(B_12,C_13,D_14)) = k2_xboole_0(k1_tarski(A_39),k2_enumset1(A_11,B_12,C_13,D_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_89])).

tff(c_117,plain,(
    ! [D_14,A_39,B_12,A_11,C_13] : k2_xboole_0(k2_tarski(A_39,A_11),k1_enumset1(B_12,C_13,D_14)) = k3_enumset1(A_39,A_11,B_12,C_13,D_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_110])).

tff(c_14,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_enumset1('#skF_3','#skF_4','#skF_5')) != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:17:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.17  
% 1.83/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.18  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.83/1.18  
% 1.83/1.18  %Foreground sorts:
% 1.83/1.18  
% 1.83/1.18  
% 1.83/1.18  %Background operators:
% 1.83/1.18  
% 1.83/1.18  
% 1.83/1.18  %Foreground operators:
% 1.83/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.83/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.83/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.83/1.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.83/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.83/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.83/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.83/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.83/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.83/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.83/1.18  
% 1.83/1.18  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 1.83/1.18  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 1.83/1.18  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.83/1.18  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.83/1.18  tff(f_40, negated_conjecture, ~(![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 1.83/1.18  tff(c_12, plain, (![B_16, A_15, D_18, E_19, C_17]: (k2_xboole_0(k1_tarski(A_15), k2_enumset1(B_16, C_17, D_18, E_19))=k3_enumset1(A_15, B_16, C_17, D_18, E_19))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.83/1.18  tff(c_10, plain, (![A_11, B_12, C_13, D_14]: (k2_xboole_0(k1_tarski(A_11), k1_enumset1(B_12, C_13, D_14))=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.83/1.18  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(B_7))=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.18  tff(c_42, plain, (![A_27, B_28, C_29]: (k2_xboole_0(k2_xboole_0(A_27, B_28), C_29)=k2_xboole_0(A_27, k2_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.83/1.18  tff(c_89, plain, (![A_39, B_40, C_41]: (k2_xboole_0(k1_tarski(A_39), k2_xboole_0(k1_tarski(B_40), C_41))=k2_xboole_0(k2_tarski(A_39, B_40), C_41))), inference(superposition, [status(thm), theory('equality')], [c_6, c_42])).
% 1.83/1.18  tff(c_110, plain, (![D_14, A_39, B_12, A_11, C_13]: (k2_xboole_0(k2_tarski(A_39, A_11), k1_enumset1(B_12, C_13, D_14))=k2_xboole_0(k1_tarski(A_39), k2_enumset1(A_11, B_12, C_13, D_14)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_89])).
% 1.83/1.18  tff(c_117, plain, (![D_14, A_39, B_12, A_11, C_13]: (k2_xboole_0(k2_tarski(A_39, A_11), k1_enumset1(B_12, C_13, D_14))=k3_enumset1(A_39, A_11, B_12, C_13, D_14))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_110])).
% 1.83/1.18  tff(c_14, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_enumset1('#skF_3', '#skF_4', '#skF_5'))!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.83/1.18  tff(c_190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_14])).
% 1.83/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.18  
% 1.83/1.18  Inference rules
% 1.83/1.18  ----------------------
% 1.83/1.18  #Ref     : 0
% 1.83/1.18  #Sup     : 44
% 1.83/1.18  #Fact    : 0
% 1.83/1.18  #Define  : 0
% 1.83/1.18  #Split   : 0
% 1.83/1.18  #Chain   : 0
% 1.83/1.18  #Close   : 0
% 1.83/1.18  
% 1.83/1.18  Ordering : KBO
% 1.83/1.18  
% 1.83/1.18  Simplification rules
% 1.83/1.18  ----------------------
% 1.83/1.18  #Subsume      : 0
% 1.83/1.18  #Demod        : 17
% 1.83/1.18  #Tautology    : 26
% 1.83/1.18  #SimpNegUnit  : 0
% 1.83/1.18  #BackRed      : 1
% 1.83/1.18  
% 1.83/1.18  #Partial instantiations: 0
% 1.83/1.18  #Strategies tried      : 1
% 1.83/1.18  
% 1.83/1.18  Timing (in seconds)
% 1.83/1.18  ----------------------
% 1.83/1.19  Preprocessing        : 0.25
% 1.83/1.19  Parsing              : 0.13
% 1.83/1.19  CNF conversion       : 0.02
% 1.83/1.19  Main loop            : 0.16
% 1.83/1.19  Inferencing          : 0.07
% 1.83/1.19  Reduction            : 0.05
% 1.83/1.19  Demodulation         : 0.04
% 1.83/1.19  BG Simplification    : 0.01
% 1.83/1.19  Subsumption          : 0.02
% 1.83/1.19  Abstraction          : 0.01
% 1.83/1.19  MUC search           : 0.00
% 1.83/1.19  Cooper               : 0.00
% 1.83/1.19  Total                : 0.43
% 1.83/1.19  Index Insertion      : 0.00
% 1.83/1.19  Index Deletion       : 0.00
% 1.83/1.19  Index Matching       : 0.00
% 1.83/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
