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
% DateTime   : Thu Dec  3 09:45:43 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(c_4,plain,(
    ! [B_5,D_7,A_4,E_8,C_6,F_9] : k2_xboole_0(k1_enumset1(A_4,B_5,C_6),k1_enumset1(D_7,E_8,F_9)) = k4_enumset1(A_4,B_5,C_6,D_7,E_8,F_9) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] : k2_xboole_0(k2_tarski(A_13,B_14),k1_enumset1(C_15,D_16,E_17)) = k3_enumset1(A_13,B_14,C_15,D_16,E_17) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_10,B_11,C_12] : k2_xboole_0(k1_tarski(A_10),k2_tarski(B_11,C_12)) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_21,B_22,C_23] : k2_xboole_0(k2_xboole_0(A_21,B_22),C_23) = k2_xboole_0(A_21,k2_xboole_0(B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    ! [A_29,B_30,C_31,C_32] : k2_xboole_0(k1_tarski(A_29),k2_xboole_0(k2_tarski(B_30,C_31),C_32)) = k2_xboole_0(k1_enumset1(A_29,B_30,C_31),C_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_20])).

tff(c_64,plain,(
    ! [A_29,E_17,A_13,B_14,C_15,D_16] : k2_xboole_0(k1_enumset1(A_29,A_13,B_14),k1_enumset1(C_15,D_16,E_17)) = k2_xboole_0(k1_tarski(A_29),k3_enumset1(A_13,B_14,C_15,D_16,E_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_52])).

tff(c_99,plain,(
    ! [A_29,E_17,A_13,B_14,C_15,D_16] : k2_xboole_0(k1_tarski(A_29),k3_enumset1(A_13,B_14,C_15,D_16,E_17)) = k4_enumset1(A_29,A_13,B_14,C_15,D_16,E_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_64])).

tff(c_10,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k3_enumset1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n025.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 13:22:35 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.18/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.42  
% 2.06/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.43  %$ k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.06/1.43  
% 2.06/1.43  %Foreground sorts:
% 2.06/1.43  
% 2.06/1.43  
% 2.06/1.43  %Background operators:
% 2.06/1.43  
% 2.06/1.43  
% 2.06/1.43  %Foreground operators:
% 2.06/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.06/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.06/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.43  
% 2.06/1.44  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 2.06/1.44  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 2.06/1.44  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.06/1.44  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.06/1.44  tff(f_36, negated_conjecture, ~(![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 2.06/1.44  tff(c_4, plain, (![B_5, D_7, A_4, E_8, C_6, F_9]: (k2_xboole_0(k1_enumset1(A_4, B_5, C_6), k1_enumset1(D_7, E_8, F_9))=k4_enumset1(A_4, B_5, C_6, D_7, E_8, F_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.06/1.44  tff(c_8, plain, (![E_17, A_13, B_14, C_15, D_16]: (k2_xboole_0(k2_tarski(A_13, B_14), k1_enumset1(C_15, D_16, E_17))=k3_enumset1(A_13, B_14, C_15, D_16, E_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.44  tff(c_6, plain, (![A_10, B_11, C_12]: (k2_xboole_0(k1_tarski(A_10), k2_tarski(B_11, C_12))=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.44  tff(c_20, plain, (![A_21, B_22, C_23]: (k2_xboole_0(k2_xboole_0(A_21, B_22), C_23)=k2_xboole_0(A_21, k2_xboole_0(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.44  tff(c_52, plain, (![A_29, B_30, C_31, C_32]: (k2_xboole_0(k1_tarski(A_29), k2_xboole_0(k2_tarski(B_30, C_31), C_32))=k2_xboole_0(k1_enumset1(A_29, B_30, C_31), C_32))), inference(superposition, [status(thm), theory('equality')], [c_6, c_20])).
% 2.06/1.44  tff(c_64, plain, (![A_29, E_17, A_13, B_14, C_15, D_16]: (k2_xboole_0(k1_enumset1(A_29, A_13, B_14), k1_enumset1(C_15, D_16, E_17))=k2_xboole_0(k1_tarski(A_29), k3_enumset1(A_13, B_14, C_15, D_16, E_17)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_52])).
% 2.06/1.44  tff(c_99, plain, (![A_29, E_17, A_13, B_14, C_15, D_16]: (k2_xboole_0(k1_tarski(A_29), k3_enumset1(A_13, B_14, C_15, D_16, E_17))=k4_enumset1(A_29, A_13, B_14, C_15, D_16, E_17))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_64])).
% 2.06/1.44  tff(c_10, plain, (k2_xboole_0(k1_tarski('#skF_1'), k3_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.06/1.44  tff(c_102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_99, c_10])).
% 2.06/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.44  
% 2.06/1.44  Inference rules
% 2.06/1.44  ----------------------
% 2.06/1.44  #Ref     : 0
% 2.06/1.44  #Sup     : 22
% 2.06/1.44  #Fact    : 0
% 2.06/1.44  #Define  : 0
% 2.06/1.44  #Split   : 0
% 2.06/1.44  #Chain   : 0
% 2.06/1.44  #Close   : 0
% 2.06/1.44  
% 2.06/1.44  Ordering : KBO
% 2.06/1.44  
% 2.06/1.44  Simplification rules
% 2.06/1.44  ----------------------
% 2.06/1.44  #Subsume      : 0
% 2.06/1.44  #Demod        : 14
% 2.06/1.44  #Tautology    : 16
% 2.06/1.44  #SimpNegUnit  : 0
% 2.06/1.44  #BackRed      : 1
% 2.06/1.44  
% 2.06/1.44  #Partial instantiations: 0
% 2.06/1.44  #Strategies tried      : 1
% 2.06/1.44  
% 2.06/1.44  Timing (in seconds)
% 2.06/1.44  ----------------------
% 2.06/1.45  Preprocessing        : 0.43
% 2.06/1.45  Parsing              : 0.23
% 2.06/1.45  CNF conversion       : 0.03
% 2.06/1.45  Main loop            : 0.22
% 2.06/1.45  Inferencing          : 0.11
% 2.06/1.45  Reduction            : 0.06
% 2.06/1.45  Demodulation         : 0.05
% 2.06/1.45  BG Simplification    : 0.02
% 2.06/1.45  Subsumption          : 0.02
% 2.06/1.45  Abstraction          : 0.02
% 2.06/1.45  MUC search           : 0.00
% 2.06/1.45  Cooper               : 0.00
% 2.06/1.45  Total                : 0.69
% 2.06/1.45  Index Insertion      : 0.00
% 2.06/1.45  Index Deletion       : 0.00
% 2.06/1.45  Index Matching       : 0.00
% 2.06/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
