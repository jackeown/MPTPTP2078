%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:49 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

tff(c_12,plain,(
    ! [A_23,B_24,F_28,D_26,G_29,C_25,E_27] : k2_xboole_0(k2_tarski(A_23,B_24),k3_enumset1(C_25,D_26,E_27,F_28,G_29)) = k5_enumset1(A_23,B_24,C_25,D_26,E_27,F_28,G_29) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [E_22,D_21,A_18,C_20,B_19] : k2_xboole_0(k1_tarski(A_18),k2_enumset1(B_19,C_20,D_21,E_22)) = k3_enumset1(A_18,B_19,C_20,D_21,E_22) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_15,B_16,C_17] : k2_xboole_0(k2_tarski(A_15,B_16),k1_tarski(C_17)) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [A_33,B_34,C_35] : k2_xboole_0(k2_xboole_0(A_33,B_34),C_35) = k2_xboole_0(A_33,k2_xboole_0(B_34,C_35)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    ! [A_45,B_46,C_47,C_48] : k2_xboole_0(k2_tarski(A_45,B_46),k2_xboole_0(k1_tarski(C_47),C_48)) = k2_xboole_0(k1_enumset1(A_45,B_46,C_47),C_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_24])).

tff(c_80,plain,(
    ! [E_22,D_21,A_45,B_46,A_18,C_20,B_19] : k2_xboole_0(k1_enumset1(A_45,B_46,A_18),k2_enumset1(B_19,C_20,D_21,E_22)) = k2_xboole_0(k2_tarski(A_45,B_46),k3_enumset1(A_18,B_19,C_20,D_21,E_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_68])).

tff(c_212,plain,(
    ! [E_22,D_21,A_45,B_46,A_18,C_20,B_19] : k2_xboole_0(k1_enumset1(A_45,B_46,A_18),k2_enumset1(B_19,C_20,D_21,E_22)) = k5_enumset1(A_45,B_46,A_18,B_19,C_20,D_21,E_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_80])).

tff(c_14,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k2_enumset1('#skF_4','#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:24:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.22  
% 2.02/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.22  %$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.02/1.22  
% 2.02/1.22  %Foreground sorts:
% 2.02/1.22  
% 2.02/1.22  
% 2.02/1.22  %Background operators:
% 2.02/1.22  
% 2.02/1.22  
% 2.02/1.22  %Foreground operators:
% 2.02/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.02/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.02/1.22  tff('#skF_7', type, '#skF_7': $i).
% 2.02/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.02/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.22  tff('#skF_5', type, '#skF_5': $i).
% 2.02/1.22  tff('#skF_6', type, '#skF_6': $i).
% 2.02/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.02/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.02/1.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.22  
% 2.02/1.23  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_enumset1)).
% 2.02/1.23  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 2.02/1.23  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.02/1.23  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.02/1.23  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 2.02/1.23  tff(c_12, plain, (![A_23, B_24, F_28, D_26, G_29, C_25, E_27]: (k2_xboole_0(k2_tarski(A_23, B_24), k3_enumset1(C_25, D_26, E_27, F_28, G_29))=k5_enumset1(A_23, B_24, C_25, D_26, E_27, F_28, G_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.02/1.23  tff(c_10, plain, (![E_22, D_21, A_18, C_20, B_19]: (k2_xboole_0(k1_tarski(A_18), k2_enumset1(B_19, C_20, D_21, E_22))=k3_enumset1(A_18, B_19, C_20, D_21, E_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.23  tff(c_8, plain, (![A_15, B_16, C_17]: (k2_xboole_0(k2_tarski(A_15, B_16), k1_tarski(C_17))=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.23  tff(c_24, plain, (![A_33, B_34, C_35]: (k2_xboole_0(k2_xboole_0(A_33, B_34), C_35)=k2_xboole_0(A_33, k2_xboole_0(B_34, C_35)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.23  tff(c_68, plain, (![A_45, B_46, C_47, C_48]: (k2_xboole_0(k2_tarski(A_45, B_46), k2_xboole_0(k1_tarski(C_47), C_48))=k2_xboole_0(k1_enumset1(A_45, B_46, C_47), C_48))), inference(superposition, [status(thm), theory('equality')], [c_8, c_24])).
% 2.02/1.23  tff(c_80, plain, (![E_22, D_21, A_45, B_46, A_18, C_20, B_19]: (k2_xboole_0(k1_enumset1(A_45, B_46, A_18), k2_enumset1(B_19, C_20, D_21, E_22))=k2_xboole_0(k2_tarski(A_45, B_46), k3_enumset1(A_18, B_19, C_20, D_21, E_22)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_68])).
% 2.02/1.23  tff(c_212, plain, (![E_22, D_21, A_45, B_46, A_18, C_20, B_19]: (k2_xboole_0(k1_enumset1(A_45, B_46, A_18), k2_enumset1(B_19, C_20, D_21, E_22))=k5_enumset1(A_45, B_46, A_18, B_19, C_20, D_21, E_22))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_80])).
% 2.02/1.23  tff(c_14, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k2_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.02/1.23  tff(c_215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_212, c_14])).
% 2.02/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.23  
% 2.02/1.23  Inference rules
% 2.02/1.23  ----------------------
% 2.02/1.23  #Ref     : 0
% 2.02/1.23  #Sup     : 51
% 2.02/1.23  #Fact    : 0
% 2.02/1.23  #Define  : 0
% 2.02/1.23  #Split   : 0
% 2.02/1.23  #Chain   : 0
% 2.02/1.23  #Close   : 0
% 2.02/1.23  
% 2.02/1.23  Ordering : KBO
% 2.02/1.23  
% 2.02/1.23  Simplification rules
% 2.02/1.23  ----------------------
% 2.02/1.23  #Subsume      : 0
% 2.02/1.23  #Demod        : 23
% 2.02/1.23  #Tautology    : 30
% 2.02/1.23  #SimpNegUnit  : 0
% 2.02/1.23  #BackRed      : 1
% 2.02/1.23  
% 2.02/1.23  #Partial instantiations: 0
% 2.02/1.23  #Strategies tried      : 1
% 2.02/1.23  
% 2.02/1.23  Timing (in seconds)
% 2.02/1.23  ----------------------
% 2.02/1.23  Preprocessing        : 0.27
% 2.02/1.23  Parsing              : 0.15
% 2.02/1.23  CNF conversion       : 0.02
% 2.02/1.23  Main loop            : 0.20
% 2.02/1.23  Inferencing          : 0.09
% 2.02/1.23  Reduction            : 0.06
% 2.02/1.23  Demodulation         : 0.05
% 2.02/1.23  BG Simplification    : 0.02
% 2.02/1.23  Subsumption          : 0.02
% 2.02/1.23  Abstraction          : 0.02
% 2.02/1.23  MUC search           : 0.00
% 2.02/1.23  Cooper               : 0.00
% 2.02/1.23  Total                : 0.50
% 2.02/1.23  Index Insertion      : 0.00
% 2.02/1.24  Index Deletion       : 0.00
% 2.02/1.24  Index Matching       : 0.00
% 2.02/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
