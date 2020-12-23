%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:44 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_35,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_tarski(A,B),k2_enumset1(C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).

tff(c_10,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,D_16] : k2_xboole_0(k1_tarski(A_13),k3_enumset1(B_14,C_15,D_16,E_17,F_18)) = k4_enumset1(A_13,B_14,C_15,D_16,E_17,F_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_86,plain,(
    ! [E_33,D_36,B_34,A_32,C_35] : k2_xboole_0(k1_tarski(A_32),k2_enumset1(B_34,C_35,D_36,E_33)) = k3_enumset1(A_32,B_34,C_35,D_36,E_33) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),k1_tarski(B_7)) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_31,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k2_xboole_0(A_23,B_24),C_25) = k2_xboole_0(A_23,k2_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    ! [A_6,B_7,C_25] : k2_xboole_0(k1_tarski(A_6),k2_xboole_0(k1_tarski(B_7),C_25)) = k2_xboole_0(k2_tarski(A_6,B_7),C_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_31])).

tff(c_92,plain,(
    ! [E_33,D_36,B_34,A_32,A_6,C_35] : k2_xboole_0(k2_tarski(A_6,A_32),k2_enumset1(B_34,C_35,D_36,E_33)) = k2_xboole_0(k1_tarski(A_6),k3_enumset1(A_32,B_34,C_35,D_36,E_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_46])).

tff(c_164,plain,(
    ! [E_33,D_36,B_34,A_32,A_6,C_35] : k2_xboole_0(k2_tarski(A_6,A_32),k2_enumset1(B_34,C_35,D_36,E_33)) = k4_enumset1(A_6,A_32,B_34,C_35,D_36,E_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_92])).

tff(c_12,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_enumset1('#skF_3','#skF_4','#skF_5','#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:33:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.16  
% 1.72/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.16  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.72/1.16  
% 1.72/1.16  %Foreground sorts:
% 1.72/1.16  
% 1.72/1.16  
% 1.72/1.16  %Background operators:
% 1.72/1.16  
% 1.72/1.16  
% 1.72/1.16  %Foreground operators:
% 1.72/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.72/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.72/1.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.72/1.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.72/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.72/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.72/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.72/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.72/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.72/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.16  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.72/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.72/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.72/1.16  
% 1.72/1.17  tff(f_35, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 1.72/1.17  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 1.72/1.17  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.72/1.17  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 1.72/1.17  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_tarski(A, B), k2_enumset1(C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_enumset1)).
% 1.72/1.17  tff(c_10, plain, (![E_17, F_18, A_13, B_14, C_15, D_16]: (k2_xboole_0(k1_tarski(A_13), k3_enumset1(B_14, C_15, D_16, E_17, F_18))=k4_enumset1(A_13, B_14, C_15, D_16, E_17, F_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.72/1.17  tff(c_86, plain, (![E_33, D_36, B_34, A_32, C_35]: (k2_xboole_0(k1_tarski(A_32), k2_enumset1(B_34, C_35, D_36, E_33))=k3_enumset1(A_32, B_34, C_35, D_36, E_33))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.72/1.17  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(B_7))=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.72/1.17  tff(c_31, plain, (![A_23, B_24, C_25]: (k2_xboole_0(k2_xboole_0(A_23, B_24), C_25)=k2_xboole_0(A_23, k2_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.72/1.17  tff(c_46, plain, (![A_6, B_7, C_25]: (k2_xboole_0(k1_tarski(A_6), k2_xboole_0(k1_tarski(B_7), C_25))=k2_xboole_0(k2_tarski(A_6, B_7), C_25))), inference(superposition, [status(thm), theory('equality')], [c_6, c_31])).
% 1.72/1.17  tff(c_92, plain, (![E_33, D_36, B_34, A_32, A_6, C_35]: (k2_xboole_0(k2_tarski(A_6, A_32), k2_enumset1(B_34, C_35, D_36, E_33))=k2_xboole_0(k1_tarski(A_6), k3_enumset1(A_32, B_34, C_35, D_36, E_33)))), inference(superposition, [status(thm), theory('equality')], [c_86, c_46])).
% 1.72/1.17  tff(c_164, plain, (![E_33, D_36, B_34, A_32, A_6, C_35]: (k2_xboole_0(k2_tarski(A_6, A_32), k2_enumset1(B_34, C_35, D_36, E_33))=k4_enumset1(A_6, A_32, B_34, C_35, D_36, E_33))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_92])).
% 1.72/1.17  tff(c_12, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.72/1.17  tff(c_167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_12])).
% 1.72/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.17  
% 1.72/1.17  Inference rules
% 1.72/1.17  ----------------------
% 1.72/1.17  #Ref     : 0
% 1.72/1.17  #Sup     : 38
% 1.72/1.17  #Fact    : 0
% 1.72/1.17  #Define  : 0
% 1.72/1.17  #Split   : 0
% 1.72/1.17  #Chain   : 0
% 1.72/1.17  #Close   : 0
% 1.72/1.17  
% 1.72/1.17  Ordering : KBO
% 1.72/1.17  
% 1.72/1.17  Simplification rules
% 1.72/1.17  ----------------------
% 1.72/1.17  #Subsume      : 0
% 1.72/1.17  #Demod        : 25
% 1.72/1.17  #Tautology    : 27
% 1.72/1.17  #SimpNegUnit  : 0
% 1.72/1.17  #BackRed      : 1
% 1.72/1.17  
% 1.72/1.17  #Partial instantiations: 0
% 1.72/1.17  #Strategies tried      : 1
% 1.72/1.17  
% 1.72/1.17  Timing (in seconds)
% 1.72/1.17  ----------------------
% 1.72/1.17  Preprocessing        : 0.26
% 1.72/1.17  Parsing              : 0.14
% 1.72/1.17  CNF conversion       : 0.02
% 1.72/1.17  Main loop            : 0.17
% 1.72/1.17  Inferencing          : 0.08
% 1.72/1.17  Reduction            : 0.05
% 1.72/1.17  Demodulation         : 0.05
% 1.72/1.17  BG Simplification    : 0.01
% 1.72/1.17  Subsumption          : 0.02
% 1.72/1.17  Abstraction          : 0.01
% 1.72/1.17  MUC search           : 0.00
% 1.72/1.17  Cooper               : 0.00
% 1.72/1.17  Total                : 0.45
% 1.72/1.17  Index Insertion      : 0.00
% 1.72/1.17  Index Deletion       : 0.00
% 1.72/1.17  Index Matching       : 0.00
% 1.72/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
