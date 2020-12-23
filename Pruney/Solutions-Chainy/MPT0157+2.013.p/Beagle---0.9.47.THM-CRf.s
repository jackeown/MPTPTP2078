%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:18 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4] : k2_xboole_0(k2_tarski(A_1,B_2),k1_enumset1(C_3,D_4,E_5)) = k3_enumset1(A_1,B_2,C_3,D_4,E_5) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_12,B_13] : k1_enumset1(A_12,A_12,B_13) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,(
    ! [B_27,F_30,E_29,C_26,A_28,D_25] : k2_xboole_0(k1_enumset1(A_28,B_27,C_26),k1_enumset1(D_25,E_29,F_30)) = k4_enumset1(A_28,B_27,C_26,D_25,E_29,F_30) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    ! [F_30,E_29,A_12,B_13,D_25] : k4_enumset1(A_12,A_12,B_13,D_25,E_29,F_30) = k2_xboole_0(k2_tarski(A_12,B_13),k1_enumset1(D_25,E_29,F_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_47])).

tff(c_62,plain,(
    ! [F_30,E_29,A_12,B_13,D_25] : k4_enumset1(A_12,A_12,B_13,D_25,E_29,F_30) = k3_enumset1(A_12,B_13,D_25,E_29,F_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_56])).

tff(c_8,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_65,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:33:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.11  
% 1.71/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.11  %$ k4_enumset1 > k3_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.71/1.11  
% 1.71/1.11  %Foreground sorts:
% 1.71/1.11  
% 1.71/1.11  
% 1.71/1.11  %Background operators:
% 1.71/1.11  
% 1.71/1.11  
% 1.71/1.11  %Foreground operators:
% 1.71/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.11  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.71/1.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.71/1.11  tff('#skF_5', type, '#skF_5': $i).
% 1.71/1.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.71/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.71/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.11  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.71/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.11  tff('#skF_4', type, '#skF_4': $i).
% 1.71/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.71/1.11  
% 1.71/1.12  tff(f_27, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_enumset1)).
% 1.71/1.12  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.71/1.12  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_enumset1)).
% 1.71/1.12  tff(f_34, negated_conjecture, ~(![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 1.71/1.12  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4]: (k2_xboole_0(k2_tarski(A_1, B_2), k1_enumset1(C_3, D_4, E_5))=k3_enumset1(A_1, B_2, C_3, D_4, E_5))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.71/1.12  tff(c_6, plain, (![A_12, B_13]: (k1_enumset1(A_12, A_12, B_13)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.71/1.12  tff(c_47, plain, (![B_27, F_30, E_29, C_26, A_28, D_25]: (k2_xboole_0(k1_enumset1(A_28, B_27, C_26), k1_enumset1(D_25, E_29, F_30))=k4_enumset1(A_28, B_27, C_26, D_25, E_29, F_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.71/1.12  tff(c_56, plain, (![F_30, E_29, A_12, B_13, D_25]: (k4_enumset1(A_12, A_12, B_13, D_25, E_29, F_30)=k2_xboole_0(k2_tarski(A_12, B_13), k1_enumset1(D_25, E_29, F_30)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_47])).
% 1.71/1.12  tff(c_62, plain, (![F_30, E_29, A_12, B_13, D_25]: (k4_enumset1(A_12, A_12, B_13, D_25, E_29, F_30)=k3_enumset1(A_12, B_13, D_25, E_29, F_30))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_56])).
% 1.71/1.12  tff(c_8, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.71/1.12  tff(c_65, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_8])).
% 1.71/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.12  
% 1.71/1.12  Inference rules
% 1.71/1.12  ----------------------
% 1.71/1.12  #Ref     : 0
% 1.71/1.12  #Sup     : 13
% 1.71/1.12  #Fact    : 0
% 1.71/1.12  #Define  : 0
% 1.71/1.12  #Split   : 0
% 1.71/1.12  #Chain   : 0
% 1.71/1.12  #Close   : 0
% 1.71/1.12  
% 1.71/1.12  Ordering : KBO
% 1.71/1.12  
% 1.71/1.12  Simplification rules
% 1.71/1.12  ----------------------
% 1.71/1.12  #Subsume      : 0
% 1.71/1.12  #Demod        : 2
% 1.71/1.12  #Tautology    : 10
% 1.71/1.12  #SimpNegUnit  : 0
% 1.71/1.12  #BackRed      : 1
% 1.71/1.12  
% 1.71/1.12  #Partial instantiations: 0
% 1.71/1.12  #Strategies tried      : 1
% 1.71/1.12  
% 1.71/1.12  Timing (in seconds)
% 1.71/1.12  ----------------------
% 1.71/1.12  Preprocessing        : 0.27
% 1.71/1.12  Parsing              : 0.14
% 1.71/1.12  CNF conversion       : 0.02
% 1.71/1.12  Main loop            : 0.08
% 1.71/1.12  Inferencing          : 0.04
% 1.71/1.12  Reduction            : 0.03
% 1.71/1.12  Demodulation         : 0.02
% 1.71/1.12  BG Simplification    : 0.01
% 1.71/1.12  Subsumption          : 0.01
% 1.71/1.12  Abstraction          : 0.01
% 1.71/1.12  MUC search           : 0.00
% 1.71/1.12  Cooper               : 0.00
% 1.71/1.12  Total                : 0.38
% 1.71/1.12  Index Insertion      : 0.00
% 1.71/1.12  Index Deletion       : 0.00
% 1.71/1.12  Index Matching       : 0.00
% 1.71/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
