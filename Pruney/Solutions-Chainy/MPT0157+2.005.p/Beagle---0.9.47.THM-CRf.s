%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:17 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4] : k2_xboole_0(k1_enumset1(A_1,B_2,C_3),k2_tarski(D_4,E_5)) = k3_enumset1(A_1,B_2,C_3,D_4,E_5) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_20,B_21,C_22] : k2_enumset1(A_20,A_20,B_21,C_22) = k1_enumset1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_120,plain,(
    ! [D_64,B_61,F_65,E_63,A_62,C_66] : k2_xboole_0(k2_enumset1(A_62,B_61,C_66,D_64),k2_tarski(E_63,F_65)) = k4_enumset1(A_62,B_61,C_66,D_64,E_63,F_65) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,(
    ! [C_22,A_20,B_21,F_65,E_63] : k4_enumset1(A_20,A_20,B_21,C_22,E_63,F_65) = k2_xboole_0(k1_enumset1(A_20,B_21,C_22),k2_tarski(E_63,F_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_120])).

tff(c_132,plain,(
    ! [C_22,A_20,B_21,F_65,E_63] : k4_enumset1(A_20,A_20,B_21,C_22,E_63,F_65) = k3_enumset1(A_20,B_21,C_22,E_63,F_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_129])).

tff(c_14,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.30  
% 1.89/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.30  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.89/1.30  
% 1.89/1.30  %Foreground sorts:
% 1.89/1.30  
% 1.89/1.30  
% 1.89/1.30  %Background operators:
% 1.89/1.30  
% 1.89/1.30  
% 1.89/1.30  %Foreground operators:
% 1.89/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.89/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.89/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.30  tff('#skF_5', type, '#skF_5': $i).
% 1.89/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.30  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.30  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.30  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.89/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.30  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.89/1.30  
% 1.89/1.31  tff(f_27, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 1.89/1.31  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.89/1.31  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 1.89/1.31  tff(f_40, negated_conjecture, ~(![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 1.89/1.31  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4]: (k2_xboole_0(k1_enumset1(A_1, B_2, C_3), k2_tarski(D_4, E_5))=k3_enumset1(A_1, B_2, C_3, D_4, E_5))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.89/1.31  tff(c_10, plain, (![A_20, B_21, C_22]: (k2_enumset1(A_20, A_20, B_21, C_22)=k1_enumset1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.89/1.31  tff(c_120, plain, (![D_64, B_61, F_65, E_63, A_62, C_66]: (k2_xboole_0(k2_enumset1(A_62, B_61, C_66, D_64), k2_tarski(E_63, F_65))=k4_enumset1(A_62, B_61, C_66, D_64, E_63, F_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.31  tff(c_129, plain, (![C_22, A_20, B_21, F_65, E_63]: (k4_enumset1(A_20, A_20, B_21, C_22, E_63, F_65)=k2_xboole_0(k1_enumset1(A_20, B_21, C_22), k2_tarski(E_63, F_65)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_120])).
% 1.89/1.31  tff(c_132, plain, (![C_22, A_20, B_21, F_65, E_63]: (k4_enumset1(A_20, A_20, B_21, C_22, E_63, F_65)=k3_enumset1(A_20, B_21, C_22, E_63, F_65))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_129])).
% 1.89/1.31  tff(c_14, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.89/1.31  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_14])).
% 1.89/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.31  
% 1.89/1.31  Inference rules
% 1.89/1.31  ----------------------
% 1.89/1.31  #Ref     : 0
% 1.89/1.31  #Sup     : 33
% 1.89/1.31  #Fact    : 0
% 1.89/1.31  #Define  : 0
% 1.89/1.31  #Split   : 0
% 1.89/1.31  #Chain   : 0
% 1.89/1.31  #Close   : 0
% 1.89/1.31  
% 1.89/1.31  Ordering : KBO
% 1.89/1.31  
% 1.89/1.31  Simplification rules
% 1.89/1.31  ----------------------
% 1.89/1.31  #Subsume      : 0
% 1.89/1.31  #Demod        : 18
% 1.89/1.31  #Tautology    : 28
% 1.89/1.31  #SimpNegUnit  : 0
% 1.89/1.31  #BackRed      : 2
% 1.89/1.31  
% 1.89/1.31  #Partial instantiations: 0
% 1.89/1.31  #Strategies tried      : 1
% 1.89/1.31  
% 1.89/1.31  Timing (in seconds)
% 1.89/1.31  ----------------------
% 1.89/1.31  Preprocessing        : 0.35
% 1.89/1.31  Parsing              : 0.17
% 1.89/1.31  CNF conversion       : 0.02
% 1.89/1.31  Main loop            : 0.15
% 1.89/1.31  Inferencing          : 0.07
% 1.89/1.31  Reduction            : 0.05
% 1.89/1.31  Demodulation         : 0.04
% 1.89/1.31  BG Simplification    : 0.02
% 1.89/1.31  Subsumption          : 0.01
% 1.89/1.31  Abstraction          : 0.01
% 1.89/1.31  MUC search           : 0.00
% 1.89/1.31  Cooper               : 0.00
% 1.89/1.31  Total                : 0.53
% 1.89/1.31  Index Insertion      : 0.00
% 1.89/1.31  Index Deletion       : 0.00
% 1.89/1.31  Index Matching       : 0.00
% 1.89/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
