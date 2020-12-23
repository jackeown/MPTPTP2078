%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:18 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
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
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_tarski(A,B),k2_enumset1(C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_enumset1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(c_2,plain,(
    ! [B_2,C_3,A_1,E_5,D_4] : k2_xboole_0(k1_tarski(A_1),k2_enumset1(B_2,C_3,D_4,E_5)) = k3_enumset1(A_1,B_2,C_3,D_4,E_5) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [D_27,A_30,F_32,B_29,E_31,C_28] : k2_xboole_0(k2_tarski(A_30,B_29),k2_enumset1(C_28,D_27,E_31,F_32)) = k4_enumset1(A_30,B_29,C_28,D_27,E_31,F_32) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    ! [D_27,F_32,A_12,E_31,C_28] : k4_enumset1(A_12,A_12,C_28,D_27,E_31,F_32) = k2_xboole_0(k1_tarski(A_12),k2_enumset1(C_28,D_27,E_31,F_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_38])).

tff(c_50,plain,(
    ! [D_27,F_32,A_12,E_31,C_28] : k4_enumset1(A_12,A_12,C_28,D_27,E_31,F_32) = k3_enumset1(A_12,C_28,D_27,E_31,F_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_47])).

tff(c_10,plain,(
    k4_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') != k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_53,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.08  
% 1.65/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.09  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.65/1.09  
% 1.65/1.09  %Foreground sorts:
% 1.65/1.09  
% 1.65/1.09  
% 1.65/1.09  %Background operators:
% 1.65/1.09  
% 1.65/1.09  
% 1.65/1.09  %Foreground operators:
% 1.65/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.65/1.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.65/1.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.65/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.65/1.09  tff('#skF_5', type, '#skF_5': $i).
% 1.65/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.09  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.65/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.09  tff('#skF_4', type, '#skF_4': $i).
% 1.65/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.65/1.09  
% 1.65/1.09  tff(f_27, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 1.65/1.09  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.65/1.09  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_tarski(A, B), k2_enumset1(C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_enumset1)).
% 1.65/1.09  tff(f_36, negated_conjecture, ~(![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.65/1.09  tff(c_2, plain, (![B_2, C_3, A_1, E_5, D_4]: (k2_xboole_0(k1_tarski(A_1), k2_enumset1(B_2, C_3, D_4, E_5))=k3_enumset1(A_1, B_2, C_3, D_4, E_5))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.65/1.09  tff(c_6, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.09  tff(c_38, plain, (![D_27, A_30, F_32, B_29, E_31, C_28]: (k2_xboole_0(k2_tarski(A_30, B_29), k2_enumset1(C_28, D_27, E_31, F_32))=k4_enumset1(A_30, B_29, C_28, D_27, E_31, F_32))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.09  tff(c_47, plain, (![D_27, F_32, A_12, E_31, C_28]: (k4_enumset1(A_12, A_12, C_28, D_27, E_31, F_32)=k2_xboole_0(k1_tarski(A_12), k2_enumset1(C_28, D_27, E_31, F_32)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_38])).
% 1.65/1.09  tff(c_50, plain, (![D_27, F_32, A_12, E_31, C_28]: (k4_enumset1(A_12, A_12, C_28, D_27, E_31, F_32)=k3_enumset1(A_12, C_28, D_27, E_31, F_32))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_47])).
% 1.65/1.09  tff(c_10, plain, (k4_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.65/1.09  tff(c_53, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_10])).
% 1.65/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.09  
% 1.65/1.09  Inference rules
% 1.65/1.09  ----------------------
% 1.65/1.09  #Ref     : 0
% 1.65/1.09  #Sup     : 9
% 1.65/1.09  #Fact    : 0
% 1.65/1.09  #Define  : 0
% 1.65/1.09  #Split   : 0
% 1.65/1.09  #Chain   : 0
% 1.65/1.09  #Close   : 0
% 1.65/1.09  
% 1.65/1.09  Ordering : KBO
% 1.65/1.09  
% 1.65/1.09  Simplification rules
% 1.65/1.09  ----------------------
% 1.65/1.09  #Subsume      : 0
% 1.65/1.09  #Demod        : 2
% 1.65/1.09  #Tautology    : 8
% 1.65/1.09  #SimpNegUnit  : 0
% 1.65/1.09  #BackRed      : 1
% 1.65/1.09  
% 1.65/1.09  #Partial instantiations: 0
% 1.65/1.09  #Strategies tried      : 1
% 1.65/1.09  
% 1.65/1.09  Timing (in seconds)
% 1.65/1.09  ----------------------
% 1.65/1.10  Preprocessing        : 0.27
% 1.65/1.10  Parsing              : 0.14
% 1.65/1.10  CNF conversion       : 0.02
% 1.65/1.10  Main loop            : 0.07
% 1.65/1.10  Inferencing          : 0.03
% 1.65/1.10  Reduction            : 0.02
% 1.65/1.10  Demodulation         : 0.02
% 1.65/1.10  BG Simplification    : 0.01
% 1.65/1.10  Subsumption          : 0.01
% 1.65/1.10  Abstraction          : 0.01
% 1.65/1.10  MUC search           : 0.00
% 1.65/1.10  Cooper               : 0.00
% 1.65/1.10  Total                : 0.36
% 1.65/1.10  Index Insertion      : 0.00
% 1.65/1.10  Index Deletion       : 0.00
% 1.65/1.10  Index Matching       : 0.00
% 1.65/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
