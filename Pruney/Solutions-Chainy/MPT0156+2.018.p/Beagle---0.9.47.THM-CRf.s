%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:16 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    4
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] : k2_xboole_0(k1_tarski(A_3),k1_enumset1(B_4,C_5,D_6)) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_52,plain,(
    ! [D_24,B_25,C_26,A_27,E_28] : k2_xboole_0(k2_tarski(A_27,B_25),k1_enumset1(C_26,D_24,E_28)) = k3_enumset1(A_27,B_25,C_26,D_24,E_28) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [A_12,C_26,D_24,E_28] : k3_enumset1(A_12,A_12,C_26,D_24,E_28) = k2_xboole_0(k1_tarski(A_12),k1_enumset1(C_26,D_24,E_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_52])).

tff(c_67,plain,(
    ! [A_12,C_26,D_24,E_28] : k3_enumset1(A_12,A_12,C_26,D_24,E_28) = k2_enumset1(A_12,C_26,D_24,E_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_64])).

tff(c_12,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:13:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.09  
% 1.69/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.09  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.69/1.09  
% 1.69/1.09  %Foreground sorts:
% 1.69/1.09  
% 1.69/1.09  
% 1.69/1.09  %Background operators:
% 1.69/1.09  
% 1.69/1.09  
% 1.69/1.09  %Foreground operators:
% 1.69/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.69/1.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.69/1.09  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.69/1.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.69/1.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.69/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.69/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.09  tff('#skF_4', type, '#skF_4': $i).
% 1.69/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.69/1.09  
% 1.69/1.10  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 1.69/1.10  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.69/1.10  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 1.69/1.10  tff(f_38, negated_conjecture, ~(![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.69/1.10  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (k2_xboole_0(k1_tarski(A_3), k1_enumset1(B_4, C_5, D_6))=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.69/1.10  tff(c_8, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.69/1.10  tff(c_52, plain, (![D_24, B_25, C_26, A_27, E_28]: (k2_xboole_0(k2_tarski(A_27, B_25), k1_enumset1(C_26, D_24, E_28))=k3_enumset1(A_27, B_25, C_26, D_24, E_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.10  tff(c_64, plain, (![A_12, C_26, D_24, E_28]: (k3_enumset1(A_12, A_12, C_26, D_24, E_28)=k2_xboole_0(k1_tarski(A_12), k1_enumset1(C_26, D_24, E_28)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_52])).
% 1.69/1.10  tff(c_67, plain, (![A_12, C_26, D_24, E_28]: (k3_enumset1(A_12, A_12, C_26, D_24, E_28)=k2_enumset1(A_12, C_26, D_24, E_28))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_64])).
% 1.69/1.10  tff(c_12, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.69/1.10  tff(c_116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_12])).
% 1.69/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.10  
% 1.69/1.10  Inference rules
% 1.69/1.10  ----------------------
% 1.69/1.10  #Ref     : 0
% 1.69/1.10  #Sup     : 24
% 1.69/1.10  #Fact    : 0
% 1.69/1.10  #Define  : 0
% 1.69/1.10  #Split   : 0
% 1.69/1.10  #Chain   : 0
% 1.69/1.10  #Close   : 0
% 1.69/1.10  
% 1.69/1.10  Ordering : KBO
% 1.69/1.10  
% 1.69/1.10  Simplification rules
% 1.69/1.10  ----------------------
% 1.69/1.10  #Subsume      : 0
% 1.69/1.10  #Demod        : 4
% 1.69/1.10  #Tautology    : 20
% 1.69/1.10  #SimpNegUnit  : 0
% 1.69/1.10  #BackRed      : 1
% 1.69/1.10  
% 1.69/1.10  #Partial instantiations: 0
% 1.69/1.10  #Strategies tried      : 1
% 1.69/1.10  
% 1.69/1.10  Timing (in seconds)
% 1.69/1.10  ----------------------
% 1.69/1.10  Preprocessing        : 0.26
% 1.69/1.10  Parsing              : 0.14
% 1.69/1.10  CNF conversion       : 0.01
% 1.69/1.10  Main loop            : 0.10
% 1.69/1.10  Inferencing          : 0.04
% 1.69/1.10  Reduction            : 0.03
% 1.69/1.10  Demodulation         : 0.02
% 1.69/1.10  BG Simplification    : 0.01
% 1.69/1.10  Subsumption          : 0.01
% 1.69/1.10  Abstraction          : 0.01
% 1.69/1.10  MUC search           : 0.00
% 1.69/1.10  Cooper               : 0.00
% 1.69/1.10  Total                : 0.38
% 1.69/1.10  Index Insertion      : 0.00
% 1.69/1.10  Index Deletion       : 0.00
% 1.69/1.10  Index Matching       : 0.00
% 1.69/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
