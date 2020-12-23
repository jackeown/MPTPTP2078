%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:34 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_35,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k5_enumset1(A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] : k5_enumset1(A,A,A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_enumset1)).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k1_tarski(A_1),k1_tarski(B_2)) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_20] : k2_enumset1(A_20,A_20,A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41,plain,(
    ! [B_33,A_31,D_30,E_29,C_32] : k2_xboole_0(k2_enumset1(A_31,B_33,C_32,D_30),k1_tarski(E_29)) = k3_enumset1(A_31,B_33,C_32,D_30,E_29) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_50,plain,(
    ! [A_20,E_29] : k3_enumset1(A_20,A_20,A_20,A_20,E_29) = k2_xboole_0(k1_tarski(A_20),k1_tarski(E_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_41])).

tff(c_53,plain,(
    ! [A_20,E_29] : k3_enumset1(A_20,A_20,A_20,A_20,E_29) = k2_tarski(A_20,E_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_50])).

tff(c_8,plain,(
    ! [B_16,A_15,D_18,E_19,C_17] : k5_enumset1(A_15,A_15,A_15,B_16,C_17,D_18,E_19) = k3_enumset1(A_15,B_16,C_17,D_18,E_19) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    k5_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_12])).

tff(c_65,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:57:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.10  
% 1.72/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.10  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.72/1.10  
% 1.72/1.10  %Foreground sorts:
% 1.72/1.10  
% 1.72/1.10  
% 1.72/1.10  %Background operators:
% 1.72/1.10  
% 1.72/1.10  
% 1.72/1.10  %Foreground operators:
% 1.72/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.72/1.10  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.72/1.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.72/1.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.72/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.10  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.72/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.72/1.10  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.72/1.10  
% 1.72/1.11  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.72/1.11  tff(f_35, axiom, (![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_enumset1)).
% 1.72/1.11  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 1.72/1.11  tff(f_33, axiom, (![A, B, C, D, E]: (k5_enumset1(A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_enumset1)).
% 1.72/1.11  tff(f_38, negated_conjecture, ~(![A, B]: (k5_enumset1(A, A, A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_enumset1)).
% 1.72/1.11  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k1_tarski(A_1), k1_tarski(B_2))=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.72/1.11  tff(c_10, plain, (![A_20]: (k2_enumset1(A_20, A_20, A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.72/1.11  tff(c_41, plain, (![B_33, A_31, D_30, E_29, C_32]: (k2_xboole_0(k2_enumset1(A_31, B_33, C_32, D_30), k1_tarski(E_29))=k3_enumset1(A_31, B_33, C_32, D_30, E_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.72/1.11  tff(c_50, plain, (![A_20, E_29]: (k3_enumset1(A_20, A_20, A_20, A_20, E_29)=k2_xboole_0(k1_tarski(A_20), k1_tarski(E_29)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_41])).
% 1.72/1.11  tff(c_53, plain, (![A_20, E_29]: (k3_enumset1(A_20, A_20, A_20, A_20, E_29)=k2_tarski(A_20, E_29))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_50])).
% 1.72/1.11  tff(c_8, plain, (![B_16, A_15, D_18, E_19, C_17]: (k5_enumset1(A_15, A_15, A_15, B_16, C_17, D_18, E_19)=k3_enumset1(A_15, B_16, C_17, D_18, E_19))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.72/1.11  tff(c_12, plain, (k5_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.72/1.11  tff(c_13, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_12])).
% 1.72/1.11  tff(c_65, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_13])).
% 1.72/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.11  
% 1.72/1.11  Inference rules
% 1.72/1.11  ----------------------
% 1.72/1.11  #Ref     : 0
% 1.72/1.11  #Sup     : 11
% 1.72/1.11  #Fact    : 0
% 1.72/1.11  #Define  : 0
% 1.72/1.11  #Split   : 0
% 1.72/1.11  #Chain   : 0
% 1.72/1.11  #Close   : 0
% 1.72/1.11  
% 1.72/1.11  Ordering : KBO
% 1.72/1.11  
% 1.72/1.11  Simplification rules
% 1.72/1.11  ----------------------
% 1.72/1.11  #Subsume      : 0
% 1.72/1.11  #Demod        : 3
% 1.72/1.11  #Tautology    : 10
% 1.72/1.11  #SimpNegUnit  : 0
% 1.72/1.11  #BackRed      : 1
% 1.72/1.11  
% 1.72/1.11  #Partial instantiations: 0
% 1.72/1.11  #Strategies tried      : 1
% 1.72/1.11  
% 1.72/1.11  Timing (in seconds)
% 1.72/1.11  ----------------------
% 1.72/1.12  Preprocessing        : 0.28
% 1.72/1.12  Parsing              : 0.15
% 1.72/1.12  CNF conversion       : 0.02
% 1.72/1.12  Main loop            : 0.08
% 1.72/1.12  Inferencing          : 0.04
% 1.72/1.12  Reduction            : 0.02
% 1.72/1.12  Demodulation         : 0.02
% 1.72/1.12  BG Simplification    : 0.01
% 1.72/1.12  Subsumption          : 0.01
% 1.72/1.12  Abstraction          : 0.01
% 1.72/1.12  MUC search           : 0.00
% 1.72/1.12  Cooper               : 0.00
% 1.72/1.12  Total                : 0.39
% 1.72/1.12  Index Insertion      : 0.00
% 1.72/1.12  Index Deletion       : 0.00
% 1.72/1.12  Index Matching       : 0.00
% 1.72/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
