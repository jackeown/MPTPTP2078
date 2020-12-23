%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:16 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   25 (  26 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   13 (  14 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(c_52,plain,(
    ! [E_26,A_25,D_22,B_23,C_24] : k2_xboole_0(k1_tarski(A_25),k2_enumset1(B_23,C_24,D_22,E_26)) = k3_enumset1(A_25,B_23,C_24,D_22,E_26) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] : k2_xboole_0(k1_tarski(A_3),k1_enumset1(B_4,C_5,D_6)) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ! [A_14,B_15,C_16,D_17] : k2_xboole_0(k1_tarski(A_14),k1_enumset1(B_15,C_16,D_17)) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_14,B_15,C_16,D_17] : k2_xboole_0(k1_tarski(A_14),k2_enumset1(A_14,B_15,C_16,D_17)) = k2_xboole_0(k1_tarski(A_14),k1_enumset1(B_15,C_16,D_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2])).

tff(c_37,plain,(
    ! [A_14,B_15,C_16,D_17] : k2_xboole_0(k1_tarski(A_14),k2_enumset1(A_14,B_15,C_16,D_17)) = k2_enumset1(A_14,B_15,C_16,D_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_32])).

tff(c_59,plain,(
    ! [B_23,C_24,D_22,E_26] : k3_enumset1(B_23,B_23,C_24,D_22,E_26) = k2_enumset1(B_23,C_24,D_22,E_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_37])).

tff(c_8,plain,(
    k3_enumset1('#skF_1','#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:37:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.08  
% 1.63/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.08  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.63/1.08  
% 1.63/1.08  %Foreground sorts:
% 1.63/1.08  
% 1.63/1.08  
% 1.63/1.08  %Background operators:
% 1.63/1.08  
% 1.63/1.08  
% 1.63/1.08  %Foreground operators:
% 1.63/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.63/1.08  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.63/1.08  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.63/1.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.63/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.08  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.08  tff('#skF_4', type, '#skF_4': $i).
% 1.63/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.63/1.08  
% 1.63/1.09  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 1.63/1.09  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 1.63/1.09  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 1.63/1.09  tff(f_34, negated_conjecture, ~(![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.63/1.09  tff(c_52, plain, (![E_26, A_25, D_22, B_23, C_24]: (k2_xboole_0(k1_tarski(A_25), k2_enumset1(B_23, C_24, D_22, E_26))=k3_enumset1(A_25, B_23, C_24, D_22, E_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.09  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (k2_xboole_0(k1_tarski(A_3), k1_enumset1(B_4, C_5, D_6))=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.09  tff(c_26, plain, (![A_14, B_15, C_16, D_17]: (k2_xboole_0(k1_tarski(A_14), k1_enumset1(B_15, C_16, D_17))=k2_enumset1(A_14, B_15, C_16, D_17))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.09  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.63/1.09  tff(c_32, plain, (![A_14, B_15, C_16, D_17]: (k2_xboole_0(k1_tarski(A_14), k2_enumset1(A_14, B_15, C_16, D_17))=k2_xboole_0(k1_tarski(A_14), k1_enumset1(B_15, C_16, D_17)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2])).
% 1.63/1.09  tff(c_37, plain, (![A_14, B_15, C_16, D_17]: (k2_xboole_0(k1_tarski(A_14), k2_enumset1(A_14, B_15, C_16, D_17))=k2_enumset1(A_14, B_15, C_16, D_17))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_32])).
% 1.63/1.09  tff(c_59, plain, (![B_23, C_24, D_22, E_26]: (k3_enumset1(B_23, B_23, C_24, D_22, E_26)=k2_enumset1(B_23, C_24, D_22, E_26))), inference(superposition, [status(thm), theory('equality')], [c_52, c_37])).
% 1.63/1.09  tff(c_8, plain, (k3_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.63/1.09  tff(c_87, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_8])).
% 1.63/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.09  
% 1.63/1.09  Inference rules
% 1.63/1.09  ----------------------
% 1.63/1.09  #Ref     : 0
% 1.63/1.09  #Sup     : 18
% 1.63/1.09  #Fact    : 0
% 1.63/1.09  #Define  : 0
% 1.63/1.09  #Split   : 0
% 1.63/1.09  #Chain   : 0
% 1.63/1.09  #Close   : 0
% 1.63/1.09  
% 1.63/1.09  Ordering : KBO
% 1.63/1.09  
% 1.63/1.09  Simplification rules
% 1.63/1.09  ----------------------
% 1.63/1.09  #Subsume      : 0
% 1.63/1.09  #Demod        : 11
% 1.63/1.09  #Tautology    : 14
% 1.63/1.09  #SimpNegUnit  : 0
% 1.63/1.09  #BackRed      : 1
% 1.63/1.09  
% 1.63/1.09  #Partial instantiations: 0
% 1.63/1.09  #Strategies tried      : 1
% 1.63/1.09  
% 1.63/1.09  Timing (in seconds)
% 1.63/1.09  ----------------------
% 1.63/1.09  Preprocessing        : 0.26
% 1.63/1.09  Parsing              : 0.13
% 1.63/1.10  CNF conversion       : 0.02
% 1.63/1.10  Main loop            : 0.09
% 1.63/1.10  Inferencing          : 0.05
% 1.63/1.10  Reduction            : 0.03
% 1.63/1.10  Demodulation         : 0.02
% 1.63/1.10  BG Simplification    : 0.01
% 1.63/1.10  Subsumption          : 0.01
% 1.63/1.10  Abstraction          : 0.01
% 1.63/1.10  MUC search           : 0.00
% 1.63/1.10  Cooper               : 0.00
% 1.63/1.10  Total                : 0.37
% 1.63/1.10  Index Insertion      : 0.00
% 1.63/1.10  Index Deletion       : 0.00
% 1.63/1.10  Index Matching       : 0.00
% 1.63/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
