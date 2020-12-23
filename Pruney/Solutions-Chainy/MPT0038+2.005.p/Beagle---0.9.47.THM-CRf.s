%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:42 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    3
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(c_11,plain,(
    ! [B_10,A_11] : k3_xboole_0(B_10,A_11) = k3_xboole_0(A_11,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ! [B_10,A_11] : r1_tarski(k3_xboole_0(B_10,A_11),A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_11,c_4])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k2_xboole_0(k3_xboole_0(A_5,B_6),k3_xboole_0(A_5,C_7)) = k3_xboole_0(A_5,k2_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ~ r1_tarski(k2_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_1','#skF_3')),k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')),k2_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_61,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:35:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.08  
% 1.54/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.09  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.63/1.09  
% 1.63/1.09  %Foreground sorts:
% 1.63/1.09  
% 1.63/1.09  
% 1.63/1.09  %Background operators:
% 1.63/1.09  
% 1.63/1.09  
% 1.63/1.09  %Foreground operators:
% 1.63/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.63/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.63/1.09  
% 1.63/1.09  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.63/1.09  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.63/1.09  tff(f_31, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 1.63/1.09  tff(f_34, negated_conjecture, ~(![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 1.63/1.09  tff(c_11, plain, (![B_10, A_11]: (k3_xboole_0(B_10, A_11)=k3_xboole_0(A_11, B_10))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.63/1.09  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.09  tff(c_26, plain, (![B_10, A_11]: (r1_tarski(k3_xboole_0(B_10, A_11), A_11))), inference(superposition, [status(thm), theory('equality')], [c_11, c_4])).
% 1.63/1.09  tff(c_6, plain, (![A_5, B_6, C_7]: (k2_xboole_0(k3_xboole_0(A_5, B_6), k3_xboole_0(A_5, C_7))=k3_xboole_0(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.09  tff(c_8, plain, (~r1_tarski(k2_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_1', '#skF_3')), k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.63/1.09  tff(c_9, plain, (~r1_tarski(k3_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), k2_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 1.63/1.09  tff(c_61, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_9])).
% 1.63/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.09  
% 1.63/1.09  Inference rules
% 1.63/1.09  ----------------------
% 1.63/1.09  #Ref     : 0
% 1.63/1.09  #Sup     : 12
% 1.63/1.09  #Fact    : 0
% 1.63/1.09  #Define  : 0
% 1.63/1.09  #Split   : 0
% 1.63/1.09  #Chain   : 0
% 1.63/1.10  #Close   : 0
% 1.63/1.10  
% 1.63/1.10  Ordering : KBO
% 1.63/1.10  
% 1.63/1.10  Simplification rules
% 1.63/1.10  ----------------------
% 1.63/1.10  #Subsume      : 0
% 1.63/1.10  #Demod        : 5
% 1.63/1.10  #Tautology    : 11
% 1.63/1.10  #SimpNegUnit  : 0
% 1.63/1.10  #BackRed      : 0
% 1.63/1.10  
% 1.63/1.10  #Partial instantiations: 0
% 1.63/1.10  #Strategies tried      : 1
% 1.63/1.10  
% 1.63/1.10  Timing (in seconds)
% 1.63/1.10  ----------------------
% 1.63/1.10  Preprocessing        : 0.25
% 1.63/1.10  Parsing              : 0.14
% 1.63/1.10  CNF conversion       : 0.01
% 1.63/1.10  Main loop            : 0.07
% 1.63/1.10  Inferencing          : 0.03
% 1.63/1.10  Reduction            : 0.03
% 1.63/1.10  Demodulation         : 0.02
% 1.63/1.10  BG Simplification    : 0.01
% 1.63/1.10  Subsumption          : 0.01
% 1.63/1.10  Abstraction          : 0.00
% 1.63/1.10  MUC search           : 0.00
% 1.63/1.10  Cooper               : 0.00
% 1.63/1.10  Total                : 0.36
% 1.63/1.10  Index Insertion      : 0.00
% 1.63/1.10  Index Deletion       : 0.00
% 1.63/1.10  Index Matching       : 0.00
% 1.63/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
