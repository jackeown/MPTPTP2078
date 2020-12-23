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
% DateTime   : Thu Dec  3 09:42:40 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    6 (   3 average)
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

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    ! [A_21,C_22,B_23] :
      ( r1_tarski(A_21,C_22)
      | ~ r1_tarski(k2_xboole_0(A_21,B_23),C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [A_24,B_25,B_26] : r1_tarski(A_24,k2_xboole_0(k2_xboole_0(A_24,B_25),B_26)) ),
    inference(resolution,[status(thm)],[c_8,c_78])).

tff(c_159,plain,(
    ! [A_30,B_31,B_32] : r1_tarski(A_30,k2_xboole_0(k2_xboole_0(B_31,A_30),B_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_104])).

tff(c_166,plain,(
    ! [A_6,B_7,B_32] : r1_tarski(k3_xboole_0(A_6,B_7),k2_xboole_0(A_6,B_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_159])).

tff(c_10,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:01:50 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.20  
% 1.85/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.20  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.85/1.20  
% 1.85/1.20  %Foreground sorts:
% 1.85/1.20  
% 1.85/1.20  
% 1.85/1.20  %Background operators:
% 1.85/1.20  
% 1.85/1.20  
% 1.85/1.20  %Foreground operators:
% 1.85/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.85/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.85/1.21  
% 1.85/1.21  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 1.85/1.21  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.85/1.21  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.85/1.21  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.85/1.21  tff(f_38, negated_conjecture, ~(![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_xboole_1)).
% 1.85/1.21  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k3_xboole_0(A_6, B_7))=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.85/1.21  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.85/1.21  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.85/1.21  tff(c_78, plain, (![A_21, C_22, B_23]: (r1_tarski(A_21, C_22) | ~r1_tarski(k2_xboole_0(A_21, B_23), C_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.21  tff(c_104, plain, (![A_24, B_25, B_26]: (r1_tarski(A_24, k2_xboole_0(k2_xboole_0(A_24, B_25), B_26)))), inference(resolution, [status(thm)], [c_8, c_78])).
% 1.85/1.21  tff(c_159, plain, (![A_30, B_31, B_32]: (r1_tarski(A_30, k2_xboole_0(k2_xboole_0(B_31, A_30), B_32)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_104])).
% 1.85/1.21  tff(c_166, plain, (![A_6, B_7, B_32]: (r1_tarski(k3_xboole_0(A_6, B_7), k2_xboole_0(A_6, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_159])).
% 1.85/1.21  tff(c_10, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.85/1.21  tff(c_272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_166, c_10])).
% 1.85/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.21  
% 1.85/1.21  Inference rules
% 1.85/1.21  ----------------------
% 1.85/1.21  #Ref     : 0
% 1.85/1.21  #Sup     : 58
% 1.85/1.21  #Fact    : 0
% 1.85/1.21  #Define  : 0
% 1.85/1.21  #Split   : 0
% 1.85/1.21  #Chain   : 0
% 1.85/1.21  #Close   : 0
% 1.85/1.21  
% 1.85/1.21  Ordering : KBO
% 1.85/1.21  
% 1.85/1.21  Simplification rules
% 1.85/1.21  ----------------------
% 1.85/1.21  #Subsume      : 2
% 1.85/1.21  #Demod        : 26
% 1.85/1.21  #Tautology    : 36
% 1.85/1.21  #SimpNegUnit  : 0
% 1.85/1.21  #BackRed      : 1
% 1.85/1.21  
% 1.85/1.21  #Partial instantiations: 0
% 1.85/1.21  #Strategies tried      : 1
% 1.85/1.21  
% 1.85/1.21  Timing (in seconds)
% 1.85/1.21  ----------------------
% 1.85/1.22  Preprocessing        : 0.24
% 1.85/1.22  Parsing              : 0.13
% 1.85/1.22  CNF conversion       : 0.01
% 1.85/1.22  Main loop            : 0.18
% 1.85/1.22  Inferencing          : 0.06
% 1.85/1.22  Reduction            : 0.07
% 1.85/1.22  Demodulation         : 0.06
% 1.85/1.22  BG Simplification    : 0.01
% 1.85/1.22  Subsumption          : 0.03
% 1.85/1.22  Abstraction          : 0.01
% 1.85/1.22  MUC search           : 0.00
% 1.85/1.22  Cooper               : 0.00
% 1.85/1.22  Total                : 0.44
% 1.85/1.22  Index Insertion      : 0.00
% 1.85/1.22  Index Deletion       : 0.00
% 1.85/1.22  Index Matching       : 0.00
% 1.85/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
