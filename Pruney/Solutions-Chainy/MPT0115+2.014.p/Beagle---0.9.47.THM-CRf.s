%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:27 EST 2020

% Result     : Theorem 1.39s
% Output     : CNFRefutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_27,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_45,plain,(
    ! [A_16,B_17] : r1_tarski(k3_xboole_0(A_16,B_17),A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_6])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_49,plain,(
    ! [A_16,B_17] : k2_xboole_0(k3_xboole_0(A_16,B_17),A_16) = A_16 ),
    inference(resolution,[status(thm)],[c_45,c_4])).

tff(c_71,plain,(
    ! [A_22,C_23,B_24] :
      ( r1_tarski(A_22,C_23)
      | ~ r1_tarski(k2_xboole_0(A_22,B_24),C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_91,plain,(
    ! [A_29,B_30,C_31] :
      ( r1_tarski(k3_xboole_0(A_29,B_30),C_31)
      | ~ r1_tarski(A_29,C_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_71])).

tff(c_10,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_97,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_91,c_10])).

tff(c_102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_97])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:21:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.39/1.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.39/1.01  
% 1.39/1.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.39/1.02  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.39/1.02  
% 1.39/1.02  %Foreground sorts:
% 1.39/1.02  
% 1.39/1.02  
% 1.39/1.02  %Background operators:
% 1.39/1.02  
% 1.39/1.02  
% 1.39/1.02  %Foreground operators:
% 1.39/1.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.39/1.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.39/1.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.39/1.02  tff('#skF_2', type, '#skF_2': $i).
% 1.39/1.02  tff('#skF_3', type, '#skF_3': $i).
% 1.39/1.02  tff('#skF_1', type, '#skF_1': $i).
% 1.39/1.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.39/1.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.39/1.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.39/1.02  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.39/1.02  
% 1.39/1.02  tff(f_42, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 1.39/1.02  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.39/1.02  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.39/1.02  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.39/1.02  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.39/1.02  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.39/1.02  tff(c_27, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.39/1.02  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.39/1.02  tff(c_45, plain, (![A_16, B_17]: (r1_tarski(k3_xboole_0(A_16, B_17), A_16))), inference(superposition, [status(thm), theory('equality')], [c_27, c_6])).
% 1.39/1.02  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.39/1.02  tff(c_49, plain, (![A_16, B_17]: (k2_xboole_0(k3_xboole_0(A_16, B_17), A_16)=A_16)), inference(resolution, [status(thm)], [c_45, c_4])).
% 1.39/1.02  tff(c_71, plain, (![A_22, C_23, B_24]: (r1_tarski(A_22, C_23) | ~r1_tarski(k2_xboole_0(A_22, B_24), C_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.39/1.02  tff(c_91, plain, (![A_29, B_30, C_31]: (r1_tarski(k3_xboole_0(A_29, B_30), C_31) | ~r1_tarski(A_29, C_31))), inference(superposition, [status(thm), theory('equality')], [c_49, c_71])).
% 1.39/1.02  tff(c_10, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.39/1.02  tff(c_97, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_91, c_10])).
% 1.39/1.02  tff(c_102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_97])).
% 1.39/1.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.39/1.02  
% 1.39/1.02  Inference rules
% 1.39/1.02  ----------------------
% 1.39/1.02  #Ref     : 0
% 1.39/1.02  #Sup     : 22
% 1.39/1.02  #Fact    : 0
% 1.39/1.02  #Define  : 0
% 1.39/1.02  #Split   : 0
% 1.39/1.02  #Chain   : 0
% 1.39/1.02  #Close   : 0
% 1.39/1.02  
% 1.39/1.02  Ordering : KBO
% 1.39/1.02  
% 1.39/1.02  Simplification rules
% 1.39/1.02  ----------------------
% 1.39/1.02  #Subsume      : 0
% 1.39/1.02  #Demod        : 2
% 1.39/1.02  #Tautology    : 9
% 1.39/1.02  #SimpNegUnit  : 0
% 1.39/1.02  #BackRed      : 0
% 1.39/1.02  
% 1.39/1.02  #Partial instantiations: 0
% 1.39/1.02  #Strategies tried      : 1
% 1.39/1.02  
% 1.39/1.02  Timing (in seconds)
% 1.39/1.02  ----------------------
% 1.59/1.03  Preprocessing        : 0.22
% 1.59/1.03  Parsing              : 0.12
% 1.59/1.03  CNF conversion       : 0.01
% 1.59/1.03  Main loop            : 0.11
% 1.59/1.03  Inferencing          : 0.05
% 1.59/1.03  Reduction            : 0.03
% 1.59/1.03  Demodulation         : 0.02
% 1.59/1.03  BG Simplification    : 0.01
% 1.59/1.03  Subsumption          : 0.01
% 1.59/1.03  Abstraction          : 0.01
% 1.59/1.03  MUC search           : 0.00
% 1.59/1.03  Cooper               : 0.00
% 1.59/1.03  Total                : 0.35
% 1.59/1.03  Index Insertion      : 0.00
% 1.59/1.03  Index Deletion       : 0.00
% 1.59/1.03  Index Matching       : 0.00
% 1.59/1.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
