%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:27 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  21 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

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

tff(c_10,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k2_xboole_0(A_10,B_11) = B_11
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_29,plain,(
    ! [A_15,B_16] : k2_xboole_0(k3_xboole_0(A_15,B_16),A_15) = A_15 ),
    inference(resolution,[status(thm)],[c_6,c_12])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ! [A_18,B_19,C_20] :
      ( r1_tarski(k3_xboole_0(A_18,B_19),C_20)
      | ~ r1_tarski(A_18,C_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_2])).

tff(c_8,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_48,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_8])).

tff(c_53,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n023.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 13:47:06 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.50/1.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.04  
% 1.50/1.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.05  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.50/1.05  
% 1.50/1.05  %Foreground sorts:
% 1.50/1.05  
% 1.50/1.05  
% 1.50/1.05  %Background operators:
% 1.50/1.05  
% 1.50/1.05  
% 1.50/1.05  %Foreground operators:
% 1.50/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.50/1.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.50/1.05  tff('#skF_2', type, '#skF_2': $i).
% 1.50/1.05  tff('#skF_3', type, '#skF_3': $i).
% 1.50/1.05  tff('#skF_1', type, '#skF_1': $i).
% 1.50/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.50/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.50/1.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.50/1.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.50/1.05  
% 1.50/1.05  tff(f_40, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 1.50/1.05  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.50/1.05  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.50/1.05  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.50/1.05  tff(c_10, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.50/1.05  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.50/1.05  tff(c_12, plain, (![A_10, B_11]: (k2_xboole_0(A_10, B_11)=B_11 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.50/1.05  tff(c_29, plain, (![A_15, B_16]: (k2_xboole_0(k3_xboole_0(A_15, B_16), A_15)=A_15)), inference(resolution, [status(thm)], [c_6, c_12])).
% 1.50/1.05  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.50/1.05  tff(c_42, plain, (![A_18, B_19, C_20]: (r1_tarski(k3_xboole_0(A_18, B_19), C_20) | ~r1_tarski(A_18, C_20))), inference(superposition, [status(thm), theory('equality')], [c_29, c_2])).
% 1.50/1.05  tff(c_8, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.50/1.05  tff(c_48, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_8])).
% 1.50/1.05  tff(c_53, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_48])).
% 1.50/1.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.05  
% 1.50/1.05  Inference rules
% 1.50/1.05  ----------------------
% 1.50/1.05  #Ref     : 0
% 1.50/1.05  #Sup     : 10
% 1.50/1.05  #Fact    : 0
% 1.50/1.05  #Define  : 0
% 1.50/1.05  #Split   : 0
% 1.50/1.05  #Chain   : 0
% 1.50/1.05  #Close   : 0
% 1.50/1.05  
% 1.50/1.05  Ordering : KBO
% 1.50/1.05  
% 1.50/1.05  Simplification rules
% 1.50/1.05  ----------------------
% 1.50/1.05  #Subsume      : 0
% 1.50/1.05  #Demod        : 1
% 1.50/1.05  #Tautology    : 4
% 1.50/1.05  #SimpNegUnit  : 0
% 1.50/1.05  #BackRed      : 0
% 1.50/1.05  
% 1.50/1.05  #Partial instantiations: 0
% 1.50/1.05  #Strategies tried      : 1
% 1.50/1.05  
% 1.50/1.05  Timing (in seconds)
% 1.50/1.05  ----------------------
% 1.50/1.06  Preprocessing        : 0.24
% 1.50/1.06  Parsing              : 0.14
% 1.50/1.06  CNF conversion       : 0.01
% 1.50/1.06  Main loop            : 0.08
% 1.50/1.06  Inferencing          : 0.04
% 1.50/1.06  Reduction            : 0.02
% 1.50/1.06  Demodulation         : 0.02
% 1.50/1.06  BG Simplification    : 0.01
% 1.50/1.06  Subsumption          : 0.01
% 1.50/1.06  Abstraction          : 0.00
% 1.50/1.06  MUC search           : 0.00
% 1.50/1.06  Cooper               : 0.00
% 1.50/1.06  Total                : 0.35
% 1.50/1.06  Index Insertion      : 0.00
% 1.50/1.06  Index Deletion       : 0.00
% 1.50/1.06  Index Matching       : 0.00
% 1.50/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
