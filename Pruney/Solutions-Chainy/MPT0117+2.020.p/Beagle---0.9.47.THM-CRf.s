%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:31 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   24 (  33 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  46 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B) )
       => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k4_xboole_0(A,B),C)
        & r1_tarski(k4_xboole_0(B,A),C) )
     => r1_tarski(k5_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_xboole_1)).

tff(c_8,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k4_xboole_0(A_1,C_3),B_2)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( r1_tarski(k5_xboole_0(A_10,B_11),C_12)
      | ~ r1_tarski(k4_xboole_0(B_11,A_10),C_12)
      | ~ r1_tarski(k4_xboole_0(A_10,B_11),C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_3','#skF_1'),'#skF_2')
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_6])).

tff(c_17,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_17])).

tff(c_24,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20])).

tff(c_25,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_3','#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_29,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_25])).

tff(c_33,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:07 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.09  
% 1.66/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.09  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.66/1.09  
% 1.66/1.09  %Foreground sorts:
% 1.66/1.09  
% 1.66/1.09  
% 1.66/1.09  %Background operators:
% 1.66/1.09  
% 1.66/1.09  
% 1.66/1.09  %Foreground operators:
% 1.66/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.66/1.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.66/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.09  
% 1.66/1.10  tff(f_42, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 1.66/1.10  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 1.66/1.10  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(k4_xboole_0(A, B), C) & r1_tarski(k4_xboole_0(B, A), C)) => r1_tarski(k5_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_xboole_1)).
% 1.66/1.10  tff(c_8, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.66/1.10  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k4_xboole_0(A_1, C_3), B_2) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.66/1.10  tff(c_10, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.66/1.10  tff(c_12, plain, (![A_10, B_11, C_12]: (r1_tarski(k5_xboole_0(A_10, B_11), C_12) | ~r1_tarski(k4_xboole_0(B_11, A_10), C_12) | ~r1_tarski(k4_xboole_0(A_10, B_11), C_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.66/1.10  tff(c_6, plain, (~r1_tarski(k5_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.66/1.10  tff(c_16, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_1'), '#skF_2') | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_12, c_6])).
% 1.66/1.10  tff(c_17, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_16])).
% 1.66/1.10  tff(c_20, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_2, c_17])).
% 1.66/1.10  tff(c_24, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_20])).
% 1.66/1.10  tff(c_25, plain, (~r1_tarski(k4_xboole_0('#skF_3', '#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_16])).
% 1.66/1.10  tff(c_29, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_2, c_25])).
% 1.66/1.10  tff(c_33, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_29])).
% 1.66/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.10  
% 1.66/1.10  Inference rules
% 1.66/1.10  ----------------------
% 1.66/1.10  #Ref     : 0
% 1.66/1.10  #Sup     : 3
% 1.66/1.10  #Fact    : 0
% 1.66/1.10  #Define  : 0
% 1.66/1.10  #Split   : 1
% 1.66/1.10  #Chain   : 0
% 1.66/1.10  #Close   : 0
% 1.66/1.10  
% 1.66/1.10  Ordering : KBO
% 1.66/1.10  
% 1.66/1.10  Simplification rules
% 1.66/1.10  ----------------------
% 1.66/1.10  #Subsume      : 0
% 1.66/1.10  #Demod        : 2
% 1.66/1.10  #Tautology    : 0
% 1.66/1.10  #SimpNegUnit  : 0
% 1.66/1.10  #BackRed      : 0
% 1.66/1.10  
% 1.66/1.10  #Partial instantiations: 0
% 1.66/1.10  #Strategies tried      : 1
% 1.66/1.10  
% 1.66/1.10  Timing (in seconds)
% 1.66/1.10  ----------------------
% 1.66/1.10  Preprocessing        : 0.25
% 1.66/1.10  Parsing              : 0.14
% 1.66/1.10  CNF conversion       : 0.02
% 1.66/1.10  Main loop            : 0.09
% 1.66/1.10  Inferencing          : 0.04
% 1.66/1.10  Reduction            : 0.02
% 1.66/1.10  Demodulation         : 0.02
% 1.66/1.10  BG Simplification    : 0.01
% 1.66/1.10  Subsumption          : 0.01
% 1.66/1.10  Abstraction          : 0.00
% 1.66/1.10  MUC search           : 0.00
% 1.66/1.10  Cooper               : 0.00
% 1.66/1.10  Total                : 0.37
% 1.66/1.10  Index Insertion      : 0.00
% 1.66/1.10  Index Deletion       : 0.00
% 1.66/1.10  Index Matching       : 0.00
% 1.66/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
