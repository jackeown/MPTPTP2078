%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:47 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :   20 (  26 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(k4_xboole_0(A,B),C)
          & r1_tarski(k4_xboole_0(B,A),C) )
       => r1_tarski(k5_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_10,plain,(
    r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    r1_tarski(k4_xboole_0('#skF_2','#skF_1'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k4_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_8,C_9,B_10] :
      ( r1_tarski(k2_xboole_0(A_8,C_9),B_10)
      | ~ r1_tarski(C_9,B_10)
      | ~ r1_tarski(A_8,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [A_11,B_12,B_13] :
      ( r1_tarski(k5_xboole_0(A_11,B_12),B_13)
      | ~ r1_tarski(k4_xboole_0(B_12,A_11),B_13)
      | ~ r1_tarski(k4_xboole_0(A_11,B_12),B_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_6,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_27,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),'#skF_3')
    | ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_6])).

tff(c_31,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n014.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 14:46:37 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.06  
% 1.54/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.06  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.54/1.06  
% 1.54/1.06  %Foreground sorts:
% 1.54/1.06  
% 1.54/1.06  
% 1.54/1.06  %Background operators:
% 1.54/1.06  
% 1.54/1.06  
% 1.54/1.06  %Foreground operators:
% 1.54/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.54/1.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.54/1.06  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.54/1.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.54/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.54/1.06  tff('#skF_3', type, '#skF_3': $i).
% 1.54/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.54/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.54/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.54/1.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.54/1.06  
% 1.54/1.06  tff(f_40, negated_conjecture, ~(![A, B, C]: ((r1_tarski(k4_xboole_0(A, B), C) & r1_tarski(k4_xboole_0(B, A), C)) => r1_tarski(k5_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_xboole_1)).
% 1.54/1.06  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 1.54/1.06  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.54/1.06  tff(c_10, plain, (r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.54/1.06  tff(c_8, plain, (r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.54/1.06  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k4_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.54/1.06  tff(c_20, plain, (![A_8, C_9, B_10]: (r1_tarski(k2_xboole_0(A_8, C_9), B_10) | ~r1_tarski(C_9, B_10) | ~r1_tarski(A_8, B_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.54/1.06  tff(c_24, plain, (![A_11, B_12, B_13]: (r1_tarski(k5_xboole_0(A_11, B_12), B_13) | ~r1_tarski(k4_xboole_0(B_12, A_11), B_13) | ~r1_tarski(k4_xboole_0(A_11, B_12), B_13))), inference(superposition, [status(thm), theory('equality')], [c_2, c_20])).
% 1.54/1.06  tff(c_6, plain, (~r1_tarski(k5_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.54/1.06  tff(c_27, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), '#skF_3') | ~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_24, c_6])).
% 1.54/1.06  tff(c_31, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_27])).
% 1.54/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.54/1.06  
% 1.54/1.06  Inference rules
% 1.54/1.06  ----------------------
% 1.54/1.06  #Ref     : 0
% 1.54/1.06  #Sup     : 4
% 1.54/1.06  #Fact    : 0
% 1.54/1.06  #Define  : 0
% 1.54/1.06  #Split   : 0
% 1.54/1.06  #Chain   : 0
% 1.54/1.06  #Close   : 0
% 1.54/1.06  
% 1.54/1.06  Ordering : KBO
% 1.54/1.06  
% 1.54/1.06  Simplification rules
% 1.54/1.06  ----------------------
% 1.54/1.06  #Subsume      : 0
% 1.54/1.06  #Demod        : 2
% 1.54/1.06  #Tautology    : 2
% 1.54/1.06  #SimpNegUnit  : 0
% 1.54/1.06  #BackRed      : 0
% 1.54/1.06  
% 1.54/1.06  #Partial instantiations: 0
% 1.54/1.06  #Strategies tried      : 1
% 1.54/1.06  
% 1.54/1.07  Timing (in seconds)
% 1.54/1.07  ----------------------
% 1.54/1.07  Preprocessing        : 0.25
% 1.54/1.07  Parsing              : 0.14
% 1.54/1.07  CNF conversion       : 0.01
% 1.54/1.07  Main loop            : 0.08
% 1.54/1.07  Inferencing          : 0.04
% 1.54/1.07  Reduction            : 0.02
% 1.54/1.07  Demodulation         : 0.02
% 1.54/1.07  BG Simplification    : 0.01
% 1.54/1.07  Subsumption          : 0.01
% 1.54/1.07  Abstraction          : 0.00
% 1.54/1.07  MUC search           : 0.00
% 1.54/1.07  Cooper               : 0.00
% 1.54/1.07  Total                : 0.35
% 1.54/1.07  Index Insertion      : 0.00
% 1.54/1.07  Index Deletion       : 0.00
% 1.54/1.07  Index Matching       : 0.00
% 1.54/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
