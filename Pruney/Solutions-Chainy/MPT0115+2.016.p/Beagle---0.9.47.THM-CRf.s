%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:27 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   18 (  19 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10,plain,(
    ! [A_8,C_9,B_10] :
      ( r1_tarski(A_8,C_9)
      | ~ r1_tarski(B_10,C_9)
      | ~ r1_tarski(A_8,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_17,plain,(
    ! [A_11] :
      ( r1_tarski(A_11,'#skF_2')
      | ~ r1_tarski(A_11,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_10])).

tff(c_6,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_17,c_6])).

tff(c_27,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.14  
% 1.59/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.14  %$ r1_tarski > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.59/1.14  
% 1.59/1.14  %Foreground sorts:
% 1.59/1.14  
% 1.59/1.14  
% 1.59/1.14  %Background operators:
% 1.59/1.14  
% 1.59/1.14  
% 1.59/1.14  %Foreground operators:
% 1.59/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.59/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.59/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.59/1.14  
% 1.59/1.15  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.59/1.15  tff(f_38, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 1.59/1.15  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.59/1.15  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.59/1.15  tff(c_8, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.59/1.15  tff(c_10, plain, (![A_8, C_9, B_10]: (r1_tarski(A_8, C_9) | ~r1_tarski(B_10, C_9) | ~r1_tarski(A_8, B_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.59/1.15  tff(c_17, plain, (![A_11]: (r1_tarski(A_11, '#skF_2') | ~r1_tarski(A_11, '#skF_1'))), inference(resolution, [status(thm)], [c_8, c_10])).
% 1.59/1.15  tff(c_6, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.59/1.15  tff(c_22, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_17, c_6])).
% 1.59/1.15  tff(c_27, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 1.59/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.15  
% 1.59/1.15  Inference rules
% 1.59/1.15  ----------------------
% 1.59/1.15  #Ref     : 0
% 1.59/1.15  #Sup     : 4
% 1.59/1.15  #Fact    : 0
% 1.59/1.15  #Define  : 0
% 1.59/1.15  #Split   : 0
% 1.59/1.15  #Chain   : 0
% 1.59/1.15  #Close   : 0
% 1.59/1.15  
% 1.59/1.15  Ordering : KBO
% 1.59/1.15  
% 1.59/1.15  Simplification rules
% 1.59/1.15  ----------------------
% 1.59/1.15  #Subsume      : 0
% 1.59/1.15  #Demod        : 1
% 1.59/1.15  #Tautology    : 0
% 1.59/1.15  #SimpNegUnit  : 0
% 1.59/1.15  #BackRed      : 0
% 1.59/1.15  
% 1.59/1.15  #Partial instantiations: 0
% 1.59/1.15  #Strategies tried      : 1
% 1.59/1.15  
% 1.59/1.15  Timing (in seconds)
% 1.59/1.15  ----------------------
% 1.59/1.15  Preprocessing        : 0.26
% 1.59/1.15  Parsing              : 0.14
% 1.59/1.15  CNF conversion       : 0.02
% 1.59/1.15  Main loop            : 0.07
% 1.59/1.15  Inferencing          : 0.04
% 1.59/1.15  Reduction            : 0.02
% 1.59/1.15  Demodulation         : 0.02
% 1.59/1.15  BG Simplification    : 0.01
% 1.59/1.15  Subsumption          : 0.01
% 1.59/1.15  Abstraction          : 0.00
% 1.59/1.15  MUC search           : 0.00
% 1.59/1.15  Cooper               : 0.00
% 1.59/1.15  Total                : 0.35
% 1.59/1.15  Index Insertion      : 0.00
% 1.59/1.15  Index Deletion       : 0.00
% 1.59/1.15  Index Matching       : 0.00
% 1.59/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
