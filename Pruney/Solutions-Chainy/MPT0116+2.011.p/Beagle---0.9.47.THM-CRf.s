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
% DateTime   : Thu Dec  3 09:45:29 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.49s
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
%$ r1_tarski > k4_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10,plain,(
    ! [A_8,C_9,B_10] :
      ( r1_tarski(A_8,C_9)
      | ~ r1_tarski(B_10,C_9)
      | ~ r1_tarski(A_8,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_17,plain,(
    ! [A_11] :
      ( r1_tarski(A_11,'#skF_2')
      | ~ r1_tarski(A_11,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8,c_10])).

tff(c_6,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_17,c_6])).

tff(c_27,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.49/1.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.03  
% 1.49/1.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.04  %$ r1_tarski > k4_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.49/1.04  
% 1.49/1.04  %Foreground sorts:
% 1.49/1.04  
% 1.49/1.04  
% 1.49/1.04  %Background operators:
% 1.49/1.04  
% 1.49/1.04  
% 1.49/1.04  %Foreground operators:
% 1.49/1.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.49/1.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.49/1.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.49/1.04  tff('#skF_2', type, '#skF_2': $i).
% 1.49/1.04  tff('#skF_3', type, '#skF_3': $i).
% 1.49/1.04  tff('#skF_1', type, '#skF_1': $i).
% 1.49/1.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.49/1.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.49/1.04  
% 1.49/1.04  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.49/1.04  tff(f_38, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 1.49/1.04  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.49/1.04  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.49/1.04  tff(c_8, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.49/1.04  tff(c_10, plain, (![A_8, C_9, B_10]: (r1_tarski(A_8, C_9) | ~r1_tarski(B_10, C_9) | ~r1_tarski(A_8, B_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.49/1.04  tff(c_17, plain, (![A_11]: (r1_tarski(A_11, '#skF_2') | ~r1_tarski(A_11, '#skF_1'))), inference(resolution, [status(thm)], [c_8, c_10])).
% 1.49/1.04  tff(c_6, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.49/1.04  tff(c_22, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_17, c_6])).
% 1.49/1.04  tff(c_27, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_22])).
% 1.49/1.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.04  
% 1.49/1.04  Inference rules
% 1.49/1.04  ----------------------
% 1.49/1.04  #Ref     : 0
% 1.49/1.04  #Sup     : 4
% 1.49/1.04  #Fact    : 0
% 1.49/1.04  #Define  : 0
% 1.49/1.04  #Split   : 0
% 1.49/1.04  #Chain   : 0
% 1.49/1.04  #Close   : 0
% 1.49/1.04  
% 1.49/1.04  Ordering : KBO
% 1.49/1.04  
% 1.49/1.04  Simplification rules
% 1.49/1.04  ----------------------
% 1.49/1.04  #Subsume      : 0
% 1.49/1.04  #Demod        : 1
% 1.49/1.04  #Tautology    : 0
% 1.49/1.04  #SimpNegUnit  : 0
% 1.49/1.04  #BackRed      : 0
% 1.49/1.04  
% 1.49/1.04  #Partial instantiations: 0
% 1.49/1.04  #Strategies tried      : 1
% 1.49/1.04  
% 1.49/1.04  Timing (in seconds)
% 1.49/1.04  ----------------------
% 1.49/1.05  Preprocessing        : 0.23
% 1.49/1.05  Parsing              : 0.13
% 1.49/1.05  CNF conversion       : 0.01
% 1.49/1.05  Main loop            : 0.07
% 1.49/1.05  Inferencing          : 0.03
% 1.49/1.05  Reduction            : 0.02
% 1.49/1.05  Demodulation         : 0.01
% 1.49/1.05  BG Simplification    : 0.01
% 1.49/1.05  Subsumption          : 0.01
% 1.49/1.05  Abstraction          : 0.00
% 1.49/1.05  MUC search           : 0.00
% 1.49/1.05  Cooper               : 0.00
% 1.49/1.05  Total                : 0.32
% 1.49/1.05  Index Insertion      : 0.00
% 1.49/1.05  Index Deletion       : 0.00
% 1.49/1.05  Index Matching       : 0.00
% 1.49/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
