%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:16 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   22 (  27 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_tarski(A,B)
          & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r2_xboole_0(A,B)
        & r1_tarski(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( ~ r2_hidden('#skF_1'(A_9,B_10),A_9)
      | ~ r2_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_17,plain,(
    ! [B_2] : ~ r2_xboole_0(B_2,B_2) ),
    inference(resolution,[status(thm)],[c_4,c_12])).

tff(c_8,plain,(
    r2_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_19,plain,(
    ! [A_12,C_13,B_14] :
      ( r2_xboole_0(A_12,C_13)
      | ~ r1_tarski(B_14,C_13)
      | ~ r2_xboole_0(A_12,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_23,plain,(
    ! [A_15] :
      ( r2_xboole_0(A_15,'#skF_3')
      | ~ r2_xboole_0(A_15,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_10,c_19])).

tff(c_26,plain,(
    r2_xboole_0('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_23])).

tff(c_30,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:48:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.05  
% 1.55/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.05  %$ r2_xboole_0 > r2_hidden > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.55/1.05  
% 1.55/1.05  %Foreground sorts:
% 1.55/1.05  
% 1.55/1.05  
% 1.55/1.05  %Background operators:
% 1.55/1.05  
% 1.55/1.05  
% 1.55/1.05  %Foreground operators:
% 1.55/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.55/1.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.55/1.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.55/1.05  tff('#skF_2', type, '#skF_2': $i).
% 1.55/1.05  tff('#skF_3', type, '#skF_3': $i).
% 1.55/1.05  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.55/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.55/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.55/1.05  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.55/1.05  
% 1.55/1.06  tff(f_35, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 1.55/1.06  tff(f_47, negated_conjecture, ~(![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 1.55/1.06  tff(f_41, axiom, (![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_xboole_1)).
% 1.55/1.06  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.55/1.06  tff(c_12, plain, (![A_9, B_10]: (~r2_hidden('#skF_1'(A_9, B_10), A_9) | ~r2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.55/1.06  tff(c_17, plain, (![B_2]: (~r2_xboole_0(B_2, B_2))), inference(resolution, [status(thm)], [c_4, c_12])).
% 1.55/1.06  tff(c_8, plain, (r2_xboole_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.55/1.06  tff(c_10, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.55/1.06  tff(c_19, plain, (![A_12, C_13, B_14]: (r2_xboole_0(A_12, C_13) | ~r1_tarski(B_14, C_13) | ~r2_xboole_0(A_12, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.55/1.06  tff(c_23, plain, (![A_15]: (r2_xboole_0(A_15, '#skF_3') | ~r2_xboole_0(A_15, '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_19])).
% 1.55/1.06  tff(c_26, plain, (r2_xboole_0('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_8, c_23])).
% 1.55/1.06  tff(c_30, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17, c_26])).
% 1.55/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.06  
% 1.55/1.06  Inference rules
% 1.55/1.06  ----------------------
% 1.55/1.06  #Ref     : 0
% 1.55/1.06  #Sup     : 3
% 1.55/1.06  #Fact    : 0
% 1.55/1.06  #Define  : 0
% 1.55/1.06  #Split   : 0
% 1.55/1.06  #Chain   : 0
% 1.55/1.06  #Close   : 0
% 1.55/1.06  
% 1.55/1.06  Ordering : KBO
% 1.55/1.06  
% 1.55/1.06  Simplification rules
% 1.55/1.06  ----------------------
% 1.55/1.06  #Subsume      : 0
% 1.55/1.06  #Demod        : 0
% 1.55/1.06  #Tautology    : 0
% 1.55/1.06  #SimpNegUnit  : 1
% 1.55/1.06  #BackRed      : 0
% 1.55/1.06  
% 1.55/1.06  #Partial instantiations: 0
% 1.55/1.06  #Strategies tried      : 1
% 1.55/1.06  
% 1.55/1.06  Timing (in seconds)
% 1.55/1.06  ----------------------
% 1.55/1.06  Preprocessing        : 0.23
% 1.55/1.06  Parsing              : 0.13
% 1.55/1.06  CNF conversion       : 0.02
% 1.55/1.06  Main loop            : 0.07
% 1.55/1.06  Inferencing          : 0.03
% 1.55/1.06  Reduction            : 0.02
% 1.55/1.06  Demodulation         : 0.01
% 1.55/1.06  BG Simplification    : 0.01
% 1.55/1.06  Subsumption          : 0.01
% 1.55/1.06  Abstraction          : 0.00
% 1.55/1.06  MUC search           : 0.00
% 1.55/1.06  Cooper               : 0.00
% 1.55/1.06  Total                : 0.32
% 1.55/1.06  Index Insertion      : 0.00
% 1.55/1.06  Index Deletion       : 0.00
% 1.55/1.06  Index Matching       : 0.00
% 1.55/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
