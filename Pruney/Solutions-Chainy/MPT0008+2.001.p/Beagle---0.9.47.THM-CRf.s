%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:28 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   24 (  29 expanded)
%              Number of leaves         :   11 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  48 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_39,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(B,C) )
       => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_8,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ! [C_10,B_11,A_12] :
      ( r2_hidden(C_10,B_11)
      | ~ r2_hidden(C_10,A_12)
      | ~ r1_tarski(A_12,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_25,plain,(
    ! [A_14,B_15,B_16] :
      ( r2_hidden('#skF_1'(A_14,B_15),B_16)
      | ~ r1_tarski(A_14,B_16)
      | r1_tarski(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_6,c_20])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    ! [A_17,B_18,B_19,B_20] :
      ( r2_hidden('#skF_1'(A_17,B_18),B_19)
      | ~ r1_tarski(B_20,B_19)
      | ~ r1_tarski(A_17,B_20)
      | r1_tarski(A_17,B_18) ) ),
    inference(resolution,[status(thm)],[c_25,c_2])).

tff(c_44,plain,(
    ! [A_21,B_22] :
      ( r2_hidden('#skF_1'(A_21,B_22),'#skF_4')
      | ~ r1_tarski(A_21,'#skF_3')
      | r1_tarski(A_21,B_22) ) ),
    inference(resolution,[status(thm)],[c_10,c_34])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_53,plain,(
    ! [A_23] :
      ( ~ r1_tarski(A_23,'#skF_3')
      | r1_tarski(A_23,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_4])).

tff(c_60,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_53])).

tff(c_66,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.14  
% 1.60/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.14  %$ r2_hidden > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.60/1.14  
% 1.60/1.14  %Foreground sorts:
% 1.60/1.14  
% 1.60/1.14  
% 1.60/1.14  %Background operators:
% 1.60/1.14  
% 1.60/1.14  
% 1.60/1.14  %Foreground operators:
% 1.60/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.60/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.60/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.60/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.60/1.14  
% 1.60/1.15  tff(f_39, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.60/1.15  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.60/1.15  tff(c_8, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.60/1.15  tff(c_12, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.60/1.15  tff(c_10, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.60/1.15  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.15  tff(c_20, plain, (![C_10, B_11, A_12]: (r2_hidden(C_10, B_11) | ~r2_hidden(C_10, A_12) | ~r1_tarski(A_12, B_11))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.15  tff(c_25, plain, (![A_14, B_15, B_16]: (r2_hidden('#skF_1'(A_14, B_15), B_16) | ~r1_tarski(A_14, B_16) | r1_tarski(A_14, B_15))), inference(resolution, [status(thm)], [c_6, c_20])).
% 1.60/1.15  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.15  tff(c_34, plain, (![A_17, B_18, B_19, B_20]: (r2_hidden('#skF_1'(A_17, B_18), B_19) | ~r1_tarski(B_20, B_19) | ~r1_tarski(A_17, B_20) | r1_tarski(A_17, B_18))), inference(resolution, [status(thm)], [c_25, c_2])).
% 1.60/1.15  tff(c_44, plain, (![A_21, B_22]: (r2_hidden('#skF_1'(A_21, B_22), '#skF_4') | ~r1_tarski(A_21, '#skF_3') | r1_tarski(A_21, B_22))), inference(resolution, [status(thm)], [c_10, c_34])).
% 1.60/1.15  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.15  tff(c_53, plain, (![A_23]: (~r1_tarski(A_23, '#skF_3') | r1_tarski(A_23, '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_4])).
% 1.60/1.15  tff(c_60, plain, (r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_12, c_53])).
% 1.60/1.15  tff(c_66, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_60])).
% 1.60/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.15  
% 1.60/1.15  Inference rules
% 1.60/1.15  ----------------------
% 1.60/1.15  #Ref     : 0
% 1.60/1.15  #Sup     : 11
% 1.60/1.15  #Fact    : 0
% 1.60/1.15  #Define  : 0
% 1.60/1.15  #Split   : 0
% 1.60/1.15  #Chain   : 0
% 1.60/1.15  #Close   : 0
% 1.60/1.15  
% 1.60/1.15  Ordering : KBO
% 1.60/1.15  
% 1.60/1.15  Simplification rules
% 1.60/1.15  ----------------------
% 1.60/1.15  #Subsume      : 1
% 1.60/1.15  #Demod        : 1
% 1.60/1.15  #Tautology    : 2
% 1.60/1.15  #SimpNegUnit  : 1
% 1.60/1.15  #BackRed      : 0
% 1.60/1.15  
% 1.60/1.15  #Partial instantiations: 0
% 1.60/1.15  #Strategies tried      : 1
% 1.60/1.15  
% 1.60/1.15  Timing (in seconds)
% 1.60/1.15  ----------------------
% 1.60/1.15  Preprocessing        : 0.26
% 1.60/1.15  Parsing              : 0.14
% 1.60/1.15  CNF conversion       : 0.02
% 1.60/1.15  Main loop            : 0.11
% 1.60/1.15  Inferencing          : 0.05
% 1.60/1.15  Reduction            : 0.02
% 1.60/1.15  Demodulation         : 0.02
% 1.60/1.15  BG Simplification    : 0.01
% 1.60/1.15  Subsumption          : 0.02
% 1.60/1.16  Abstraction          : 0.00
% 1.60/1.16  MUC search           : 0.00
% 1.60/1.16  Cooper               : 0.00
% 1.60/1.16  Total                : 0.40
% 1.60/1.16  Index Insertion      : 0.00
% 1.60/1.16  Index Deletion       : 0.00
% 1.60/1.16  Index Matching       : 0.00
% 1.60/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
