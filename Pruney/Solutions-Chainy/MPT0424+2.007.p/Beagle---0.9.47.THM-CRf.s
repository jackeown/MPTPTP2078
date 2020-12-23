%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:53 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  28 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(k3_tarski(A),B)
          & r2_hidden(C,A) )
       => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_6,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,k3_tarski(B_5))
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    r1_tarski(k3_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [A_8,C_9,B_10] :
      ( r1_tarski(A_8,C_9)
      | ~ r1_tarski(B_10,C_9)
      | ~ r1_tarski(A_8,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_19,plain,(
    ! [A_11] :
      ( r1_tarski(A_11,'#skF_2')
      | ~ r1_tarski(A_11,k3_tarski('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_10,c_12])).

tff(c_25,plain,(
    ! [A_12] :
      ( r1_tarski(A_12,'#skF_2')
      | ~ r2_hidden(A_12,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_4,c_19])).

tff(c_28,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_25])).

tff(c_32,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:51:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.08  
% 1.54/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.08  %$ r2_hidden > r1_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 1.64/1.08  
% 1.64/1.08  %Foreground sorts:
% 1.64/1.08  
% 1.64/1.08  
% 1.64/1.08  %Background operators:
% 1.64/1.08  
% 1.64/1.08  
% 1.64/1.08  %Foreground operators:
% 1.64/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.08  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.08  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.64/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.08  
% 1.64/1.09  tff(f_42, negated_conjecture, ~(![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_setfam_1)).
% 1.64/1.09  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 1.64/1.09  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.64/1.09  tff(c_6, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.64/1.09  tff(c_8, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.64/1.09  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, k3_tarski(B_5)) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.64/1.09  tff(c_10, plain, (r1_tarski(k3_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.64/1.09  tff(c_12, plain, (![A_8, C_9, B_10]: (r1_tarski(A_8, C_9) | ~r1_tarski(B_10, C_9) | ~r1_tarski(A_8, B_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.09  tff(c_19, plain, (![A_11]: (r1_tarski(A_11, '#skF_2') | ~r1_tarski(A_11, k3_tarski('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_12])).
% 1.64/1.09  tff(c_25, plain, (![A_12]: (r1_tarski(A_12, '#skF_2') | ~r2_hidden(A_12, '#skF_1'))), inference(resolution, [status(thm)], [c_4, c_19])).
% 1.64/1.09  tff(c_28, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_8, c_25])).
% 1.64/1.09  tff(c_32, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_28])).
% 1.64/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.09  
% 1.64/1.09  Inference rules
% 1.64/1.09  ----------------------
% 1.64/1.09  #Ref     : 0
% 1.64/1.09  #Sup     : 4
% 1.64/1.09  #Fact    : 0
% 1.64/1.09  #Define  : 0
% 1.64/1.09  #Split   : 0
% 1.64/1.09  #Chain   : 0
% 1.64/1.09  #Close   : 0
% 1.64/1.09  
% 1.64/1.09  Ordering : KBO
% 1.64/1.09  
% 1.64/1.09  Simplification rules
% 1.64/1.09  ----------------------
% 1.64/1.09  #Subsume      : 0
% 1.64/1.09  #Demod        : 0
% 1.64/1.09  #Tautology    : 0
% 1.64/1.09  #SimpNegUnit  : 1
% 1.64/1.09  #BackRed      : 0
% 1.64/1.09  
% 1.64/1.09  #Partial instantiations: 0
% 1.64/1.09  #Strategies tried      : 1
% 1.64/1.09  
% 1.64/1.09  Timing (in seconds)
% 1.64/1.09  ----------------------
% 1.64/1.09  Preprocessing        : 0.25
% 1.64/1.09  Parsing              : 0.14
% 1.64/1.09  CNF conversion       : 0.01
% 1.64/1.09  Main loop            : 0.08
% 1.64/1.09  Inferencing          : 0.04
% 1.64/1.09  Reduction            : 0.02
% 1.64/1.09  Demodulation         : 0.01
% 1.64/1.09  BG Simplification    : 0.01
% 1.64/1.09  Subsumption          : 0.01
% 1.64/1.09  Abstraction          : 0.00
% 1.64/1.09  MUC search           : 0.00
% 1.64/1.09  Cooper               : 0.00
% 1.64/1.09  Total                : 0.36
% 1.64/1.09  Index Insertion      : 0.00
% 1.64/1.09  Index Deletion       : 0.00
% 1.64/1.09  Index Matching       : 0.00
% 1.64/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
