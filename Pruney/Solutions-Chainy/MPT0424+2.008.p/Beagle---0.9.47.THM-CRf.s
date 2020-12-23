%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:53 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.14  
% 1.59/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.14  %$ r2_hidden > r1_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 1.59/1.14  
% 1.59/1.14  %Foreground sorts:
% 1.59/1.14  
% 1.59/1.14  
% 1.59/1.14  %Background operators:
% 1.59/1.14  
% 1.59/1.14  
% 1.59/1.14  %Foreground operators:
% 1.59/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.59/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.59/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.59/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.14  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.59/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.14  
% 1.59/1.14  tff(f_42, negated_conjecture, ~(![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_setfam_1)).
% 1.59/1.14  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_zfmisc_1)).
% 1.59/1.14  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.59/1.14  tff(c_6, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.59/1.14  tff(c_8, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.59/1.14  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, k3_tarski(B_5)) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.59/1.14  tff(c_10, plain, (r1_tarski(k3_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.59/1.14  tff(c_12, plain, (![A_8, C_9, B_10]: (r1_tarski(A_8, C_9) | ~r1_tarski(B_10, C_9) | ~r1_tarski(A_8, B_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.59/1.14  tff(c_19, plain, (![A_11]: (r1_tarski(A_11, '#skF_2') | ~r1_tarski(A_11, k3_tarski('#skF_1')))), inference(resolution, [status(thm)], [c_10, c_12])).
% 1.59/1.14  tff(c_25, plain, (![A_12]: (r1_tarski(A_12, '#skF_2') | ~r2_hidden(A_12, '#skF_1'))), inference(resolution, [status(thm)], [c_4, c_19])).
% 1.59/1.14  tff(c_28, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_8, c_25])).
% 1.59/1.14  tff(c_32, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_28])).
% 1.59/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.14  
% 1.59/1.14  Inference rules
% 1.59/1.14  ----------------------
% 1.59/1.14  #Ref     : 0
% 1.59/1.14  #Sup     : 4
% 1.59/1.14  #Fact    : 0
% 1.59/1.14  #Define  : 0
% 1.59/1.14  #Split   : 0
% 1.59/1.14  #Chain   : 0
% 1.59/1.14  #Close   : 0
% 1.59/1.14  
% 1.59/1.14  Ordering : KBO
% 1.59/1.14  
% 1.59/1.14  Simplification rules
% 1.59/1.14  ----------------------
% 1.59/1.14  #Subsume      : 0
% 1.59/1.14  #Demod        : 0
% 1.59/1.14  #Tautology    : 0
% 1.59/1.14  #SimpNegUnit  : 1
% 1.59/1.14  #BackRed      : 0
% 1.59/1.14  
% 1.59/1.14  #Partial instantiations: 0
% 1.59/1.14  #Strategies tried      : 1
% 1.59/1.14  
% 1.59/1.14  Timing (in seconds)
% 1.59/1.14  ----------------------
% 1.59/1.15  Preprocessing        : 0.25
% 1.59/1.15  Parsing              : 0.14
% 1.59/1.15  CNF conversion       : 0.02
% 1.59/1.15  Main loop            : 0.07
% 1.59/1.15  Inferencing          : 0.03
% 1.59/1.15  Reduction            : 0.02
% 1.59/1.15  Demodulation         : 0.01
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
