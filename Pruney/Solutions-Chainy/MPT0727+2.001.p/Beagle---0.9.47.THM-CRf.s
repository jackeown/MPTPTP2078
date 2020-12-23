%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:54 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   20 (  25 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  33 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_43,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_hidden(A,B)
          & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_10,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_29,plain,(
    ! [C_17,B_18,A_19] :
      ( r2_hidden(C_17,B_18)
      | ~ r2_hidden(C_17,A_19)
      | ~ r1_tarski(A_19,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_35,plain,(
    ! [B_18] :
      ( r2_hidden('#skF_2',B_18)
      | ~ r1_tarski('#skF_3',B_18) ) ),
    inference(resolution,[status(thm)],[c_12,c_29])).

tff(c_36,plain,(
    ! [B_20] :
      ( r2_hidden('#skF_2',B_20)
      | ~ r1_tarski('#skF_3',B_20) ) ),
    inference(resolution,[status(thm)],[c_12,c_29])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_48,plain,(
    ! [B_21] :
      ( ~ r2_hidden(B_21,'#skF_2')
      | ~ r1_tarski('#skF_3',B_21) ) ),
    inference(resolution,[status(thm)],[c_36,c_2])).

tff(c_52,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_35,c_48])).

tff(c_60,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.09  
% 1.63/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.10  %$ r2_hidden > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.63/1.10  
% 1.63/1.10  %Foreground sorts:
% 1.63/1.10  
% 1.63/1.10  
% 1.63/1.10  %Background operators:
% 1.63/1.10  
% 1.63/1.10  
% 1.63/1.10  %Foreground operators:
% 1.63/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.63/1.10  
% 1.63/1.10  tff(f_43, negated_conjecture, ~(![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.63/1.10  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.63/1.10  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 1.63/1.10  tff(c_10, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.63/1.10  tff(c_12, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.63/1.10  tff(c_29, plain, (![C_17, B_18, A_19]: (r2_hidden(C_17, B_18) | ~r2_hidden(C_17, A_19) | ~r1_tarski(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.63/1.10  tff(c_35, plain, (![B_18]: (r2_hidden('#skF_2', B_18) | ~r1_tarski('#skF_3', B_18))), inference(resolution, [status(thm)], [c_12, c_29])).
% 1.63/1.10  tff(c_36, plain, (![B_20]: (r2_hidden('#skF_2', B_20) | ~r1_tarski('#skF_3', B_20))), inference(resolution, [status(thm)], [c_12, c_29])).
% 1.63/1.10  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.63/1.10  tff(c_48, plain, (![B_21]: (~r2_hidden(B_21, '#skF_2') | ~r1_tarski('#skF_3', B_21))), inference(resolution, [status(thm)], [c_36, c_2])).
% 1.63/1.10  tff(c_52, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_35, c_48])).
% 1.63/1.10  tff(c_60, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_52])).
% 1.63/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.10  
% 1.63/1.10  Inference rules
% 1.63/1.10  ----------------------
% 1.63/1.10  #Ref     : 0
% 1.63/1.10  #Sup     : 10
% 1.63/1.10  #Fact    : 0
% 1.63/1.10  #Define  : 0
% 1.63/1.10  #Split   : 0
% 1.63/1.10  #Chain   : 0
% 1.63/1.10  #Close   : 0
% 1.63/1.10  
% 1.63/1.10  Ordering : KBO
% 1.63/1.10  
% 1.63/1.10  Simplification rules
% 1.63/1.10  ----------------------
% 1.63/1.10  #Subsume      : 0
% 1.63/1.10  #Demod        : 1
% 1.63/1.10  #Tautology    : 0
% 1.63/1.10  #SimpNegUnit  : 0
% 1.63/1.10  #BackRed      : 0
% 1.63/1.10  
% 1.63/1.10  #Partial instantiations: 0
% 1.63/1.10  #Strategies tried      : 1
% 1.63/1.10  
% 1.63/1.10  Timing (in seconds)
% 1.63/1.10  ----------------------
% 1.63/1.11  Preprocessing        : 0.24
% 1.63/1.11  Parsing              : 0.14
% 1.63/1.11  CNF conversion       : 0.02
% 1.63/1.11  Main loop            : 0.10
% 1.63/1.11  Inferencing          : 0.05
% 1.63/1.11  Reduction            : 0.02
% 1.63/1.11  Demodulation         : 0.02
% 1.63/1.11  BG Simplification    : 0.01
% 1.63/1.11  Subsumption          : 0.02
% 1.63/1.11  Abstraction          : 0.00
% 1.63/1.11  MUC search           : 0.00
% 1.63/1.11  Cooper               : 0.00
% 1.63/1.11  Total                : 0.36
% 1.63/1.11  Index Insertion      : 0.00
% 1.63/1.11  Index Deletion       : 0.00
% 1.63/1.11  Index Matching       : 0.00
% 1.63/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
