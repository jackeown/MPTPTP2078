%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:02 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   25 (  28 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   27 (  39 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_ordinal1 > #nlpp > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_ordinal1(C)
       => ( ( r2_hidden(A,B)
            & r2_hidden(B,C) )
         => r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_ordinal1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_20,plain,(
    v1_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_23,plain,(
    ! [B_12,A_13] :
      ( r1_tarski(B_12,A_13)
      | ~ r2_hidden(B_12,A_13)
      | ~ v1_ordinal1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_29,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ v1_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_23])).

tff(c_36,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_29])).

tff(c_18,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_51,plain,(
    ! [C_19,B_20,A_21] :
      ( r2_hidden(C_19,B_20)
      | ~ r2_hidden(C_19,A_21)
      | ~ r1_tarski(A_21,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [B_23] :
      ( r2_hidden('#skF_3',B_23)
      | ~ r1_tarski('#skF_4',B_23) ) ),
    inference(resolution,[status(thm)],[c_18,c_51])).

tff(c_14,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_80,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_14])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_80])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.08  
% 1.68/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.08  %$ r2_hidden > r1_tarski > v1_ordinal1 > #nlpp > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 1.68/1.08  
% 1.68/1.08  %Foreground sorts:
% 1.68/1.08  
% 1.68/1.08  
% 1.68/1.08  %Background operators:
% 1.68/1.08  
% 1.68/1.08  
% 1.68/1.08  %Foreground operators:
% 1.68/1.08  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.68/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.08  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 1.68/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.08  tff('#skF_5', type, '#skF_5': $i).
% 1.68/1.08  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.08  tff('#skF_4', type, '#skF_4': $i).
% 1.68/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.68/1.08  
% 1.68/1.09  tff(f_48, negated_conjecture, ~(![A, B, C]: (v1_ordinal1(C) => ((r2_hidden(A, B) & r2_hidden(B, C)) => r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_ordinal1)).
% 1.68/1.09  tff(f_39, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 1.68/1.09  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.68/1.09  tff(c_20, plain, (v1_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.68/1.09  tff(c_16, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.68/1.09  tff(c_23, plain, (![B_12, A_13]: (r1_tarski(B_12, A_13) | ~r2_hidden(B_12, A_13) | ~v1_ordinal1(A_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.68/1.09  tff(c_29, plain, (r1_tarski('#skF_4', '#skF_5') | ~v1_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_23])).
% 1.68/1.09  tff(c_36, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_29])).
% 1.68/1.09  tff(c_18, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.68/1.09  tff(c_51, plain, (![C_19, B_20, A_21]: (r2_hidden(C_19, B_20) | ~r2_hidden(C_19, A_21) | ~r1_tarski(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.68/1.09  tff(c_72, plain, (![B_23]: (r2_hidden('#skF_3', B_23) | ~r1_tarski('#skF_4', B_23))), inference(resolution, [status(thm)], [c_18, c_51])).
% 1.68/1.09  tff(c_14, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.68/1.09  tff(c_80, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_72, c_14])).
% 1.68/1.09  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_80])).
% 1.68/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.09  
% 1.68/1.09  Inference rules
% 1.68/1.09  ----------------------
% 1.68/1.09  #Ref     : 0
% 1.68/1.09  #Sup     : 14
% 1.68/1.09  #Fact    : 0
% 1.68/1.09  #Define  : 0
% 1.68/1.09  #Split   : 1
% 1.68/1.09  #Chain   : 0
% 1.68/1.09  #Close   : 0
% 1.68/1.09  
% 1.68/1.09  Ordering : KBO
% 1.68/1.09  
% 1.68/1.09  Simplification rules
% 1.68/1.09  ----------------------
% 1.68/1.09  #Subsume      : 0
% 1.68/1.09  #Demod        : 2
% 1.68/1.09  #Tautology    : 1
% 1.68/1.09  #SimpNegUnit  : 0
% 1.68/1.09  #BackRed      : 0
% 1.68/1.09  
% 1.68/1.09  #Partial instantiations: 0
% 1.68/1.09  #Strategies tried      : 1
% 1.68/1.09  
% 1.68/1.09  Timing (in seconds)
% 1.68/1.09  ----------------------
% 1.68/1.09  Preprocessing        : 0.25
% 1.68/1.09  Parsing              : 0.14
% 1.68/1.09  CNF conversion       : 0.02
% 1.68/1.09  Main loop            : 0.12
% 1.68/1.09  Inferencing          : 0.05
% 1.68/1.09  Reduction            : 0.03
% 1.68/1.09  Demodulation         : 0.02
% 1.68/1.09  BG Simplification    : 0.01
% 1.68/1.09  Subsumption          : 0.02
% 1.68/1.09  Abstraction          : 0.00
% 1.68/1.10  MUC search           : 0.00
% 1.68/1.10  Cooper               : 0.00
% 1.68/1.10  Total                : 0.39
% 1.68/1.10  Index Insertion      : 0.00
% 1.68/1.10  Index Deletion       : 0.00
% 1.68/1.10  Index Matching       : 0.00
% 1.68/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
