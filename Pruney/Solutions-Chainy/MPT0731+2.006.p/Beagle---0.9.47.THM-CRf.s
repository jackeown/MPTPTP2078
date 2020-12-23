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
% DateTime   : Thu Dec  3 10:06:01 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   23 (  24 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :   19 (  22 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,negated_conjecture,(
    ~ ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_36,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_46,plain,(
    ! [A_17,B_18] :
      ( r2_hidden('#skF_1'(A_17,B_18),A_17)
      | r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    ! [A_17] : r1_tarski(A_17,A_17) ),
    inference(resolution,[status(thm)],[c_46,c_4])).

tff(c_14,plain,(
    k1_ordinal1('#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_19,plain,(
    ! [A_10] : r2_hidden(A_10,k1_ordinal1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    r2_hidden('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_19])).

tff(c_32,plain,(
    ! [B_12,A_13] :
      ( ~ r1_tarski(B_12,A_13)
      | ~ r2_hidden(A_13,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_39,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_32])).

tff(c_68,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:44:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.15  
% 1.66/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.15  %$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 1.66/1.15  
% 1.66/1.15  %Foreground sorts:
% 1.66/1.15  
% 1.66/1.15  
% 1.66/1.15  %Background operators:
% 1.66/1.15  
% 1.66/1.15  
% 1.66/1.15  %Foreground operators:
% 1.66/1.15  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.66/1.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.66/1.15  
% 1.71/1.16  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.71/1.16  tff(f_45, negated_conjecture, ~(![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_ordinal1)).
% 1.71/1.16  tff(f_36, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 1.71/1.16  tff(f_41, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.71/1.16  tff(c_46, plain, (![A_17, B_18]: (r2_hidden('#skF_1'(A_17, B_18), A_17) | r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.71/1.16  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.71/1.16  tff(c_54, plain, (![A_17]: (r1_tarski(A_17, A_17))), inference(resolution, [status(thm)], [c_46, c_4])).
% 1.71/1.16  tff(c_14, plain, (k1_ordinal1('#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.71/1.16  tff(c_19, plain, (![A_10]: (r2_hidden(A_10, k1_ordinal1(A_10)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.71/1.16  tff(c_22, plain, (r2_hidden('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14, c_19])).
% 1.71/1.16  tff(c_32, plain, (![B_12, A_13]: (~r1_tarski(B_12, A_13) | ~r2_hidden(A_13, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.71/1.16  tff(c_39, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_32])).
% 1.71/1.16  tff(c_68, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_39])).
% 1.71/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.16  
% 1.71/1.16  Inference rules
% 1.71/1.16  ----------------------
% 1.71/1.16  #Ref     : 0
% 1.71/1.16  #Sup     : 13
% 1.71/1.16  #Fact    : 0
% 1.71/1.16  #Define  : 0
% 1.71/1.16  #Split   : 0
% 1.71/1.16  #Chain   : 0
% 1.71/1.16  #Close   : 0
% 1.71/1.16  
% 1.71/1.16  Ordering : KBO
% 1.71/1.16  
% 1.71/1.16  Simplification rules
% 1.71/1.16  ----------------------
% 1.71/1.16  #Subsume      : 1
% 1.71/1.16  #Demod        : 1
% 1.71/1.16  #Tautology    : 4
% 1.71/1.16  #SimpNegUnit  : 0
% 1.71/1.16  #BackRed      : 1
% 1.71/1.16  
% 1.71/1.16  #Partial instantiations: 0
% 1.71/1.16  #Strategies tried      : 1
% 1.71/1.16  
% 1.71/1.16  Timing (in seconds)
% 1.71/1.16  ----------------------
% 1.71/1.16  Preprocessing        : 0.26
% 1.71/1.17  Parsing              : 0.15
% 1.71/1.17  CNF conversion       : 0.02
% 1.71/1.17  Main loop            : 0.10
% 1.71/1.17  Inferencing          : 0.05
% 1.71/1.17  Reduction            : 0.02
% 1.71/1.17  Demodulation         : 0.02
% 1.71/1.17  BG Simplification    : 0.01
% 1.71/1.17  Subsumption          : 0.02
% 1.71/1.17  Abstraction          : 0.00
% 1.71/1.17  MUC search           : 0.00
% 1.71/1.17  Cooper               : 0.00
% 1.71/1.17  Total                : 0.38
% 1.71/1.17  Index Insertion      : 0.00
% 1.71/1.17  Index Deletion       : 0.00
% 1.71/1.17  Index Matching       : 0.00
% 1.71/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
