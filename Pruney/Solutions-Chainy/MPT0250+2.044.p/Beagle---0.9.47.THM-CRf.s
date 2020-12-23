%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:37 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   34 (  36 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  41 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_24,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_113,plain,(
    ! [A_35,B_36] :
      ( ~ r2_hidden('#skF_1'(A_35,B_36),B_36)
      | r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_118,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_113])).

tff(c_10,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,k2_xboole_0(C_10,B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_27,plain,(
    r1_tarski(k2_xboole_0('#skF_3',k1_tarski('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_26])).

tff(c_172,plain,(
    ! [A_50,C_51,B_52] :
      ( r1_tarski(A_50,C_51)
      | ~ r1_tarski(B_52,C_51)
      | ~ r1_tarski(A_50,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_209,plain,(
    ! [A_56] :
      ( r1_tarski(A_56,'#skF_3')
      | ~ r1_tarski(A_56,k2_xboole_0('#skF_3',k1_tarski('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_27,c_172])).

tff(c_231,plain,(
    ! [A_57] :
      ( r1_tarski(A_57,'#skF_3')
      | ~ r1_tarski(A_57,k1_tarski('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_209])).

tff(c_240,plain,(
    r1_tarski(k1_tarski('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_231])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,B_18)
      | ~ r1_tarski(k1_tarski(A_17),B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_246,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_240,c_18])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_246])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:57:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.31  
% 2.16/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.31  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.16/1.31  
% 2.16/1.31  %Foreground sorts:
% 2.16/1.31  
% 2.16/1.31  
% 2.16/1.31  %Background operators:
% 2.16/1.31  
% 2.16/1.31  
% 2.16/1.31  %Foreground operators:
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.16/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.31  
% 2.16/1.32  tff(f_59, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.16/1.32  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.16/1.32  tff(f_38, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.16/1.32  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.16/1.32  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.16/1.32  tff(f_52, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.16/1.32  tff(c_24, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.32  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.16/1.32  tff(c_113, plain, (![A_35, B_36]: (~r2_hidden('#skF_1'(A_35, B_36), B_36) | r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.16/1.32  tff(c_118, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_8, c_113])).
% 2.16/1.32  tff(c_10, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, k2_xboole_0(C_10, B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.16/1.32  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.16/1.32  tff(c_26, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.32  tff(c_27, plain, (r1_tarski(k2_xboole_0('#skF_3', k1_tarski('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_26])).
% 2.16/1.32  tff(c_172, plain, (![A_50, C_51, B_52]: (r1_tarski(A_50, C_51) | ~r1_tarski(B_52, C_51) | ~r1_tarski(A_50, B_52))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.16/1.32  tff(c_209, plain, (![A_56]: (r1_tarski(A_56, '#skF_3') | ~r1_tarski(A_56, k2_xboole_0('#skF_3', k1_tarski('#skF_2'))))), inference(resolution, [status(thm)], [c_27, c_172])).
% 2.16/1.32  tff(c_231, plain, (![A_57]: (r1_tarski(A_57, '#skF_3') | ~r1_tarski(A_57, k1_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_209])).
% 2.16/1.32  tff(c_240, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_118, c_231])).
% 2.16/1.32  tff(c_18, plain, (![A_17, B_18]: (r2_hidden(A_17, B_18) | ~r1_tarski(k1_tarski(A_17), B_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.16/1.32  tff(c_246, plain, (r2_hidden('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_240, c_18])).
% 2.16/1.32  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_246])).
% 2.16/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.32  
% 2.16/1.32  Inference rules
% 2.16/1.32  ----------------------
% 2.16/1.32  #Ref     : 0
% 2.16/1.32  #Sup     : 53
% 2.16/1.32  #Fact    : 0
% 2.16/1.32  #Define  : 0
% 2.16/1.32  #Split   : 0
% 2.16/1.32  #Chain   : 0
% 2.16/1.32  #Close   : 0
% 2.16/1.32  
% 2.16/1.32  Ordering : KBO
% 2.16/1.32  
% 2.16/1.32  Simplification rules
% 2.16/1.32  ----------------------
% 2.16/1.32  #Subsume      : 9
% 2.16/1.32  #Demod        : 2
% 2.16/1.32  #Tautology    : 20
% 2.16/1.32  #SimpNegUnit  : 1
% 2.16/1.32  #BackRed      : 0
% 2.16/1.32  
% 2.16/1.32  #Partial instantiations: 0
% 2.16/1.32  #Strategies tried      : 1
% 2.16/1.32  
% 2.16/1.32  Timing (in seconds)
% 2.16/1.32  ----------------------
% 2.16/1.32  Preprocessing        : 0.30
% 2.16/1.32  Parsing              : 0.16
% 2.16/1.32  CNF conversion       : 0.02
% 2.16/1.32  Main loop            : 0.24
% 2.16/1.32  Inferencing          : 0.09
% 2.16/1.32  Reduction            : 0.07
% 2.16/1.32  Demodulation         : 0.06
% 2.16/1.32  BG Simplification    : 0.01
% 2.16/1.32  Subsumption          : 0.04
% 2.16/1.32  Abstraction          : 0.01
% 2.16/1.33  MUC search           : 0.00
% 2.16/1.33  Cooper               : 0.00
% 2.16/1.33  Total                : 0.57
% 2.16/1.33  Index Insertion      : 0.00
% 2.16/1.33  Index Deletion       : 0.00
% 2.16/1.33  Index Matching       : 0.00
% 2.16/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
