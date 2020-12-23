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
% DateTime   : Thu Dec  3 09:52:08 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :   22 (  28 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k3_xboole_0(k2_tarski(A,C),B) = k2_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_14,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18,plain,(
    ! [A_14,B_15,C_16] :
      ( r1_tarski(k2_tarski(A_14,B_15),C_16)
      | ~ r2_hidden(B_15,C_16)
      | ~ r2_hidden(A_14,C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    ! [A_17,B_18,C_19] :
      ( k3_xboole_0(k2_tarski(A_17,B_18),C_19) = k2_tarski(A_17,B_18)
      | ~ r2_hidden(B_18,C_19)
      | ~ r2_hidden(A_17,C_19) ) ),
    inference(resolution,[status(thm)],[c_18,c_2])).

tff(c_10,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != k2_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_37,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_10])).

tff(c_45,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.77  
% 1.89/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.77  %$ r2_hidden > r1_tarski > k3_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.89/1.77  
% 1.89/1.77  %Foreground sorts:
% 1.89/1.77  
% 1.89/1.77  
% 1.89/1.77  %Background operators:
% 1.89/1.77  
% 1.89/1.77  
% 1.89/1.77  %Foreground operators:
% 1.89/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.77  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.77  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.77  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.89/1.77  
% 1.89/1.79  tff(f_42, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k3_xboole_0(k2_tarski(A, C), B) = k2_tarski(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 1.89/1.79  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.89/1.79  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.89/1.79  tff(c_14, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.89/1.79  tff(c_12, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.89/1.79  tff(c_18, plain, (![A_14, B_15, C_16]: (r1_tarski(k2_tarski(A_14, B_15), C_16) | ~r2_hidden(B_15, C_16) | ~r2_hidden(A_14, C_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.89/1.79  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.89/1.79  tff(c_31, plain, (![A_17, B_18, C_19]: (k3_xboole_0(k2_tarski(A_17, B_18), C_19)=k2_tarski(A_17, B_18) | ~r2_hidden(B_18, C_19) | ~r2_hidden(A_17, C_19))), inference(resolution, [status(thm)], [c_18, c_2])).
% 1.89/1.79  tff(c_10, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!=k2_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.89/1.79  tff(c_37, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_31, c_10])).
% 1.89/1.79  tff(c_45, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_37])).
% 1.89/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.79  
% 1.89/1.79  Inference rules
% 1.89/1.79  ----------------------
% 1.89/1.79  #Ref     : 0
% 1.89/1.79  #Sup     : 6
% 1.89/1.79  #Fact    : 0
% 1.89/1.79  #Define  : 0
% 1.89/1.79  #Split   : 0
% 1.89/1.79  #Chain   : 0
% 1.89/1.79  #Close   : 0
% 1.89/1.79  
% 1.89/1.79  Ordering : KBO
% 1.89/1.79  
% 1.89/1.79  Simplification rules
% 1.89/1.79  ----------------------
% 1.89/1.79  #Subsume      : 0
% 1.89/1.79  #Demod        : 2
% 1.89/1.79  #Tautology    : 3
% 1.89/1.79  #SimpNegUnit  : 0
% 1.89/1.79  #BackRed      : 0
% 1.89/1.79  
% 1.89/1.79  #Partial instantiations: 0
% 1.89/1.79  #Strategies tried      : 1
% 1.89/1.79  
% 1.89/1.79  Timing (in seconds)
% 1.89/1.79  ----------------------
% 1.89/1.80  Preprocessing        : 0.49
% 1.89/1.80  Parsing              : 0.29
% 1.89/1.80  CNF conversion       : 0.04
% 1.89/1.80  Main loop            : 0.21
% 1.89/1.80  Inferencing          : 0.11
% 1.89/1.80  Reduction            : 0.04
% 1.89/1.80  Demodulation         : 0.03
% 1.89/1.80  BG Simplification    : 0.02
% 1.89/1.80  Subsumption          : 0.03
% 1.89/1.80  Abstraction          : 0.01
% 1.89/1.80  MUC search           : 0.00
% 1.89/1.80  Cooper               : 0.00
% 1.89/1.80  Total                : 0.74
% 1.89/1.80  Index Insertion      : 0.00
% 1.89/1.80  Index Deletion       : 0.00
% 1.89/1.80  Index Matching       : 0.00
% 1.89/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
