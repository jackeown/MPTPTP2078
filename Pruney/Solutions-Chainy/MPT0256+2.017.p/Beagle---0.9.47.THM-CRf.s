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
% DateTime   : Thu Dec  3 09:52:04 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   27 (  28 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    4
%              Number of atoms          :   22 (  24 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
       => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_42,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_38,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,(
    ! [D_17,B_18] : r2_hidden(D_17,k2_tarski(D_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_57,plain,(
    ! [A_13] : r2_hidden(A_13,k1_tarski(A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_54])).

tff(c_44,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_77,plain,(
    ! [D_24,A_25,B_26] :
      ( r2_hidden(D_24,A_25)
      | ~ r2_hidden(D_24,k3_xboole_0(A_25,B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_81,plain,(
    ! [D_27] :
      ( r2_hidden(D_27,'#skF_5')
      | ~ r2_hidden(D_27,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_77])).

tff(c_85,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_57,c_81])).

tff(c_89,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:21:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.12  
% 1.66/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.13  %$ r2_hidden > k2_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 1.66/1.13  
% 1.66/1.13  %Foreground sorts:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Background operators:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Foreground operators:
% 1.66/1.13  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.13  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.66/1.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.66/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.66/1.13  tff('#skF_5', type, '#skF_5': $i).
% 1.66/1.13  tff('#skF_6', type, '#skF_6': $i).
% 1.66/1.13  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.13  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.66/1.13  
% 1.66/1.13  tff(f_52, negated_conjecture, ~(![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 1.66/1.13  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.66/1.13  tff(f_43, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.66/1.13  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.66/1.13  tff(c_42, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.66/1.13  tff(c_38, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.66/1.13  tff(c_54, plain, (![D_17, B_18]: (r2_hidden(D_17, k2_tarski(D_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.66/1.13  tff(c_57, plain, (![A_13]: (r2_hidden(A_13, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_54])).
% 1.66/1.13  tff(c_44, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.66/1.13  tff(c_77, plain, (![D_24, A_25, B_26]: (r2_hidden(D_24, A_25) | ~r2_hidden(D_24, k3_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.66/1.13  tff(c_81, plain, (![D_27]: (r2_hidden(D_27, '#skF_5') | ~r2_hidden(D_27, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_44, c_77])).
% 1.66/1.13  tff(c_85, plain, (r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_57, c_81])).
% 1.66/1.13  tff(c_89, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_85])).
% 1.66/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.13  
% 1.66/1.13  Inference rules
% 1.66/1.13  ----------------------
% 1.66/1.13  #Ref     : 0
% 1.66/1.13  #Sup     : 10
% 1.66/1.13  #Fact    : 0
% 1.66/1.13  #Define  : 0
% 1.66/1.13  #Split   : 0
% 1.66/1.13  #Chain   : 0
% 1.66/1.13  #Close   : 0
% 1.66/1.13  
% 1.66/1.13  Ordering : KBO
% 1.66/1.13  
% 1.66/1.13  Simplification rules
% 1.66/1.13  ----------------------
% 1.66/1.13  #Subsume      : 0
% 1.66/1.13  #Demod        : 1
% 1.66/1.13  #Tautology    : 7
% 1.66/1.13  #SimpNegUnit  : 1
% 1.66/1.13  #BackRed      : 0
% 1.66/1.13  
% 1.66/1.13  #Partial instantiations: 0
% 1.66/1.13  #Strategies tried      : 1
% 1.66/1.13  
% 1.66/1.13  Timing (in seconds)
% 1.66/1.13  ----------------------
% 1.66/1.14  Preprocessing        : 0.28
% 1.66/1.14  Parsing              : 0.14
% 1.66/1.14  CNF conversion       : 0.02
% 1.66/1.14  Main loop            : 0.09
% 1.66/1.14  Inferencing          : 0.02
% 1.66/1.14  Reduction            : 0.03
% 1.66/1.14  Demodulation         : 0.02
% 1.66/1.14  BG Simplification    : 0.01
% 1.66/1.14  Subsumption          : 0.02
% 1.66/1.14  Abstraction          : 0.01
% 1.66/1.14  MUC search           : 0.00
% 1.66/1.14  Cooper               : 0.00
% 1.66/1.14  Total                : 0.39
% 1.66/1.14  Index Insertion      : 0.00
% 1.66/1.14  Index Deletion       : 0.00
% 1.66/1.14  Index Matching       : 0.00
% 1.66/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
