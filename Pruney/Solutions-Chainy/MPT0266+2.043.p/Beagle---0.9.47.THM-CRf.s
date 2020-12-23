%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:31 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   19 (  21 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k3_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_zfmisc_1)).

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

tff(c_40,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    ! [D_12,B_8] : r2_hidden(D_12,k2_tarski(D_12,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_42,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k2_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_57,plain,(
    ! [D_25] :
      ( r2_hidden(D_25,'#skF_7')
      | ~ r2_hidden(D_25,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_4])).

tff(c_65,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_57])).

tff(c_70,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.13  
% 1.64/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.13  %$ r2_hidden > k4_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 1.64/1.13  
% 1.64/1.13  %Foreground sorts:
% 1.64/1.13  
% 1.64/1.13  
% 1.64/1.13  %Background operators:
% 1.64/1.13  
% 1.64/1.13  
% 1.64/1.13  %Foreground operators:
% 1.64/1.13  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.13  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.64/1.13  tff('#skF_7', type, '#skF_7': $i).
% 1.64/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.64/1.13  tff('#skF_5', type, '#skF_5': $i).
% 1.64/1.13  tff('#skF_6', type, '#skF_6': $i).
% 1.64/1.13  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.64/1.13  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.13  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.64/1.13  
% 1.76/1.15  tff(f_50, negated_conjecture, ~(![A, B, C]: ((k3_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_zfmisc_1)).
% 1.76/1.15  tff(f_43, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.76/1.15  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.76/1.15  tff(c_40, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.76/1.15  tff(c_24, plain, (![D_12, B_8]: (r2_hidden(D_12, k2_tarski(D_12, B_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.76/1.15  tff(c_42, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k2_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.76/1.15  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.76/1.15  tff(c_57, plain, (![D_25]: (r2_hidden(D_25, '#skF_7') | ~r2_hidden(D_25, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_42, c_4])).
% 1.76/1.15  tff(c_65, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_24, c_57])).
% 1.76/1.15  tff(c_70, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_65])).
% 1.76/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.15  
% 1.76/1.15  Inference rules
% 1.76/1.15  ----------------------
% 1.76/1.15  #Ref     : 0
% 1.76/1.15  #Sup     : 6
% 1.76/1.15  #Fact    : 0
% 1.76/1.15  #Define  : 0
% 1.76/1.15  #Split   : 0
% 1.76/1.15  #Chain   : 0
% 1.76/1.15  #Close   : 0
% 1.76/1.15  
% 1.76/1.15  Ordering : KBO
% 1.76/1.15  
% 1.76/1.15  Simplification rules
% 1.76/1.15  ----------------------
% 1.76/1.15  #Subsume      : 0
% 1.76/1.15  #Demod        : 0
% 1.76/1.15  #Tautology    : 3
% 1.76/1.15  #SimpNegUnit  : 1
% 1.76/1.15  #BackRed      : 0
% 1.76/1.15  
% 1.76/1.15  #Partial instantiations: 0
% 1.76/1.15  #Strategies tried      : 1
% 1.76/1.15  
% 1.76/1.15  Timing (in seconds)
% 1.76/1.15  ----------------------
% 1.76/1.15  Preprocessing        : 0.29
% 1.76/1.15  Parsing              : 0.14
% 1.76/1.15  CNF conversion       : 0.02
% 1.76/1.15  Main loop            : 0.09
% 1.76/1.15  Inferencing          : 0.02
% 1.76/1.15  Reduction            : 0.03
% 1.76/1.15  Demodulation         : 0.02
% 1.76/1.15  BG Simplification    : 0.01
% 1.76/1.15  Subsumption          : 0.02
% 1.76/1.15  Abstraction          : 0.01
% 1.76/1.15  MUC search           : 0.00
% 1.76/1.15  Cooper               : 0.00
% 1.76/1.15  Total                : 0.41
% 1.76/1.15  Index Insertion      : 0.00
% 1.76/1.15  Index Deletion       : 0.00
% 1.76/1.16  Index Matching       : 0.00
% 1.76/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
