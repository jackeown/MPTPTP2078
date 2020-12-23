%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:12 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   30 (  31 expanded)
%              Number of leaves         :   21 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  30 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_48,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    ! [D_17,B_13] : r2_hidden(D_17,k2_tarski(D_17,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_50,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_6','#skF_7'),'#skF_8'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( ~ r2_hidden(D_11,A_6)
      | r2_hidden(D_11,k2_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_91,plain,(
    ! [C_41,B_42,A_43] :
      ( r2_hidden(C_41,B_42)
      | ~ r2_hidden(C_41,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_151,plain,(
    ! [D_56,B_57,A_58,B_59] :
      ( r2_hidden(D_56,B_57)
      | ~ r1_tarski(k2_xboole_0(A_58,B_59),B_57)
      | ~ r2_hidden(D_56,A_58) ) ),
    inference(resolution,[status(thm)],[c_12,c_91])).

tff(c_159,plain,(
    ! [D_60] :
      ( r2_hidden(D_60,'#skF_8')
      | ~ r2_hidden(D_60,k2_tarski('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_50,c_151])).

tff(c_171,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_30,c_159])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.27  
% 1.85/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.27  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_8 > #skF_3 > #skF_1
% 1.85/1.27  
% 1.85/1.27  %Foreground sorts:
% 1.85/1.27  
% 1.85/1.27  
% 1.85/1.27  %Background operators:
% 1.85/1.27  
% 1.85/1.27  
% 1.85/1.27  %Foreground operators:
% 1.85/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.85/1.27  tff('#skF_7', type, '#skF_7': $i).
% 1.85/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.85/1.27  tff('#skF_6', type, '#skF_6': $i).
% 1.85/1.27  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.85/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.85/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.85/1.27  tff('#skF_8', type, '#skF_8': $i).
% 1.85/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.85/1.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.85/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.85/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.85/1.27  
% 1.85/1.28  tff(f_59, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 1.85/1.28  tff(f_50, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.85/1.28  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.85/1.28  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.85/1.28  tff(c_48, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.85/1.28  tff(c_30, plain, (![D_17, B_13]: (r2_hidden(D_17, k2_tarski(D_17, B_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.85/1.28  tff(c_50, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), '#skF_8'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.85/1.28  tff(c_12, plain, (![D_11, A_6, B_7]: (~r2_hidden(D_11, A_6) | r2_hidden(D_11, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.85/1.28  tff(c_91, plain, (![C_41, B_42, A_43]: (r2_hidden(C_41, B_42) | ~r2_hidden(C_41, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.85/1.28  tff(c_151, plain, (![D_56, B_57, A_58, B_59]: (r2_hidden(D_56, B_57) | ~r1_tarski(k2_xboole_0(A_58, B_59), B_57) | ~r2_hidden(D_56, A_58))), inference(resolution, [status(thm)], [c_12, c_91])).
% 1.85/1.28  tff(c_159, plain, (![D_60]: (r2_hidden(D_60, '#skF_8') | ~r2_hidden(D_60, k2_tarski('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_50, c_151])).
% 1.85/1.28  tff(c_171, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_30, c_159])).
% 1.85/1.28  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_171])).
% 1.85/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.28  
% 1.85/1.28  Inference rules
% 1.85/1.28  ----------------------
% 1.85/1.28  #Ref     : 0
% 1.85/1.28  #Sup     : 25
% 1.85/1.28  #Fact    : 0
% 1.85/1.28  #Define  : 0
% 1.85/1.28  #Split   : 0
% 1.85/1.28  #Chain   : 0
% 1.85/1.28  #Close   : 0
% 1.85/1.28  
% 1.85/1.28  Ordering : KBO
% 1.85/1.28  
% 1.85/1.28  Simplification rules
% 1.85/1.28  ----------------------
% 1.85/1.28  #Subsume      : 1
% 1.85/1.28  #Demod        : 2
% 1.85/1.28  #Tautology    : 10
% 1.85/1.28  #SimpNegUnit  : 1
% 1.85/1.28  #BackRed      : 0
% 1.85/1.28  
% 1.85/1.28  #Partial instantiations: 0
% 1.85/1.28  #Strategies tried      : 1
% 1.85/1.28  
% 1.85/1.28  Timing (in seconds)
% 1.85/1.28  ----------------------
% 2.06/1.28  Preprocessing        : 0.33
% 2.06/1.28  Parsing              : 0.16
% 2.06/1.28  CNF conversion       : 0.03
% 2.06/1.28  Main loop            : 0.14
% 2.06/1.29  Inferencing          : 0.05
% 2.07/1.29  Reduction            : 0.04
% 2.07/1.29  Demodulation         : 0.03
% 2.07/1.29  BG Simplification    : 0.01
% 2.07/1.29  Subsumption          : 0.03
% 2.07/1.29  Abstraction          : 0.01
% 2.07/1.29  MUC search           : 0.00
% 2.07/1.29  Cooper               : 0.00
% 2.07/1.29  Total                : 0.49
% 2.07/1.29  Index Insertion      : 0.00
% 2.07/1.29  Index Deletion       : 0.00
% 2.07/1.29  Index Matching       : 0.00
% 2.07/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
