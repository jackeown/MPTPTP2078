%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:34 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   26 (  31 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  41 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k3_xboole_0(B,C))
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    r1_tarski('#skF_4',k3_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,(
    ! [C_23,B_24,A_25] :
      ( r2_hidden(C_23,B_24)
      | ~ r2_hidden(C_23,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [A_32,B_33,B_34] :
      ( r2_hidden('#skF_1'(A_32,B_33),B_34)
      | ~ r1_tarski(A_32,B_34)
      | r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_181,plain,(
    ! [A_50,B_51,A_52,B_53] :
      ( r2_hidden('#skF_1'(A_50,B_51),A_52)
      | ~ r1_tarski(A_50,k3_xboole_0(A_52,B_53))
      | r1_tarski(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_76,c_12])).

tff(c_197,plain,(
    ! [B_54] :
      ( r2_hidden('#skF_1'('#skF_4',B_54),'#skF_5')
      | r1_tarski('#skF_4',B_54) ) ),
    inference(resolution,[status(thm)],[c_28,c_181])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_203,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_197,c_4])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:57:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.21  
% 1.91/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.21  %$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.91/1.21  
% 1.91/1.21  %Foreground sorts:
% 1.91/1.21  
% 1.91/1.21  
% 1.91/1.21  %Background operators:
% 1.91/1.21  
% 1.91/1.21  
% 1.91/1.21  %Foreground operators:
% 1.91/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.91/1.21  tff('#skF_6', type, '#skF_6': $i).
% 1.91/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.91/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.91/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.91/1.21  
% 1.91/1.21  tff(f_46, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 1.91/1.21  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.91/1.21  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.91/1.21  tff(c_26, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.91/1.21  tff(c_28, plain, (r1_tarski('#skF_4', k3_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.91/1.21  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.21  tff(c_49, plain, (![C_23, B_24, A_25]: (r2_hidden(C_23, B_24) | ~r2_hidden(C_23, A_25) | ~r1_tarski(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.22  tff(c_76, plain, (![A_32, B_33, B_34]: (r2_hidden('#skF_1'(A_32, B_33), B_34) | ~r1_tarski(A_32, B_34) | r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_6, c_49])).
% 1.91/1.22  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.91/1.22  tff(c_181, plain, (![A_50, B_51, A_52, B_53]: (r2_hidden('#skF_1'(A_50, B_51), A_52) | ~r1_tarski(A_50, k3_xboole_0(A_52, B_53)) | r1_tarski(A_50, B_51))), inference(resolution, [status(thm)], [c_76, c_12])).
% 1.91/1.22  tff(c_197, plain, (![B_54]: (r2_hidden('#skF_1'('#skF_4', B_54), '#skF_5') | r1_tarski('#skF_4', B_54))), inference(resolution, [status(thm)], [c_28, c_181])).
% 1.91/1.22  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.22  tff(c_203, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_197, c_4])).
% 1.91/1.22  tff(c_208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_203])).
% 1.91/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.22  
% 1.91/1.22  Inference rules
% 1.91/1.22  ----------------------
% 1.91/1.22  #Ref     : 0
% 1.91/1.22  #Sup     : 37
% 1.91/1.22  #Fact    : 0
% 1.91/1.22  #Define  : 0
% 1.91/1.22  #Split   : 0
% 1.91/1.22  #Chain   : 0
% 1.91/1.22  #Close   : 0
% 1.91/1.22  
% 1.91/1.22  Ordering : KBO
% 1.91/1.22  
% 1.91/1.22  Simplification rules
% 1.91/1.22  ----------------------
% 1.91/1.22  #Subsume      : 1
% 1.91/1.22  #Demod        : 0
% 1.91/1.22  #Tautology    : 3
% 1.91/1.22  #SimpNegUnit  : 1
% 1.91/1.22  #BackRed      : 0
% 1.91/1.22  
% 1.91/1.22  #Partial instantiations: 0
% 1.91/1.22  #Strategies tried      : 1
% 1.91/1.22  
% 1.91/1.22  Timing (in seconds)
% 1.91/1.22  ----------------------
% 1.91/1.22  Preprocessing        : 0.27
% 1.91/1.22  Parsing              : 0.14
% 1.91/1.22  CNF conversion       : 0.02
% 1.91/1.22  Main loop            : 0.19
% 1.91/1.22  Inferencing          : 0.08
% 1.91/1.22  Reduction            : 0.04
% 1.91/1.22  Demodulation         : 0.03
% 1.91/1.22  BG Simplification    : 0.02
% 1.91/1.22  Subsumption          : 0.05
% 1.91/1.22  Abstraction          : 0.01
% 1.91/1.22  MUC search           : 0.00
% 1.91/1.22  Cooper               : 0.00
% 1.91/1.22  Total                : 0.48
% 1.91/1.22  Index Insertion      : 0.00
% 1.91/1.22  Index Deletion       : 0.00
% 1.91/1.22  Index Matching       : 0.00
% 1.91/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
