%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:15 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   22 (  24 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  29 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > #nlpp > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_tarski(A,B)
          & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_14,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12,plain,(
    r2_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | ~ r2_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_31,plain,(
    ! [C_19,B_20,A_21] :
      ( r2_hidden(C_19,B_20)
      | ~ r2_hidden(C_19,A_21)
      | ~ r1_tarski(A_21,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [A_22,B_23,B_24] :
      ( r2_hidden('#skF_2'(A_22,B_23),B_24)
      | ~ r1_tarski(B_23,B_24)
      | ~ r2_xboole_0(A_22,B_23) ) ),
    inference(resolution,[status(thm)],[c_10,c_31])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7),A_6)
      | ~ r2_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_47,plain,(
    ! [B_25,B_26] :
      ( ~ r1_tarski(B_25,B_26)
      | ~ r2_xboole_0(B_26,B_25) ) ),
    inference(resolution,[status(thm)],[c_38,c_8])).

tff(c_50,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_47])).

tff(c_54,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.19  
% 1.71/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.19  %$ r2_xboole_0 > r2_hidden > r1_tarski > #nlpp > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.71/1.19  
% 1.71/1.19  %Foreground sorts:
% 1.71/1.19  
% 1.71/1.19  
% 1.71/1.19  %Background operators:
% 1.71/1.19  
% 1.71/1.19  
% 1.71/1.19  %Foreground operators:
% 1.71/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.71/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.71/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.71/1.19  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.71/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.71/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.71/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.71/1.19  
% 1.71/1.20  tff(f_48, negated_conjecture, ~(![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 1.71/1.20  tff(f_42, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 1.71/1.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.71/1.20  tff(c_14, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.71/1.20  tff(c_12, plain, (r2_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.71/1.20  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | ~r2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.71/1.20  tff(c_31, plain, (![C_19, B_20, A_21]: (r2_hidden(C_19, B_20) | ~r2_hidden(C_19, A_21) | ~r1_tarski(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.71/1.20  tff(c_38, plain, (![A_22, B_23, B_24]: (r2_hidden('#skF_2'(A_22, B_23), B_24) | ~r1_tarski(B_23, B_24) | ~r2_xboole_0(A_22, B_23))), inference(resolution, [status(thm)], [c_10, c_31])).
% 1.71/1.20  tff(c_8, plain, (![A_6, B_7]: (~r2_hidden('#skF_2'(A_6, B_7), A_6) | ~r2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.71/1.20  tff(c_47, plain, (![B_25, B_26]: (~r1_tarski(B_25, B_26) | ~r2_xboole_0(B_26, B_25))), inference(resolution, [status(thm)], [c_38, c_8])).
% 1.71/1.20  tff(c_50, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_12, c_47])).
% 1.71/1.20  tff(c_54, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_50])).
% 1.71/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.71/1.20  
% 1.71/1.20  Inference rules
% 1.71/1.20  ----------------------
% 1.71/1.20  #Ref     : 0
% 1.71/1.20  #Sup     : 7
% 1.71/1.20  #Fact    : 0
% 1.71/1.20  #Define  : 0
% 1.71/1.20  #Split   : 0
% 1.71/1.20  #Chain   : 0
% 1.71/1.20  #Close   : 0
% 1.71/1.20  
% 1.71/1.20  Ordering : KBO
% 1.71/1.20  
% 1.71/1.20  Simplification rules
% 1.71/1.20  ----------------------
% 1.71/1.20  #Subsume      : 0
% 1.71/1.20  #Demod        : 1
% 1.71/1.20  #Tautology    : 0
% 1.71/1.20  #SimpNegUnit  : 0
% 1.71/1.20  #BackRed      : 0
% 1.71/1.20  
% 1.71/1.20  #Partial instantiations: 0
% 1.71/1.20  #Strategies tried      : 1
% 1.71/1.20  
% 1.71/1.20  Timing (in seconds)
% 1.71/1.20  ----------------------
% 1.71/1.20  Preprocessing        : 0.26
% 1.71/1.20  Parsing              : 0.14
% 1.77/1.20  CNF conversion       : 0.02
% 1.77/1.20  Main loop            : 0.11
% 1.77/1.20  Inferencing          : 0.05
% 1.77/1.20  Reduction            : 0.02
% 1.77/1.20  Demodulation         : 0.02
% 1.77/1.20  BG Simplification    : 0.01
% 1.77/1.20  Subsumption          : 0.02
% 1.77/1.20  Abstraction          : 0.00
% 1.77/1.20  MUC search           : 0.00
% 1.77/1.20  Cooper               : 0.00
% 1.77/1.20  Total                : 0.39
% 1.77/1.20  Index Insertion      : 0.00
% 1.77/1.20  Index Deletion       : 0.00
% 1.77/1.20  Index Matching       : 0.00
% 1.77/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
