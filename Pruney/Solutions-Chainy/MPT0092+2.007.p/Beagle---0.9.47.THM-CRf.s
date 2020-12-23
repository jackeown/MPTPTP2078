%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:29 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   35 (  43 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_34,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_4'(A_12,B_13),A_12)
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_78,plain,(
    ! [C_35,B_36,A_37] :
      ( r2_hidden(C_35,B_36)
      | ~ r2_hidden(C_35,A_37)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,(
    ! [A_12,B_13,B_36] :
      ( r2_hidden('#skF_4'(A_12,B_13),B_36)
      | ~ r1_tarski(A_12,B_36)
      | r1_xboole_0(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_30,c_78])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_4'(A_12,B_13),B_13)
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_61,plain,(
    ! [D_29,B_30,A_31] :
      ( ~ r2_hidden(D_29,B_30)
      | ~ r2_hidden(D_29,k4_xboole_0(A_31,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_805,plain,(
    ! [A_145,A_146,B_147] :
      ( ~ r2_hidden('#skF_4'(A_145,k4_xboole_0(A_146,B_147)),B_147)
      | r1_xboole_0(A_145,k4_xboole_0(A_146,B_147)) ) ),
    inference(resolution,[status(thm)],[c_28,c_61])).

tff(c_839,plain,(
    ! [A_153,B_154,A_155] :
      ( ~ r1_tarski(A_153,B_154)
      | r1_xboole_0(A_153,k4_xboole_0(A_155,B_154)) ) ),
    inference(resolution,[status(thm)],[c_86,c_805])).

tff(c_32,plain,(
    ~ r1_xboole_0('#skF_5',k4_xboole_0('#skF_7','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_844,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_839,c_32])).

tff(c_849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_844])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.48  
% 3.23/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.49  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.23/1.49  
% 3.23/1.49  %Foreground sorts:
% 3.23/1.49  
% 3.23/1.49  
% 3.23/1.49  %Background operators:
% 3.23/1.49  
% 3.23/1.49  
% 3.23/1.49  %Foreground operators:
% 3.23/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.23/1.49  tff('#skF_7', type, '#skF_7': $i).
% 3.23/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.23/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.23/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.23/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.23/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.23/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.23/1.49  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.23/1.49  
% 3.23/1.50  tff(f_65, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.23/1.50  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.23/1.50  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.23/1.50  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.23/1.50  tff(c_34, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.23/1.50  tff(c_30, plain, (![A_12, B_13]: (r2_hidden('#skF_4'(A_12, B_13), A_12) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.23/1.50  tff(c_78, plain, (![C_35, B_36, A_37]: (r2_hidden(C_35, B_36) | ~r2_hidden(C_35, A_37) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.23/1.50  tff(c_86, plain, (![A_12, B_13, B_36]: (r2_hidden('#skF_4'(A_12, B_13), B_36) | ~r1_tarski(A_12, B_36) | r1_xboole_0(A_12, B_13))), inference(resolution, [status(thm)], [c_30, c_78])).
% 3.23/1.50  tff(c_28, plain, (![A_12, B_13]: (r2_hidden('#skF_4'(A_12, B_13), B_13) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.23/1.50  tff(c_61, plain, (![D_29, B_30, A_31]: (~r2_hidden(D_29, B_30) | ~r2_hidden(D_29, k4_xboole_0(A_31, B_30)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.23/1.50  tff(c_805, plain, (![A_145, A_146, B_147]: (~r2_hidden('#skF_4'(A_145, k4_xboole_0(A_146, B_147)), B_147) | r1_xboole_0(A_145, k4_xboole_0(A_146, B_147)))), inference(resolution, [status(thm)], [c_28, c_61])).
% 3.23/1.50  tff(c_839, plain, (![A_153, B_154, A_155]: (~r1_tarski(A_153, B_154) | r1_xboole_0(A_153, k4_xboole_0(A_155, B_154)))), inference(resolution, [status(thm)], [c_86, c_805])).
% 3.23/1.50  tff(c_32, plain, (~r1_xboole_0('#skF_5', k4_xboole_0('#skF_7', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.23/1.50  tff(c_844, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_839, c_32])).
% 3.23/1.50  tff(c_849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_844])).
% 3.23/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.50  
% 3.23/1.50  Inference rules
% 3.23/1.50  ----------------------
% 3.23/1.50  #Ref     : 0
% 3.23/1.50  #Sup     : 187
% 3.23/1.50  #Fact    : 0
% 3.23/1.50  #Define  : 0
% 3.23/1.50  #Split   : 0
% 3.23/1.50  #Chain   : 0
% 3.23/1.50  #Close   : 0
% 3.23/1.50  
% 3.23/1.50  Ordering : KBO
% 3.23/1.50  
% 3.23/1.50  Simplification rules
% 3.23/1.50  ----------------------
% 3.23/1.50  #Subsume      : 12
% 3.23/1.50  #Demod        : 26
% 3.23/1.50  #Tautology    : 32
% 3.23/1.50  #SimpNegUnit  : 0
% 3.23/1.50  #BackRed      : 0
% 3.23/1.50  
% 3.23/1.50  #Partial instantiations: 0
% 3.23/1.50  #Strategies tried      : 1
% 3.23/1.50  
% 3.23/1.50  Timing (in seconds)
% 3.23/1.50  ----------------------
% 3.23/1.50  Preprocessing        : 0.29
% 3.23/1.50  Parsing              : 0.15
% 3.23/1.50  CNF conversion       : 0.02
% 3.23/1.50  Main loop            : 0.46
% 3.23/1.50  Inferencing          : 0.18
% 3.23/1.50  Reduction            : 0.10
% 3.23/1.50  Demodulation         : 0.07
% 3.23/1.50  BG Simplification    : 0.03
% 3.23/1.50  Subsumption          : 0.11
% 3.23/1.50  Abstraction          : 0.02
% 3.23/1.50  MUC search           : 0.00
% 3.23/1.50  Cooper               : 0.00
% 3.23/1.50  Total                : 0.77
% 3.23/1.50  Index Insertion      : 0.00
% 3.23/1.50  Index Deletion       : 0.00
% 3.23/1.50  Index Matching       : 0.00
% 3.23/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
