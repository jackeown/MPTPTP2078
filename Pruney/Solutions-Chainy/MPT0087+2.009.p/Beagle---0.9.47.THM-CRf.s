%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:18 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  45 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42,plain,(
    ! [D_19,A_20,B_21] :
      ( r2_hidden(D_19,A_20)
      | ~ r2_hidden(D_19,k4_xboole_0(A_20,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_472,plain,(
    ! [A_90,A_91,B_92] :
      ( r2_hidden('#skF_3'(A_90,k4_xboole_0(A_91,B_92)),A_91)
      | r1_xboole_0(A_90,k4_xboole_0(A_91,B_92)) ) ),
    inference(resolution,[status(thm)],[c_22,c_42])).

tff(c_28,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_53,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ r1_xboole_0(A_22,B_23)
      | ~ r2_hidden(C_24,B_23)
      | ~ r2_hidden(C_24,A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_56,plain,(
    ! [C_24] :
      ( ~ r2_hidden(C_24,'#skF_5')
      | ~ r2_hidden(C_24,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_53])).

tff(c_685,plain,(
    ! [A_119,B_120] :
      ( ~ r2_hidden('#skF_3'(A_119,k4_xboole_0('#skF_5',B_120)),'#skF_4')
      | r1_xboole_0(A_119,k4_xboole_0('#skF_5',B_120)) ) ),
    inference(resolution,[status(thm)],[c_472,c_56])).

tff(c_695,plain,(
    ! [B_120] : r1_xboole_0('#skF_4',k4_xboole_0('#skF_5',B_120)) ),
    inference(resolution,[status(thm)],[c_24,c_685])).

tff(c_26,plain,(
    ~ r1_xboole_0('#skF_4',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_698,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:16:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.85  
% 3.45/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.85  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.45/1.85  
% 3.45/1.85  %Foreground sorts:
% 3.45/1.85  
% 3.45/1.85  
% 3.45/1.85  %Background operators:
% 3.45/1.85  
% 3.45/1.85  
% 3.45/1.85  %Foreground operators:
% 3.45/1.85  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.45/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.45/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.45/1.85  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.45/1.85  tff('#skF_5', type, '#skF_5': $i).
% 3.45/1.85  tff('#skF_6', type, '#skF_6': $i).
% 3.45/1.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.45/1.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.45/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.85  tff('#skF_4', type, '#skF_4': $i).
% 3.45/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.85  
% 3.45/1.87  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.45/1.87  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.45/1.87  tff(f_58, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_xboole_1)).
% 3.45/1.87  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.45/1.87  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.45/1.87  tff(c_42, plain, (![D_19, A_20, B_21]: (r2_hidden(D_19, A_20) | ~r2_hidden(D_19, k4_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.45/1.87  tff(c_472, plain, (![A_90, A_91, B_92]: (r2_hidden('#skF_3'(A_90, k4_xboole_0(A_91, B_92)), A_91) | r1_xboole_0(A_90, k4_xboole_0(A_91, B_92)))), inference(resolution, [status(thm)], [c_22, c_42])).
% 3.45/1.87  tff(c_28, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.45/1.87  tff(c_53, plain, (![A_22, B_23, C_24]: (~r1_xboole_0(A_22, B_23) | ~r2_hidden(C_24, B_23) | ~r2_hidden(C_24, A_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.45/1.87  tff(c_56, plain, (![C_24]: (~r2_hidden(C_24, '#skF_5') | ~r2_hidden(C_24, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_53])).
% 3.45/1.87  tff(c_685, plain, (![A_119, B_120]: (~r2_hidden('#skF_3'(A_119, k4_xboole_0('#skF_5', B_120)), '#skF_4') | r1_xboole_0(A_119, k4_xboole_0('#skF_5', B_120)))), inference(resolution, [status(thm)], [c_472, c_56])).
% 3.45/1.87  tff(c_695, plain, (![B_120]: (r1_xboole_0('#skF_4', k4_xboole_0('#skF_5', B_120)))), inference(resolution, [status(thm)], [c_24, c_685])).
% 3.45/1.87  tff(c_26, plain, (~r1_xboole_0('#skF_4', k4_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.45/1.87  tff(c_698, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_695, c_26])).
% 3.45/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.87  
% 3.45/1.87  Inference rules
% 3.45/1.87  ----------------------
% 3.45/1.87  #Ref     : 0
% 3.45/1.87  #Sup     : 143
% 3.45/1.87  #Fact    : 0
% 3.45/1.87  #Define  : 0
% 3.45/1.87  #Split   : 0
% 3.45/1.87  #Chain   : 0
% 3.45/1.87  #Close   : 0
% 3.45/1.87  
% 3.45/1.87  Ordering : KBO
% 3.45/1.87  
% 3.45/1.87  Simplification rules
% 3.45/1.87  ----------------------
% 3.45/1.87  #Subsume      : 14
% 3.45/1.87  #Demod        : 11
% 3.45/1.87  #Tautology    : 15
% 3.45/1.87  #SimpNegUnit  : 0
% 3.45/1.87  #BackRed      : 1
% 3.45/1.87  
% 3.45/1.87  #Partial instantiations: 0
% 3.45/1.87  #Strategies tried      : 1
% 3.45/1.87  
% 3.45/1.87  Timing (in seconds)
% 3.45/1.87  ----------------------
% 3.45/1.87  Preprocessing        : 0.43
% 3.45/1.87  Parsing              : 0.23
% 3.45/1.87  CNF conversion       : 0.03
% 3.45/1.87  Main loop            : 0.57
% 3.45/1.87  Inferencing          : 0.23
% 3.45/1.87  Reduction            : 0.13
% 3.45/1.87  Demodulation         : 0.09
% 3.45/1.87  BG Simplification    : 0.03
% 3.45/1.87  Subsumption          : 0.14
% 3.45/1.87  Abstraction          : 0.03
% 3.45/1.87  MUC search           : 0.00
% 3.45/1.87  Cooper               : 0.00
% 3.45/1.87  Total                : 1.05
% 3.45/1.87  Index Insertion      : 0.00
% 3.45/1.87  Index Deletion       : 0.00
% 3.45/1.87  Index Matching       : 0.00
% 3.45/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
