%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:21 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   27 (  31 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  54 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > #nlpp > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_50,axiom,(
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

tff(c_18,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_66,plain,(
    ! [C_27,B_28,A_29] :
      ( r2_hidden(C_27,B_28)
      | ~ r2_hidden(C_27,A_29)
      | ~ r1_tarski(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_96,plain,(
    ! [A_33,B_34,B_35] :
      ( r2_hidden('#skF_2'(A_33,B_34),B_35)
      | ~ r1_tarski(A_33,B_35)
      | r1_xboole_0(A_33,B_34) ) ),
    inference(resolution,[status(thm)],[c_12,c_66])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_29,plain,(
    ! [A_20,B_21,C_22] :
      ( ~ r1_xboole_0(A_20,B_21)
      | ~ r2_hidden(C_22,B_21)
      | ~ r2_hidden(C_22,A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_33,plain,(
    ! [C_23] :
      ( ~ r2_hidden(C_23,'#skF_5')
      | ~ r2_hidden(C_23,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_29])).

tff(c_47,plain,(
    ! [A_6] :
      ( ~ r2_hidden('#skF_2'(A_6,'#skF_5'),'#skF_4')
      | r1_xboole_0(A_6,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10,c_33])).

tff(c_126,plain,(
    ! [A_38] :
      ( ~ r1_tarski(A_38,'#skF_4')
      | r1_xboole_0(A_38,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_96,c_47])).

tff(c_14,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_131,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_126,c_14])).

tff(c_136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:42:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.21  
% 1.72/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.21  %$ r2_hidden > r1_xboole_0 > r1_tarski > #nlpp > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.72/1.21  
% 1.72/1.21  %Foreground sorts:
% 1.72/1.21  
% 1.72/1.21  
% 1.72/1.21  %Background operators:
% 1.72/1.21  
% 1.72/1.21  
% 1.72/1.21  %Foreground operators:
% 1.72/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.72/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.72/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.72/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.72/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.72/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.72/1.21  
% 1.72/1.22  tff(f_57, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.72/1.22  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.72/1.22  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.72/1.22  tff(c_18, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.72/1.22  tff(c_12, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.72/1.22  tff(c_66, plain, (![C_27, B_28, A_29]: (r2_hidden(C_27, B_28) | ~r2_hidden(C_27, A_29) | ~r1_tarski(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.72/1.22  tff(c_96, plain, (![A_33, B_34, B_35]: (r2_hidden('#skF_2'(A_33, B_34), B_35) | ~r1_tarski(A_33, B_35) | r1_xboole_0(A_33, B_34))), inference(resolution, [status(thm)], [c_12, c_66])).
% 1.72/1.22  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.72/1.22  tff(c_16, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.72/1.22  tff(c_29, plain, (![A_20, B_21, C_22]: (~r1_xboole_0(A_20, B_21) | ~r2_hidden(C_22, B_21) | ~r2_hidden(C_22, A_20))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.72/1.22  tff(c_33, plain, (![C_23]: (~r2_hidden(C_23, '#skF_5') | ~r2_hidden(C_23, '#skF_4'))), inference(resolution, [status(thm)], [c_16, c_29])).
% 1.72/1.22  tff(c_47, plain, (![A_6]: (~r2_hidden('#skF_2'(A_6, '#skF_5'), '#skF_4') | r1_xboole_0(A_6, '#skF_5'))), inference(resolution, [status(thm)], [c_10, c_33])).
% 1.72/1.22  tff(c_126, plain, (![A_38]: (~r1_tarski(A_38, '#skF_4') | r1_xboole_0(A_38, '#skF_5'))), inference(resolution, [status(thm)], [c_96, c_47])).
% 1.72/1.22  tff(c_14, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.72/1.22  tff(c_131, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_126, c_14])).
% 1.72/1.22  tff(c_136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_131])).
% 1.72/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.22  
% 1.72/1.22  Inference rules
% 1.72/1.22  ----------------------
% 1.72/1.22  #Ref     : 0
% 1.72/1.22  #Sup     : 23
% 1.72/1.22  #Fact    : 0
% 1.72/1.22  #Define  : 0
% 1.72/1.22  #Split   : 1
% 1.72/1.22  #Chain   : 0
% 1.72/1.22  #Close   : 0
% 1.72/1.22  
% 1.72/1.22  Ordering : KBO
% 1.72/1.22  
% 1.72/1.22  Simplification rules
% 1.72/1.22  ----------------------
% 1.72/1.22  #Subsume      : 2
% 1.72/1.22  #Demod        : 2
% 1.72/1.22  #Tautology    : 2
% 1.72/1.22  #SimpNegUnit  : 0
% 1.72/1.22  #BackRed      : 0
% 1.72/1.22  
% 1.72/1.22  #Partial instantiations: 0
% 1.72/1.22  #Strategies tried      : 1
% 1.72/1.22  
% 1.72/1.22  Timing (in seconds)
% 1.72/1.22  ----------------------
% 1.72/1.22  Preprocessing        : 0.27
% 1.72/1.22  Parsing              : 0.15
% 1.72/1.22  CNF conversion       : 0.02
% 1.72/1.23  Main loop            : 0.15
% 1.72/1.23  Inferencing          : 0.06
% 1.72/1.23  Reduction            : 0.03
% 1.72/1.23  Demodulation         : 0.02
% 1.72/1.23  BG Simplification    : 0.01
% 1.72/1.23  Subsumption          : 0.04
% 1.72/1.23  Abstraction          : 0.01
% 1.72/1.23  MUC search           : 0.00
% 1.72/1.23  Cooper               : 0.00
% 1.72/1.23  Total                : 0.44
% 1.72/1.23  Index Insertion      : 0.00
% 1.72/1.23  Index Deletion       : 0.00
% 1.72/1.23  Index Matching       : 0.00
% 1.72/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
