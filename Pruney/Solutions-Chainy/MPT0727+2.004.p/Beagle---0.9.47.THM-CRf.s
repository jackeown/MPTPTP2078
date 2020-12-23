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
% DateTime   : Thu Dec  3 10:05:55 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   22 (  34 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  55 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_45,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_hidden(A,B)
          & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & r2_hidden(B,C)
        & r2_hidden(C,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_ordinal1)).

tff(c_10,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    ! [C_19,B_20,A_21] :
      ( r2_hidden(C_19,B_20)
      | ~ r2_hidden(C_19,A_21)
      | ~ r1_tarski(A_21,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [B_20] :
      ( r2_hidden('#skF_2',B_20)
      | ~ r1_tarski('#skF_3',B_20) ) ),
    inference(resolution,[status(thm)],[c_12,c_34])).

tff(c_41,plain,(
    ! [B_22] :
      ( r2_hidden('#skF_2',B_22)
      | ~ r1_tarski('#skF_3',B_22) ) ),
    inference(resolution,[status(thm)],[c_12,c_34])).

tff(c_8,plain,(
    ! [C_8,A_6,B_7] :
      ( ~ r2_hidden(C_8,A_6)
      | ~ r2_hidden(B_7,C_8)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_54,plain,(
    ! [B_23,B_24] :
      ( ~ r2_hidden(B_23,'#skF_2')
      | ~ r2_hidden(B_24,B_23)
      | ~ r1_tarski('#skF_3',B_24) ) ),
    inference(resolution,[status(thm)],[c_41,c_8])).

tff(c_57,plain,(
    ! [B_24] :
      ( ~ r2_hidden(B_24,'#skF_2')
      | ~ r1_tarski('#skF_3',B_24)
      | ~ r1_tarski('#skF_3','#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_54])).

tff(c_65,plain,(
    ! [B_25] :
      ( ~ r2_hidden(B_25,'#skF_2')
      | ~ r1_tarski('#skF_3',B_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_57])).

tff(c_69,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_65])).

tff(c_77,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:52:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.17  
% 1.55/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.17  %$ r2_hidden > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.55/1.17  
% 1.55/1.17  %Foreground sorts:
% 1.55/1.17  
% 1.55/1.17  
% 1.55/1.17  %Background operators:
% 1.55/1.17  
% 1.55/1.17  
% 1.55/1.17  %Foreground operators:
% 1.55/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.55/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.55/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.55/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.55/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.55/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.55/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.55/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.55/1.17  
% 1.55/1.18  tff(f_45, negated_conjecture, ~(![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.55/1.18  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.55/1.18  tff(f_39, axiom, (![A, B, C]: ~((r2_hidden(A, B) & r2_hidden(B, C)) & r2_hidden(C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_ordinal1)).
% 1.55/1.18  tff(c_10, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.55/1.18  tff(c_12, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.55/1.18  tff(c_34, plain, (![C_19, B_20, A_21]: (r2_hidden(C_19, B_20) | ~r2_hidden(C_19, A_21) | ~r1_tarski(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.55/1.18  tff(c_40, plain, (![B_20]: (r2_hidden('#skF_2', B_20) | ~r1_tarski('#skF_3', B_20))), inference(resolution, [status(thm)], [c_12, c_34])).
% 1.55/1.18  tff(c_41, plain, (![B_22]: (r2_hidden('#skF_2', B_22) | ~r1_tarski('#skF_3', B_22))), inference(resolution, [status(thm)], [c_12, c_34])).
% 1.55/1.18  tff(c_8, plain, (![C_8, A_6, B_7]: (~r2_hidden(C_8, A_6) | ~r2_hidden(B_7, C_8) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.55/1.18  tff(c_54, plain, (![B_23, B_24]: (~r2_hidden(B_23, '#skF_2') | ~r2_hidden(B_24, B_23) | ~r1_tarski('#skF_3', B_24))), inference(resolution, [status(thm)], [c_41, c_8])).
% 1.55/1.18  tff(c_57, plain, (![B_24]: (~r2_hidden(B_24, '#skF_2') | ~r1_tarski('#skF_3', B_24) | ~r1_tarski('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_54])).
% 1.55/1.18  tff(c_65, plain, (![B_25]: (~r2_hidden(B_25, '#skF_2') | ~r1_tarski('#skF_3', B_25))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_57])).
% 1.55/1.18  tff(c_69, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_65])).
% 1.55/1.18  tff(c_77, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_69])).
% 1.55/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.18  
% 1.55/1.18  Inference rules
% 1.55/1.18  ----------------------
% 1.55/1.18  #Ref     : 0
% 1.55/1.18  #Sup     : 13
% 1.55/1.18  #Fact    : 0
% 1.55/1.18  #Define  : 0
% 1.55/1.18  #Split   : 0
% 1.55/1.18  #Chain   : 0
% 1.55/1.18  #Close   : 0
% 1.55/1.18  
% 1.55/1.18  Ordering : KBO
% 1.55/1.18  
% 1.55/1.18  Simplification rules
% 1.55/1.18  ----------------------
% 1.55/1.18  #Subsume      : 0
% 1.55/1.18  #Demod        : 3
% 1.55/1.18  #Tautology    : 0
% 1.55/1.18  #SimpNegUnit  : 0
% 1.55/1.18  #BackRed      : 0
% 1.55/1.18  
% 1.55/1.18  #Partial instantiations: 0
% 1.55/1.18  #Strategies tried      : 1
% 1.55/1.18  
% 1.55/1.18  Timing (in seconds)
% 1.55/1.18  ----------------------
% 1.55/1.18  Preprocessing        : 0.27
% 1.55/1.18  Parsing              : 0.14
% 1.55/1.18  CNF conversion       : 0.02
% 1.55/1.18  Main loop            : 0.11
% 1.55/1.18  Inferencing          : 0.05
% 1.55/1.18  Reduction            : 0.02
% 1.55/1.18  Demodulation         : 0.02
% 1.55/1.18  BG Simplification    : 0.01
% 1.55/1.18  Subsumption          : 0.02
% 1.55/1.18  Abstraction          : 0.01
% 1.55/1.18  MUC search           : 0.00
% 1.55/1.18  Cooper               : 0.00
% 1.55/1.18  Total                : 0.41
% 1.55/1.18  Index Insertion      : 0.00
% 1.55/1.18  Index Deletion       : 0.00
% 1.55/1.18  Index Matching       : 0.00
% 1.55/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
