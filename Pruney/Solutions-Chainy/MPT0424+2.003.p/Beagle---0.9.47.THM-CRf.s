%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:53 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   30 (  36 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  50 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k3_tarski > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(k3_tarski(A),B)
          & r2_hidden(C,A) )
       => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    r1_tarski(k3_tarski('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_58,plain,(
    ! [C_36,A_37,D_38] :
      ( r2_hidden(C_36,k3_tarski(A_37))
      | ~ r2_hidden(D_38,A_37)
      | ~ r2_hidden(C_36,D_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,(
    ! [C_39] :
      ( r2_hidden(C_39,k3_tarski('#skF_6'))
      | ~ r2_hidden(C_39,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_28,c_58])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_92,plain,(
    ! [C_42,B_43] :
      ( r2_hidden(C_42,B_43)
      | ~ r1_tarski(k3_tarski('#skF_6'),B_43)
      | ~ r2_hidden(C_42,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_68,c_2])).

tff(c_107,plain,(
    ! [C_46] :
      ( r2_hidden(C_46,'#skF_7')
      | ~ r2_hidden(C_46,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_30,c_92])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_119,plain,(
    ! [A_47] :
      ( r1_tarski(A_47,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_47,'#skF_7'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_107,c_4])).

tff(c_123,plain,(
    r1_tarski('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_119])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:08:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.17  
% 1.81/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.18  %$ r2_hidden > r1_tarski > #nlpp > k3_tarski > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 1.81/1.18  
% 1.81/1.18  %Foreground sorts:
% 1.81/1.18  
% 1.81/1.18  
% 1.81/1.18  %Background operators:
% 1.81/1.18  
% 1.81/1.18  
% 1.81/1.18  %Foreground operators:
% 1.81/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.18  tff('#skF_7', type, '#skF_7': $i).
% 1.81/1.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.81/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.18  tff('#skF_6', type, '#skF_6': $i).
% 1.81/1.18  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.81/1.18  tff('#skF_8', type, '#skF_8': $i).
% 1.81/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.81/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.81/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.81/1.18  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.81/1.18  
% 1.81/1.18  tff(f_49, negated_conjecture, ~(![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_setfam_1)).
% 1.81/1.18  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.81/1.18  tff(f_42, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 1.81/1.18  tff(c_26, plain, (~r1_tarski('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.81/1.18  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.18  tff(c_30, plain, (r1_tarski(k3_tarski('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.81/1.18  tff(c_28, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.81/1.18  tff(c_58, plain, (![C_36, A_37, D_38]: (r2_hidden(C_36, k3_tarski(A_37)) | ~r2_hidden(D_38, A_37) | ~r2_hidden(C_36, D_38))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.81/1.18  tff(c_68, plain, (![C_39]: (r2_hidden(C_39, k3_tarski('#skF_6')) | ~r2_hidden(C_39, '#skF_8'))), inference(resolution, [status(thm)], [c_28, c_58])).
% 1.81/1.18  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.18  tff(c_92, plain, (![C_42, B_43]: (r2_hidden(C_42, B_43) | ~r1_tarski(k3_tarski('#skF_6'), B_43) | ~r2_hidden(C_42, '#skF_8'))), inference(resolution, [status(thm)], [c_68, c_2])).
% 1.81/1.18  tff(c_107, plain, (![C_46]: (r2_hidden(C_46, '#skF_7') | ~r2_hidden(C_46, '#skF_8'))), inference(resolution, [status(thm)], [c_30, c_92])).
% 1.81/1.18  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.18  tff(c_119, plain, (![A_47]: (r1_tarski(A_47, '#skF_7') | ~r2_hidden('#skF_1'(A_47, '#skF_7'), '#skF_8'))), inference(resolution, [status(thm)], [c_107, c_4])).
% 1.81/1.18  tff(c_123, plain, (r1_tarski('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_6, c_119])).
% 1.81/1.18  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_123])).
% 1.81/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.18  
% 1.81/1.18  Inference rules
% 1.81/1.18  ----------------------
% 1.81/1.18  #Ref     : 0
% 1.81/1.18  #Sup     : 23
% 1.81/1.18  #Fact    : 0
% 1.81/1.18  #Define  : 0
% 1.81/1.18  #Split   : 1
% 1.81/1.18  #Chain   : 0
% 1.81/1.18  #Close   : 0
% 1.81/1.18  
% 1.81/1.18  Ordering : KBO
% 1.81/1.18  
% 1.81/1.18  Simplification rules
% 1.81/1.18  ----------------------
% 1.81/1.18  #Subsume      : 2
% 1.81/1.18  #Demod        : 0
% 1.81/1.18  #Tautology    : 0
% 1.81/1.18  #SimpNegUnit  : 1
% 1.81/1.18  #BackRed      : 0
% 1.81/1.18  
% 1.81/1.18  #Partial instantiations: 0
% 1.81/1.18  #Strategies tried      : 1
% 1.81/1.18  
% 1.81/1.18  Timing (in seconds)
% 1.81/1.18  ----------------------
% 1.81/1.19  Preprocessing        : 0.27
% 1.81/1.19  Parsing              : 0.14
% 1.81/1.19  CNF conversion       : 0.02
% 1.81/1.19  Main loop            : 0.15
% 1.81/1.19  Inferencing          : 0.06
% 1.81/1.19  Reduction            : 0.04
% 1.81/1.19  Demodulation         : 0.02
% 1.81/1.19  BG Simplification    : 0.01
% 1.81/1.19  Subsumption          : 0.04
% 1.81/1.19  Abstraction          : 0.01
% 1.81/1.19  MUC search           : 0.00
% 1.81/1.19  Cooper               : 0.00
% 1.81/1.19  Total                : 0.44
% 1.81/1.19  Index Insertion      : 0.00
% 1.81/1.19  Index Deletion       : 0.00
% 1.81/1.19  Index Matching       : 0.00
% 1.81/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
