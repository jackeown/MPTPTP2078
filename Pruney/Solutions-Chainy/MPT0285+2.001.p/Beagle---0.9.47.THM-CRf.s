%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:30 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   25 (  29 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  32 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k3_tarski > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

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

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

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
    ~ r1_tarski('#skF_6',k3_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_52,plain,(
    ! [C_36,A_37,D_38] :
      ( r2_hidden(C_36,k3_tarski(A_37))
      | ~ r2_hidden(D_38,A_37)
      | ~ r2_hidden(C_36,D_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_62,plain,(
    ! [C_39] :
      ( r2_hidden(C_39,k3_tarski('#skF_7'))
      | ~ r2_hidden(C_39,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_28,c_52])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_91,plain,(
    ! [A_44] :
      ( r1_tarski(A_44,k3_tarski('#skF_7'))
      | ~ r2_hidden('#skF_1'(A_44,k3_tarski('#skF_7')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_62,c_4])).

tff(c_95,plain,(
    r1_tarski('#skF_6',k3_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_6,c_91])).

tff(c_99,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_95])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:35:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.12  
% 1.68/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.12  %$ r2_hidden > r1_tarski > #nlpp > k3_tarski > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 1.68/1.12  
% 1.68/1.12  %Foreground sorts:
% 1.68/1.12  
% 1.68/1.12  
% 1.68/1.12  %Background operators:
% 1.68/1.12  
% 1.68/1.12  
% 1.68/1.12  %Foreground operators:
% 1.68/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.12  tff('#skF_7', type, '#skF_7': $i).
% 1.68/1.12  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.68/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.12  tff('#skF_6', type, '#skF_6': $i).
% 1.68/1.12  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.68/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.12  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.68/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.68/1.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.68/1.12  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.68/1.12  
% 1.79/1.13  tff(f_47, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_zfmisc_1)).
% 1.79/1.13  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.79/1.13  tff(f_42, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 1.79/1.13  tff(c_26, plain, (~r1_tarski('#skF_6', k3_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.79/1.13  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.79/1.13  tff(c_28, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.79/1.13  tff(c_52, plain, (![C_36, A_37, D_38]: (r2_hidden(C_36, k3_tarski(A_37)) | ~r2_hidden(D_38, A_37) | ~r2_hidden(C_36, D_38))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.79/1.13  tff(c_62, plain, (![C_39]: (r2_hidden(C_39, k3_tarski('#skF_7')) | ~r2_hidden(C_39, '#skF_6'))), inference(resolution, [status(thm)], [c_28, c_52])).
% 1.79/1.13  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.79/1.13  tff(c_91, plain, (![A_44]: (r1_tarski(A_44, k3_tarski('#skF_7')) | ~r2_hidden('#skF_1'(A_44, k3_tarski('#skF_7')), '#skF_6'))), inference(resolution, [status(thm)], [c_62, c_4])).
% 1.79/1.13  tff(c_95, plain, (r1_tarski('#skF_6', k3_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_6, c_91])).
% 1.79/1.13  tff(c_99, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_95])).
% 1.79/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.13  
% 1.79/1.13  Inference rules
% 1.79/1.13  ----------------------
% 1.79/1.13  #Ref     : 0
% 1.79/1.13  #Sup     : 16
% 1.79/1.13  #Fact    : 0
% 1.79/1.13  #Define  : 0
% 1.79/1.13  #Split   : 0
% 1.79/1.13  #Chain   : 0
% 1.79/1.13  #Close   : 0
% 1.79/1.13  
% 1.79/1.13  Ordering : KBO
% 1.79/1.13  
% 1.79/1.13  Simplification rules
% 1.79/1.13  ----------------------
% 1.79/1.13  #Subsume      : 2
% 1.79/1.13  #Demod        : 0
% 1.79/1.13  #Tautology    : 0
% 1.79/1.13  #SimpNegUnit  : 1
% 1.79/1.13  #BackRed      : 0
% 1.79/1.13  
% 1.79/1.13  #Partial instantiations: 0
% 1.79/1.13  #Strategies tried      : 1
% 1.79/1.13  
% 1.79/1.13  Timing (in seconds)
% 1.79/1.13  ----------------------
% 1.79/1.13  Preprocessing        : 0.26
% 1.79/1.13  Parsing              : 0.14
% 1.79/1.13  CNF conversion       : 0.02
% 1.79/1.13  Main loop            : 0.12
% 1.79/1.13  Inferencing          : 0.05
% 1.79/1.13  Reduction            : 0.03
% 1.79/1.13  Demodulation         : 0.02
% 1.79/1.13  BG Simplification    : 0.01
% 1.79/1.13  Subsumption          : 0.03
% 1.79/1.13  Abstraction          : 0.01
% 1.79/1.13  MUC search           : 0.00
% 1.79/1.13  Cooper               : 0.00
% 1.79/1.13  Total                : 0.40
% 1.79/1.13  Index Insertion      : 0.00
% 1.79/1.13  Index Deletion       : 0.00
% 1.79/1.13  Index Matching       : 0.00
% 1.79/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
