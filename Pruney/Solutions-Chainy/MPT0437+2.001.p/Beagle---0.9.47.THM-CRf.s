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
% DateTime   : Thu Dec  3 09:58:17 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   32 (  37 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    3
%              Number of atoms          :   23 (  38 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_4 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(k4_tarski(A,B),C)
         => ( r2_hidden(A,k1_relat_1(C))
            & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_26,plain,
    ( ~ r2_hidden('#skF_10',k2_relat_1('#skF_11'))
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_31,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_28,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_37,plain,(
    ! [C_42,A_43,D_44] :
      ( r2_hidden(C_42,k1_relat_1(A_43))
      | ~ r2_hidden(k4_tarski(C_42,D_44),A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_28,c_37])).

tff(c_44,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_40])).

tff(c_45,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_53,plain,(
    ! [C_48,A_49,D_50] :
      ( r2_hidden(C_48,k2_relat_1(A_49))
      | ~ r2_hidden(k4_tarski(D_50,C_48),A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_56,plain,(
    r2_hidden('#skF_10',k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_28,c_53])).

tff(c_60,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:55:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.12  
% 1.64/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.13  %$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_4 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5
% 1.64/1.13  
% 1.64/1.13  %Foreground sorts:
% 1.64/1.13  
% 1.64/1.13  
% 1.64/1.13  %Background operators:
% 1.64/1.13  
% 1.64/1.13  
% 1.64/1.13  %Foreground operators:
% 1.64/1.13  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.13  tff('#skF_11', type, '#skF_11': $i).
% 1.64/1.13  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.64/1.13  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.64/1.13  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.64/1.13  tff('#skF_10', type, '#skF_10': $i).
% 1.64/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.64/1.13  tff('#skF_9', type, '#skF_9': $i).
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.64/1.13  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 1.64/1.13  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 1.64/1.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.64/1.13  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.64/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.64/1.13  
% 1.64/1.13  tff(f_50, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 1.64/1.13  tff(f_33, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 1.64/1.13  tff(f_41, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 1.64/1.13  tff(c_26, plain, (~r2_hidden('#skF_10', k2_relat_1('#skF_11')) | ~r2_hidden('#skF_9', k1_relat_1('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.64/1.13  tff(c_31, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_11'))), inference(splitLeft, [status(thm)], [c_26])).
% 1.64/1.13  tff(c_28, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_11')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.64/1.13  tff(c_37, plain, (![C_42, A_43, D_44]: (r2_hidden(C_42, k1_relat_1(A_43)) | ~r2_hidden(k4_tarski(C_42, D_44), A_43))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.64/1.13  tff(c_40, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_28, c_37])).
% 1.64/1.13  tff(c_44, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31, c_40])).
% 1.64/1.13  tff(c_45, plain, (~r2_hidden('#skF_10', k2_relat_1('#skF_11'))), inference(splitRight, [status(thm)], [c_26])).
% 1.64/1.13  tff(c_53, plain, (![C_48, A_49, D_50]: (r2_hidden(C_48, k2_relat_1(A_49)) | ~r2_hidden(k4_tarski(D_50, C_48), A_49))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.64/1.13  tff(c_56, plain, (r2_hidden('#skF_10', k2_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_28, c_53])).
% 1.64/1.13  tff(c_60, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_56])).
% 1.64/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.14  
% 1.64/1.14  Inference rules
% 1.64/1.14  ----------------------
% 1.64/1.14  #Ref     : 0
% 1.64/1.14  #Sup     : 4
% 1.64/1.14  #Fact    : 0
% 1.64/1.14  #Define  : 0
% 1.64/1.14  #Split   : 1
% 1.64/1.14  #Chain   : 0
% 1.64/1.14  #Close   : 0
% 1.64/1.14  
% 1.64/1.14  Ordering : KBO
% 1.64/1.14  
% 1.64/1.14  Simplification rules
% 1.64/1.14  ----------------------
% 1.64/1.14  #Subsume      : 0
% 1.64/1.14  #Demod        : 1
% 1.64/1.14  #Tautology    : 1
% 1.64/1.14  #SimpNegUnit  : 2
% 1.64/1.14  #BackRed      : 0
% 1.64/1.14  
% 1.64/1.14  #Partial instantiations: 0
% 1.64/1.14  #Strategies tried      : 1
% 1.64/1.14  
% 1.64/1.14  Timing (in seconds)
% 1.64/1.14  ----------------------
% 1.64/1.14  Preprocessing        : 0.28
% 1.64/1.14  Parsing              : 0.14
% 1.64/1.14  CNF conversion       : 0.02
% 1.64/1.14  Main loop            : 0.09
% 1.64/1.14  Inferencing          : 0.03
% 1.64/1.14  Reduction            : 0.03
% 1.64/1.14  Demodulation         : 0.01
% 1.64/1.14  BG Simplification    : 0.01
% 1.64/1.14  Subsumption          : 0.02
% 1.64/1.14  Abstraction          : 0.00
% 1.64/1.14  MUC search           : 0.00
% 1.64/1.14  Cooper               : 0.00
% 1.64/1.14  Total                : 0.40
% 1.64/1.14  Index Insertion      : 0.00
% 1.64/1.14  Index Deletion       : 0.00
% 1.64/1.14  Index Matching       : 0.00
% 1.69/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
