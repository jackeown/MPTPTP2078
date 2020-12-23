%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:17 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   28 (  29 expanded)
%              Number of leaves         :   21 (  22 expanded)
%              Depth                    :    4
%              Number of atoms          :   19 (  22 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( r2_hidden(A,k2_relat_1(B))
            & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(c_46,plain,(
    ! [A_52,C_53] :
      ( r2_hidden(k4_tarski('#skF_8'(A_52,k2_relat_1(A_52),C_53),C_53),A_52)
      | ~ r2_hidden(C_53,k2_relat_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k1_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(C_16,D_19),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1402,plain,(
    ! [A_114,C_115] :
      ( r2_hidden('#skF_8'(A_114,k2_relat_1(A_114),C_115),k1_relat_1(A_114))
      | ~ r2_hidden(C_115,k2_relat_1(A_114)) ) ),
    inference(resolution,[status(thm)],[c_46,c_4])).

tff(c_26,plain,(
    ! [C_40] : ~ r2_hidden(C_40,k1_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1413,plain,(
    ! [C_115] : ~ r2_hidden(C_115,k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_1402,c_26])).

tff(c_28,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1413,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:23:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.61  
% 3.03/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.61  %$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5
% 3.03/1.61  
% 3.03/1.61  %Foreground sorts:
% 3.03/1.61  
% 3.03/1.61  
% 3.03/1.61  %Background operators:
% 3.03/1.61  
% 3.03/1.61  
% 3.03/1.61  %Foreground operators:
% 3.03/1.61  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.03/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.03/1.61  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.03/1.61  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.03/1.61  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.03/1.61  tff('#skF_10', type, '#skF_10': $i).
% 3.03/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.03/1.61  tff('#skF_9', type, '#skF_9': $i).
% 3.03/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.03/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.03/1.61  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.03/1.61  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.03/1.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.03/1.61  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.03/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.03/1.61  
% 3.03/1.62  tff(f_41, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 3.03/1.62  tff(f_33, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.03/1.62  tff(f_51, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 3.03/1.62  tff(c_46, plain, (![A_52, C_53]: (r2_hidden(k4_tarski('#skF_8'(A_52, k2_relat_1(A_52), C_53), C_53), A_52) | ~r2_hidden(C_53, k2_relat_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.03/1.62  tff(c_4, plain, (![C_16, A_1, D_19]: (r2_hidden(C_16, k1_relat_1(A_1)) | ~r2_hidden(k4_tarski(C_16, D_19), A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.03/1.62  tff(c_1402, plain, (![A_114, C_115]: (r2_hidden('#skF_8'(A_114, k2_relat_1(A_114), C_115), k1_relat_1(A_114)) | ~r2_hidden(C_115, k2_relat_1(A_114)))), inference(resolution, [status(thm)], [c_46, c_4])).
% 3.03/1.62  tff(c_26, plain, (![C_40]: (~r2_hidden(C_40, k1_relat_1('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.03/1.62  tff(c_1413, plain, (![C_115]: (~r2_hidden(C_115, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_1402, c_26])).
% 3.03/1.62  tff(c_28, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.03/1.62  tff(c_1419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1413, c_28])).
% 3.03/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.62  
% 3.03/1.62  Inference rules
% 3.03/1.62  ----------------------
% 3.03/1.62  #Ref     : 0
% 3.03/1.62  #Sup     : 252
% 3.03/1.62  #Fact    : 0
% 3.03/1.62  #Define  : 0
% 3.03/1.62  #Split   : 0
% 3.03/1.62  #Chain   : 0
% 3.03/1.62  #Close   : 0
% 3.03/1.62  
% 3.03/1.62  Ordering : KBO
% 3.03/1.62  
% 3.03/1.62  Simplification rules
% 3.03/1.62  ----------------------
% 3.03/1.62  #Subsume      : 135
% 3.03/1.62  #Demod        : 287
% 3.03/1.62  #Tautology    : 30
% 3.03/1.62  #SimpNegUnit  : 7
% 3.03/1.62  #BackRed      : 39
% 3.03/1.62  
% 3.03/1.62  #Partial instantiations: 0
% 3.03/1.62  #Strategies tried      : 1
% 3.03/1.62  
% 3.03/1.62  Timing (in seconds)
% 3.03/1.62  ----------------------
% 3.03/1.62  Preprocessing        : 0.33
% 3.03/1.62  Parsing              : 0.17
% 3.03/1.62  CNF conversion       : 0.03
% 3.03/1.62  Main loop            : 0.46
% 3.03/1.62  Inferencing          : 0.16
% 3.03/1.62  Reduction            : 0.14
% 3.03/1.62  Demodulation         : 0.09
% 3.03/1.62  BG Simplification    : 0.02
% 3.03/1.62  Subsumption          : 0.10
% 3.03/1.62  Abstraction          : 0.03
% 3.03/1.62  MUC search           : 0.00
% 3.03/1.62  Cooper               : 0.00
% 3.03/1.62  Total                : 0.82
% 3.03/1.62  Index Insertion      : 0.00
% 3.03/1.62  Index Deletion       : 0.00
% 3.03/1.62  Index Matching       : 0.00
% 3.03/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
