%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:17 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
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

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( r2_hidden(A,k1_relat_1(B))
            & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

tff(c_172,plain,(
    ! [C_61,A_62] :
      ( r2_hidden(k4_tarski(C_61,'#skF_4'(A_62,k1_relat_1(A_62),C_61)),A_62)
      | ~ r2_hidden(C_61,k1_relat_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [C_35,A_20,D_38] :
      ( r2_hidden(C_35,k2_relat_1(A_20))
      | ~ r2_hidden(k4_tarski(D_38,C_35),A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1382,plain,(
    ! [A_112,C_113] :
      ( r2_hidden('#skF_4'(A_112,k1_relat_1(A_112),C_113),k2_relat_1(A_112))
      | ~ r2_hidden(C_113,k1_relat_1(A_112)) ) ),
    inference(resolution,[status(thm)],[c_172,c_16])).

tff(c_26,plain,(
    ! [C_40] : ~ r2_hidden(C_40,k2_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1393,plain,(
    ! [C_113] : ~ r2_hidden(C_113,k1_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_1382,c_26])).

tff(c_28,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1393,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:44:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.52  
% 3.15/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.52  %$ r2_hidden > v1_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_4 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5
% 3.15/1.52  
% 3.15/1.52  %Foreground sorts:
% 3.15/1.52  
% 3.15/1.52  
% 3.15/1.52  %Background operators:
% 3.15/1.52  
% 3.15/1.52  
% 3.15/1.52  %Foreground operators:
% 3.15/1.52  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.15/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.15/1.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.15/1.52  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.15/1.52  tff('#skF_10', type, '#skF_10': $i).
% 3.15/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.15/1.52  tff('#skF_9', type, '#skF_9': $i).
% 3.15/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.15/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.15/1.52  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.15/1.52  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.15/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.15/1.52  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.15/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.15/1.52  
% 3.15/1.53  tff(f_33, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.15/1.53  tff(f_41, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 3.15/1.53  tff(f_51, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_relat_1)).
% 3.15/1.53  tff(c_172, plain, (![C_61, A_62]: (r2_hidden(k4_tarski(C_61, '#skF_4'(A_62, k1_relat_1(A_62), C_61)), A_62) | ~r2_hidden(C_61, k1_relat_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.15/1.53  tff(c_16, plain, (![C_35, A_20, D_38]: (r2_hidden(C_35, k2_relat_1(A_20)) | ~r2_hidden(k4_tarski(D_38, C_35), A_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.15/1.53  tff(c_1382, plain, (![A_112, C_113]: (r2_hidden('#skF_4'(A_112, k1_relat_1(A_112), C_113), k2_relat_1(A_112)) | ~r2_hidden(C_113, k1_relat_1(A_112)))), inference(resolution, [status(thm)], [c_172, c_16])).
% 3.15/1.53  tff(c_26, plain, (![C_40]: (~r2_hidden(C_40, k2_relat_1('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.15/1.53  tff(c_1393, plain, (![C_113]: (~r2_hidden(C_113, k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_1382, c_26])).
% 3.15/1.53  tff(c_28, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.15/1.53  tff(c_1399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1393, c_28])).
% 3.15/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.53  
% 3.15/1.53  Inference rules
% 3.15/1.53  ----------------------
% 3.15/1.53  #Ref     : 0
% 3.15/1.53  #Sup     : 250
% 3.15/1.53  #Fact    : 0
% 3.15/1.53  #Define  : 0
% 3.15/1.53  #Split   : 0
% 3.15/1.53  #Chain   : 0
% 3.15/1.53  #Close   : 0
% 3.15/1.53  
% 3.15/1.53  Ordering : KBO
% 3.15/1.53  
% 3.15/1.53  Simplification rules
% 3.15/1.53  ----------------------
% 3.15/1.53  #Subsume      : 128
% 3.15/1.53  #Demod        : 238
% 3.15/1.53  #Tautology    : 26
% 3.15/1.53  #SimpNegUnit  : 5
% 3.15/1.53  #BackRed      : 39
% 3.15/1.53  
% 3.15/1.53  #Partial instantiations: 0
% 3.15/1.53  #Strategies tried      : 1
% 3.15/1.53  
% 3.15/1.53  Timing (in seconds)
% 3.15/1.53  ----------------------
% 3.15/1.53  Preprocessing        : 0.29
% 3.15/1.53  Parsing              : 0.16
% 3.15/1.53  CNF conversion       : 0.03
% 3.15/1.53  Main loop            : 0.44
% 3.15/1.53  Inferencing          : 0.15
% 3.15/1.53  Reduction            : 0.14
% 3.15/1.53  Demodulation         : 0.08
% 3.15/1.53  BG Simplification    : 0.02
% 3.15/1.53  Subsumption          : 0.10
% 3.15/1.53  Abstraction          : 0.02
% 3.15/1.53  MUC search           : 0.00
% 3.15/1.53  Cooper               : 0.00
% 3.15/1.53  Total                : 0.75
% 3.15/1.53  Index Insertion      : 0.00
% 3.15/1.53  Index Deletion       : 0.00
% 3.15/1.53  Index Matching       : 0.00
% 3.15/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
