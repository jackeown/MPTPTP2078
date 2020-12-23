%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:51 EST 2020

% Result     : Theorem 1.75s
% Output     : CNFRefutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   28 (  31 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    4
%              Number of atoms          :   30 (  42 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r2_hidden(A,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_45,plain,(
    ! [A_39,C_40] :
      ( r2_hidden(k4_tarski(A_39,k1_funct_1(C_40,A_39)),C_40)
      | ~ r2_hidden(A_39,k1_relat_1(C_40))
      | ~ v1_funct_1(C_40)
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k2_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(D_19,C_16),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    ! [C_41,A_42] :
      ( r2_hidden(k1_funct_1(C_41,A_42),k2_relat_1(C_41))
      | ~ r2_hidden(A_42,k1_relat_1(C_41))
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(resolution,[status(thm)],[c_45,c_4])).

tff(c_20,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_62,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_59,c_20])).

tff(c_66,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:06:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.75/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.14  
% 1.75/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.14  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 1.75/1.14  
% 1.75/1.14  %Foreground sorts:
% 1.75/1.14  
% 1.75/1.14  
% 1.75/1.14  %Background operators:
% 1.75/1.14  
% 1.75/1.14  
% 1.75/1.14  %Foreground operators:
% 1.75/1.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.75/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.75/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.75/1.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.75/1.14  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.75/1.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.75/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.75/1.14  tff('#skF_5', type, '#skF_5': $i).
% 1.75/1.14  tff('#skF_6', type, '#skF_6': $i).
% 1.75/1.14  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.75/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.75/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.75/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.75/1.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.75/1.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.75/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.75/1.14  
% 1.75/1.15  tff(f_52, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 1.75/1.15  tff(f_43, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 1.75/1.15  tff(f_33, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 1.75/1.15  tff(c_26, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.75/1.15  tff(c_24, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.75/1.15  tff(c_22, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.75/1.15  tff(c_45, plain, (![A_39, C_40]: (r2_hidden(k4_tarski(A_39, k1_funct_1(C_40, A_39)), C_40) | ~r2_hidden(A_39, k1_relat_1(C_40)) | ~v1_funct_1(C_40) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.75/1.15  tff(c_4, plain, (![C_16, A_1, D_19]: (r2_hidden(C_16, k2_relat_1(A_1)) | ~r2_hidden(k4_tarski(D_19, C_16), A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.75/1.15  tff(c_59, plain, (![C_41, A_42]: (r2_hidden(k1_funct_1(C_41, A_42), k2_relat_1(C_41)) | ~r2_hidden(A_42, k1_relat_1(C_41)) | ~v1_funct_1(C_41) | ~v1_relat_1(C_41))), inference(resolution, [status(thm)], [c_45, c_4])).
% 1.75/1.15  tff(c_20, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.75/1.15  tff(c_62, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_59, c_20])).
% 1.75/1.15  tff(c_66, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_62])).
% 1.75/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.75/1.15  
% 1.75/1.15  Inference rules
% 1.75/1.15  ----------------------
% 1.75/1.15  #Ref     : 0
% 1.75/1.15  #Sup     : 7
% 1.75/1.15  #Fact    : 0
% 1.75/1.15  #Define  : 0
% 1.75/1.15  #Split   : 0
% 1.75/1.15  #Chain   : 0
% 1.75/1.15  #Close   : 0
% 1.75/1.15  
% 1.75/1.15  Ordering : KBO
% 1.75/1.15  
% 1.75/1.15  Simplification rules
% 1.75/1.15  ----------------------
% 1.75/1.15  #Subsume      : 0
% 1.75/1.15  #Demod        : 3
% 1.75/1.15  #Tautology    : 3
% 1.75/1.15  #SimpNegUnit  : 0
% 1.75/1.15  #BackRed      : 0
% 1.75/1.15  
% 1.75/1.15  #Partial instantiations: 0
% 1.75/1.15  #Strategies tried      : 1
% 1.75/1.15  
% 1.75/1.15  Timing (in seconds)
% 1.75/1.15  ----------------------
% 1.75/1.15  Preprocessing        : 0.28
% 1.75/1.15  Parsing              : 0.15
% 1.75/1.15  CNF conversion       : 0.02
% 1.75/1.16  Main loop            : 0.12
% 1.75/1.16  Inferencing          : 0.06
% 1.75/1.16  Reduction            : 0.03
% 1.75/1.16  Demodulation         : 0.02
% 1.75/1.16  BG Simplification    : 0.01
% 1.75/1.16  Subsumption          : 0.02
% 1.75/1.16  Abstraction          : 0.00
% 1.75/1.16  MUC search           : 0.00
% 1.75/1.16  Cooper               : 0.00
% 1.75/1.16  Total                : 0.42
% 1.75/1.16  Index Insertion      : 0.00
% 1.75/1.16  Index Deletion       : 0.00
% 1.75/1.16  Index Matching       : 0.00
% 1.75/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
