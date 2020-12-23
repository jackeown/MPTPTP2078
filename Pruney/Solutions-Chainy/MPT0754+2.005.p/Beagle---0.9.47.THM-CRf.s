%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:30 EST 2020

% Result     : Theorem 1.47s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   25 (  32 expanded)
%              Number of leaves         :   13 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  89 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r1_tarski > v5_ordinal1 > v1_relat_1 > v1_funct_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ! [C] :
            ( ( v1_relat_1(C)
              & v5_relat_1(C,A)
              & v1_funct_1(C)
              & v5_ordinal1(C) )
           => ( v1_relat_1(C)
              & v5_relat_1(C,B)
              & v1_funct_1(C)
              & v5_ordinal1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_ordinal1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v5_relat_1(C,A) )
         => v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t218_relat_1)).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_17,plain,(
    ! [C_6,B_7,A_8] :
      ( v5_relat_1(C_6,B_7)
      | ~ v5_relat_1(C_6,A_8)
      | ~ v1_relat_1(C_6)
      | ~ r1_tarski(A_8,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_19,plain,(
    ! [B_7] :
      ( v5_relat_1('#skF_3',B_7)
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski('#skF_1',B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_17])).

tff(c_23,plain,(
    ! [B_9] :
      ( v5_relat_1('#skF_3',B_9)
      | ~ r1_tarski('#skF_1',B_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_19])).

tff(c_8,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    v5_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,
    ( ~ v5_ordinal1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ~ v5_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_8,c_6,c_4])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_23,c_16])).

tff(c_35,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.47/1.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.06  
% 1.58/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.07  %$ v5_relat_1 > r1_tarski > v5_ordinal1 > v1_relat_1 > v1_funct_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.58/1.07  
% 1.58/1.07  %Foreground sorts:
% 1.58/1.07  
% 1.58/1.07  
% 1.58/1.07  %Background operators:
% 1.58/1.07  
% 1.58/1.07  
% 1.58/1.07  %Foreground operators:
% 1.58/1.07  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.58/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.58/1.07  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.58/1.07  tff('#skF_2', type, '#skF_2': $i).
% 1.58/1.07  tff('#skF_3', type, '#skF_3': $i).
% 1.58/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.07  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.58/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.58/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.07  
% 1.58/1.07  tff(f_54, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (![C]: ((((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) & v5_ordinal1(C)) => (((v1_relat_1(C) & v5_relat_1(C, B)) & v1_funct_1(C)) & v5_ordinal1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_ordinal1)).
% 1.58/1.07  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v5_relat_1(C, A)) => v5_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t218_relat_1)).
% 1.58/1.07  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.58/1.07  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.58/1.07  tff(c_10, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.58/1.07  tff(c_17, plain, (![C_6, B_7, A_8]: (v5_relat_1(C_6, B_7) | ~v5_relat_1(C_6, A_8) | ~v1_relat_1(C_6) | ~r1_tarski(A_8, B_7))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.58/1.07  tff(c_19, plain, (![B_7]: (v5_relat_1('#skF_3', B_7) | ~v1_relat_1('#skF_3') | ~r1_tarski('#skF_1', B_7))), inference(resolution, [status(thm)], [c_10, c_17])).
% 1.58/1.07  tff(c_23, plain, (![B_9]: (v5_relat_1('#skF_3', B_9) | ~r1_tarski('#skF_1', B_9))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_19])).
% 1.58/1.07  tff(c_8, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.58/1.07  tff(c_6, plain, (v5_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.58/1.07  tff(c_4, plain, (~v5_ordinal1('#skF_3') | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.58/1.07  tff(c_16, plain, (~v5_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_8, c_6, c_4])).
% 1.58/1.07  tff(c_28, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_23, c_16])).
% 1.58/1.07  tff(c_35, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_28])).
% 1.58/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.07  
% 1.58/1.07  Inference rules
% 1.58/1.07  ----------------------
% 1.58/1.07  #Ref     : 0
% 1.58/1.07  #Sup     : 3
% 1.58/1.07  #Fact    : 0
% 1.58/1.07  #Define  : 0
% 1.58/1.07  #Split   : 0
% 1.58/1.07  #Chain   : 0
% 1.58/1.07  #Close   : 0
% 1.58/1.07  
% 1.58/1.07  Ordering : KBO
% 1.58/1.07  
% 1.58/1.07  Simplification rules
% 1.58/1.07  ----------------------
% 1.58/1.07  #Subsume      : 0
% 1.58/1.07  #Demod        : 6
% 1.58/1.07  #Tautology    : 0
% 1.58/1.07  #SimpNegUnit  : 0
% 1.58/1.07  #BackRed      : 0
% 1.58/1.07  
% 1.58/1.07  #Partial instantiations: 0
% 1.58/1.07  #Strategies tried      : 1
% 1.58/1.07  
% 1.58/1.07  Timing (in seconds)
% 1.58/1.07  ----------------------
% 1.58/1.08  Preprocessing        : 0.24
% 1.58/1.08  Parsing              : 0.13
% 1.58/1.08  CNF conversion       : 0.02
% 1.58/1.08  Main loop            : 0.08
% 1.58/1.08  Inferencing          : 0.04
% 1.58/1.08  Reduction            : 0.02
% 1.58/1.08  Demodulation         : 0.02
% 1.58/1.08  BG Simplification    : 0.01
% 1.58/1.08  Subsumption          : 0.01
% 1.58/1.08  Abstraction          : 0.00
% 1.58/1.08  MUC search           : 0.00
% 1.58/1.08  Cooper               : 0.00
% 1.58/1.08  Total                : 0.35
% 1.58/1.08  Index Insertion      : 0.00
% 1.58/1.08  Index Deletion       : 0.00
% 1.58/1.08  Index Matching       : 0.00
% 1.58/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
