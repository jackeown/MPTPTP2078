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
% DateTime   : Thu Dec  3 10:02:51 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   24 (  27 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    3
%              Number of atoms          :   22 (  34 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_49,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r2_hidden(A,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_27,plain,(
    ! [A_41,D_42] :
      ( r2_hidden(k1_funct_1(A_41,D_42),k2_relat_1(A_41))
      | ~ r2_hidden(D_42,k1_relat_1(A_41))
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_20,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,
    ( ~ r2_hidden('#skF_5',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_27,c_20])).

tff(c_34,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_30])).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 10:03:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.21  
% 1.81/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.22  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 1.81/1.22  
% 1.81/1.22  %Foreground sorts:
% 1.81/1.22  
% 1.81/1.22  
% 1.81/1.22  %Background operators:
% 1.81/1.22  
% 1.81/1.22  
% 1.81/1.22  %Foreground operators:
% 1.81/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.81/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.22  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.81/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.81/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.81/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.81/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.81/1.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.81/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.81/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.81/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.81/1.22  
% 1.81/1.23  tff(f_49, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 1.81/1.23  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 1.81/1.23  tff(c_26, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.81/1.23  tff(c_24, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.81/1.23  tff(c_22, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.81/1.23  tff(c_27, plain, (![A_41, D_42]: (r2_hidden(k1_funct_1(A_41, D_42), k2_relat_1(A_41)) | ~r2_hidden(D_42, k1_relat_1(A_41)) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.81/1.23  tff(c_20, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.81/1.23  tff(c_30, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_27, c_20])).
% 1.81/1.23  tff(c_34, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_30])).
% 1.81/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.23  
% 1.81/1.23  Inference rules
% 1.81/1.23  ----------------------
% 1.81/1.23  #Ref     : 0
% 1.81/1.23  #Sup     : 1
% 1.81/1.23  #Fact    : 0
% 1.81/1.23  #Define  : 0
% 1.81/1.23  #Split   : 0
% 1.81/1.23  #Chain   : 0
% 1.81/1.23  #Close   : 0
% 1.81/1.23  
% 1.81/1.23  Ordering : KBO
% 1.81/1.23  
% 1.81/1.23  Simplification rules
% 1.81/1.23  ----------------------
% 1.81/1.23  #Subsume      : 0
% 1.81/1.23  #Demod        : 3
% 1.81/1.23  #Tautology    : 0
% 1.81/1.23  #SimpNegUnit  : 0
% 1.81/1.23  #BackRed      : 0
% 1.81/1.23  
% 1.81/1.23  #Partial instantiations: 0
% 1.81/1.23  #Strategies tried      : 1
% 1.81/1.23  
% 1.81/1.23  Timing (in seconds)
% 1.81/1.23  ----------------------
% 1.81/1.23  Preprocessing        : 0.31
% 1.81/1.23  Parsing              : 0.16
% 1.81/1.23  CNF conversion       : 0.03
% 1.81/1.23  Main loop            : 0.07
% 1.81/1.23  Inferencing          : 0.02
% 1.81/1.23  Reduction            : 0.02
% 1.81/1.23  Demodulation         : 0.02
% 1.81/1.23  BG Simplification    : 0.02
% 1.81/1.23  Subsumption          : 0.01
% 1.81/1.23  Abstraction          : 0.01
% 1.81/1.23  MUC search           : 0.00
% 1.81/1.23  Cooper               : 0.00
% 1.81/1.23  Total                : 0.41
% 1.81/1.23  Index Insertion      : 0.00
% 1.81/1.23  Index Deletion       : 0.00
% 1.81/1.23  Index Matching       : 0.00
% 1.81/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
