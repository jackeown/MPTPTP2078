%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:42 EST 2020

% Result     : Theorem 1.40s
% Output     : CNFRefutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    2
%              Number of atoms          :    6 (   6 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > #nlpp > k6_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_32,negated_conjecture,(
    ~ ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(c_4,plain,(
    ! [A_1] : v2_funct_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ~ v2_funct_1(k6_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.40/1.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.40/1.00  
% 1.40/1.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.40/1.02  %$ v2_funct_1 > v1_relat_1 > #nlpp > k6_relat_1 > #skF_1
% 1.40/1.02  
% 1.40/1.02  %Foreground sorts:
% 1.40/1.02  
% 1.40/1.02  
% 1.40/1.02  %Background operators:
% 1.40/1.02  
% 1.40/1.02  
% 1.40/1.02  %Foreground operators:
% 1.40/1.02  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.40/1.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.40/1.02  tff('#skF_1', type, '#skF_1': $i).
% 1.40/1.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.40/1.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.40/1.02  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.40/1.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.40/1.02  
% 1.40/1.02  tff(f_29, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 1.40/1.02  tff(f_32, negated_conjecture, ~(![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 1.40/1.02  tff(c_4, plain, (![A_1]: (v2_funct_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.40/1.02  tff(c_6, plain, (~v2_funct_1(k6_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.40/1.02  tff(c_8, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.40/1.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.40/1.02  
% 1.40/1.02  Inference rules
% 1.40/1.02  ----------------------
% 1.40/1.02  #Ref     : 0
% 1.40/1.02  #Sup     : 0
% 1.40/1.02  #Fact    : 0
% 1.40/1.02  #Define  : 0
% 1.40/1.02  #Split   : 0
% 1.40/1.02  #Chain   : 0
% 1.40/1.02  #Close   : 0
% 1.40/1.02  
% 1.40/1.02  Ordering : KBO
% 1.40/1.02  
% 1.40/1.02  Simplification rules
% 1.40/1.02  ----------------------
% 1.40/1.02  #Subsume      : 2
% 1.40/1.02  #Demod        : 1
% 1.40/1.02  #Tautology    : 0
% 1.40/1.02  #SimpNegUnit  : 0
% 1.40/1.02  #BackRed      : 0
% 1.40/1.02  
% 1.40/1.02  #Partial instantiations: 0
% 1.40/1.02  #Strategies tried      : 1
% 1.40/1.02  
% 1.40/1.02  Timing (in seconds)
% 1.40/1.02  ----------------------
% 1.40/1.02  Preprocessing        : 0.22
% 1.40/1.03  Parsing              : 0.12
% 1.40/1.03  CNF conversion       : 0.01
% 1.40/1.03  Main loop            : 0.02
% 1.40/1.03  Inferencing          : 0.00
% 1.40/1.03  Reduction            : 0.01
% 1.40/1.03  Demodulation         : 0.01
% 1.40/1.03  BG Simplification    : 0.01
% 1.40/1.03  Subsumption          : 0.00
% 1.40/1.03  Abstraction          : 0.00
% 1.40/1.03  MUC search           : 0.00
% 1.40/1.03  Cooper               : 0.00
% 1.40/1.03  Total                : 0.26
% 1.40/1.03  Index Insertion      : 0.00
% 1.40/1.03  Index Deletion       : 0.00
% 1.40/1.03  Index Matching       : 0.00
% 1.40/1.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
