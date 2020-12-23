%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:09 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   23 (  25 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_funct_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_27,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_41,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_6,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_3] : v1_funct_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1] : k4_relat_1(k6_relat_1(A_1)) = k6_relat_1(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_4] : v2_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_25,plain,(
    ! [A_9] :
      ( k4_relat_1(A_9) = k2_funct_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ! [A_4] :
      ( k4_relat_1(k6_relat_1(A_4)) = k2_funct_1(k6_relat_1(A_4))
      | ~ v1_funct_1(k6_relat_1(A_4))
      | ~ v1_relat_1(k6_relat_1(A_4)) ) ),
    inference(resolution,[status(thm)],[c_10,c_25])).

tff(c_31,plain,(
    ! [A_4] : k2_funct_1(k6_relat_1(A_4)) = k6_relat_1(A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8,c_2,c_28])).

tff(c_12,plain,(
    k2_funct_1(k6_relat_1('#skF_1')) != k6_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.05  
% 1.51/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.05  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_funct_1 > #skF_1
% 1.51/1.05  
% 1.51/1.05  %Foreground sorts:
% 1.51/1.05  
% 1.51/1.05  
% 1.51/1.05  %Background operators:
% 1.51/1.05  
% 1.51/1.05  
% 1.51/1.05  %Foreground operators:
% 1.51/1.05  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.51/1.05  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.51/1.05  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.51/1.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.51/1.05  tff('#skF_1', type, '#skF_1': $i).
% 1.51/1.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.51/1.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.51/1.05  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.51/1.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.51/1.05  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.51/1.05  
% 1.51/1.06  tff(f_39, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.51/1.06  tff(f_27, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 1.51/1.06  tff(f_41, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 1.51/1.06  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 1.51/1.06  tff(f_44, negated_conjecture, ~(![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 1.51/1.06  tff(c_6, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.51/1.06  tff(c_8, plain, (![A_3]: (v1_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.51/1.06  tff(c_2, plain, (![A_1]: (k4_relat_1(k6_relat_1(A_1))=k6_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.51/1.06  tff(c_10, plain, (![A_4]: (v2_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.51/1.06  tff(c_25, plain, (![A_9]: (k4_relat_1(A_9)=k2_funct_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.51/1.06  tff(c_28, plain, (![A_4]: (k4_relat_1(k6_relat_1(A_4))=k2_funct_1(k6_relat_1(A_4)) | ~v1_funct_1(k6_relat_1(A_4)) | ~v1_relat_1(k6_relat_1(A_4)))), inference(resolution, [status(thm)], [c_10, c_25])).
% 1.51/1.06  tff(c_31, plain, (![A_4]: (k2_funct_1(k6_relat_1(A_4))=k6_relat_1(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8, c_2, c_28])).
% 1.51/1.06  tff(c_12, plain, (k2_funct_1(k6_relat_1('#skF_1'))!=k6_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.51/1.06  tff(c_34, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31, c_12])).
% 1.51/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.06  
% 1.51/1.06  Inference rules
% 1.51/1.06  ----------------------
% 1.51/1.06  #Ref     : 0
% 1.51/1.06  #Sup     : 3
% 1.51/1.06  #Fact    : 0
% 1.51/1.06  #Define  : 0
% 1.51/1.06  #Split   : 0
% 1.51/1.06  #Chain   : 0
% 1.51/1.06  #Close   : 0
% 1.51/1.06  
% 1.51/1.06  Ordering : KBO
% 1.51/1.06  
% 1.51/1.06  Simplification rules
% 1.51/1.06  ----------------------
% 1.51/1.06  #Subsume      : 0
% 1.51/1.06  #Demod        : 4
% 1.51/1.06  #Tautology    : 2
% 1.51/1.06  #SimpNegUnit  : 0
% 1.51/1.06  #BackRed      : 1
% 1.51/1.06  
% 1.51/1.06  #Partial instantiations: 0
% 1.51/1.06  #Strategies tried      : 1
% 1.51/1.06  
% 1.51/1.06  Timing (in seconds)
% 1.51/1.06  ----------------------
% 1.51/1.06  Preprocessing        : 0.25
% 1.51/1.06  Parsing              : 0.13
% 1.51/1.06  CNF conversion       : 0.01
% 1.51/1.06  Main loop            : 0.06
% 1.51/1.06  Inferencing          : 0.03
% 1.51/1.06  Reduction            : 0.02
% 1.51/1.06  Demodulation         : 0.01
% 1.51/1.06  BG Simplification    : 0.01
% 1.51/1.06  Subsumption          : 0.00
% 1.51/1.06  Abstraction          : 0.01
% 1.51/1.06  MUC search           : 0.00
% 1.51/1.06  Cooper               : 0.00
% 1.51/1.06  Total                : 0.33
% 1.51/1.06  Index Insertion      : 0.00
% 1.51/1.06  Index Deletion       : 0.00
% 1.51/1.06  Index Matching       : 0.00
% 1.51/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
