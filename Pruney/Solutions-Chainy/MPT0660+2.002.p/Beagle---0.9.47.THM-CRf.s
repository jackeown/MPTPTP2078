%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:09 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   24 (  26 expanded)
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

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_27,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(c_10,plain,(
    ! [A_4] : v1_relat_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_3] : v1_funct_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1] : k4_relat_1(k6_relat_1(A_1)) = k6_relat_1(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_4] : v2_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    ! [A_9] :
      ( k4_relat_1(A_9) = k2_funct_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_31,plain,(
    ! [A_4] :
      ( k4_relat_1(k6_relat_1(A_4)) = k2_funct_1(k6_relat_1(A_4))
      | ~ v1_funct_1(k6_relat_1(A_4))
      | ~ v1_relat_1(k6_relat_1(A_4)) ) ),
    inference(resolution,[status(thm)],[c_12,c_28])).

tff(c_34,plain,(
    ! [A_4] : k2_funct_1(k6_relat_1(A_4)) = k6_relat_1(A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_8,c_2,c_31])).

tff(c_14,plain,(
    k2_funct_1(k6_relat_1('#skF_1')) != k6_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_37,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.36  
% 1.90/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.37  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_funct_1 > #skF_1
% 1.90/1.37  
% 1.90/1.37  %Foreground sorts:
% 1.90/1.37  
% 1.90/1.37  
% 1.90/1.37  %Background operators:
% 1.90/1.37  
% 1.90/1.37  
% 1.90/1.37  %Foreground operators:
% 1.90/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.90/1.37  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 1.90/1.37  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.90/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.37  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.90/1.37  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.90/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.37  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.90/1.37  
% 1.90/1.38  tff(f_43, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 1.90/1.38  tff(f_39, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.90/1.38  tff(f_27, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 1.90/1.38  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 1.90/1.38  tff(f_46, negated_conjecture, ~(![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 1.90/1.38  tff(c_10, plain, (![A_4]: (v1_relat_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.90/1.38  tff(c_8, plain, (![A_3]: (v1_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.90/1.38  tff(c_2, plain, (![A_1]: (k4_relat_1(k6_relat_1(A_1))=k6_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.90/1.38  tff(c_12, plain, (![A_4]: (v2_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.90/1.38  tff(c_28, plain, (![A_9]: (k4_relat_1(A_9)=k2_funct_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.90/1.38  tff(c_31, plain, (![A_4]: (k4_relat_1(k6_relat_1(A_4))=k2_funct_1(k6_relat_1(A_4)) | ~v1_funct_1(k6_relat_1(A_4)) | ~v1_relat_1(k6_relat_1(A_4)))), inference(resolution, [status(thm)], [c_12, c_28])).
% 1.90/1.38  tff(c_34, plain, (![A_4]: (k2_funct_1(k6_relat_1(A_4))=k6_relat_1(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_8, c_2, c_31])).
% 1.90/1.38  tff(c_14, plain, (k2_funct_1(k6_relat_1('#skF_1'))!=k6_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.90/1.38  tff(c_37, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_14])).
% 1.90/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.38  
% 1.90/1.38  Inference rules
% 1.90/1.38  ----------------------
% 1.90/1.38  #Ref     : 0
% 1.90/1.38  #Sup     : 3
% 1.90/1.38  #Fact    : 0
% 1.90/1.38  #Define  : 0
% 1.90/1.38  #Split   : 0
% 1.90/1.38  #Chain   : 0
% 1.90/1.38  #Close   : 0
% 1.90/1.38  
% 1.90/1.38  Ordering : KBO
% 1.90/1.38  
% 1.90/1.38  Simplification rules
% 1.90/1.38  ----------------------
% 1.90/1.38  #Subsume      : 0
% 1.90/1.38  #Demod        : 5
% 1.90/1.38  #Tautology    : 3
% 1.90/1.38  #SimpNegUnit  : 0
% 1.90/1.38  #BackRed      : 1
% 1.90/1.38  
% 1.90/1.38  #Partial instantiations: 0
% 1.90/1.38  #Strategies tried      : 1
% 1.90/1.38  
% 1.90/1.38  Timing (in seconds)
% 1.90/1.38  ----------------------
% 1.90/1.38  Preprocessing        : 0.39
% 1.90/1.38  Parsing              : 0.20
% 1.90/1.38  CNF conversion       : 0.02
% 1.90/1.38  Main loop            : 0.10
% 1.90/1.38  Inferencing          : 0.04
% 1.90/1.38  Reduction            : 0.03
% 1.90/1.38  Demodulation         : 0.03
% 1.90/1.38  BG Simplification    : 0.01
% 1.90/1.38  Subsumption          : 0.01
% 1.90/1.38  Abstraction          : 0.01
% 1.90/1.38  MUC search           : 0.00
% 1.90/1.39  Cooper               : 0.00
% 1.90/1.39  Total                : 0.53
% 1.90/1.39  Index Insertion      : 0.00
% 1.90/1.39  Index Deletion       : 0.00
% 1.90/1.39  Index Matching       : 0.00
% 1.90/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
