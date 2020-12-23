%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:22 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   29 (  33 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   49 (  63 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( v2_funct_1(B)
         => v2_funct_1(k8_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_51,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B)
        & v2_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v2_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_funct_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3] : v1_funct_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_6] : v2_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_relat_1(A_1)) = k8_relat_1(A_1,B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_33,plain,(
    ! [A_12,B_13] :
      ( v2_funct_1(k5_relat_1(A_12,B_13))
      | ~ v2_funct_1(B_13)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_36,plain,(
    ! [A_1,B_2] :
      ( v2_funct_1(k8_relat_1(A_1,B_2))
      | ~ v2_funct_1(k6_relat_1(A_1))
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ v2_funct_1(B_2)
      | ~ v1_funct_1(B_2)
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_33])).

tff(c_45,plain,(
    ! [A_16,B_17] :
      ( v2_funct_1(k8_relat_1(A_16,B_17))
      | ~ v2_funct_1(B_17)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_12,c_36])).

tff(c_14,plain,(
    ~ v2_funct_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,
    ( ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_45,c_14])).

tff(c_52,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.12  
% 1.55/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.13  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_1
% 1.55/1.13  
% 1.55/1.13  %Foreground sorts:
% 1.55/1.13  
% 1.55/1.13  
% 1.55/1.13  %Background operators:
% 1.55/1.13  
% 1.55/1.13  
% 1.55/1.13  %Foreground operators:
% 1.55/1.13  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.55/1.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.55/1.13  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.55/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.55/1.13  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.55/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.55/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.55/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.55/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.55/1.13  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.55/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.55/1.13  
% 1.55/1.14  tff(f_60, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => v2_funct_1(k8_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_funct_1)).
% 1.55/1.14  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.55/1.14  tff(f_51, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 1.55/1.14  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 1.55/1.14  tff(f_49, axiom, (![A, B]: ((((((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) & v2_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v2_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_funct_1)).
% 1.55/1.14  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.55/1.14  tff(c_18, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.55/1.14  tff(c_16, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.55/1.14  tff(c_4, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.55/1.14  tff(c_6, plain, (![A_3]: (v1_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.55/1.14  tff(c_12, plain, (![A_6]: (v2_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.55/1.14  tff(c_2, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_relat_1(A_1))=k8_relat_1(A_1, B_2) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.55/1.14  tff(c_33, plain, (![A_12, B_13]: (v2_funct_1(k5_relat_1(A_12, B_13)) | ~v2_funct_1(B_13) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.55/1.14  tff(c_36, plain, (![A_1, B_2]: (v2_funct_1(k8_relat_1(A_1, B_2)) | ~v2_funct_1(k6_relat_1(A_1)) | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)) | ~v2_funct_1(B_2) | ~v1_funct_1(B_2) | ~v1_relat_1(B_2) | ~v1_relat_1(B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_33])).
% 1.55/1.14  tff(c_45, plain, (![A_16, B_17]: (v2_funct_1(k8_relat_1(A_16, B_17)) | ~v2_funct_1(B_17) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_12, c_36])).
% 1.55/1.14  tff(c_14, plain, (~v2_funct_1(k8_relat_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.55/1.14  tff(c_48, plain, (~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_45, c_14])).
% 1.55/1.14  tff(c_52, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_48])).
% 1.55/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.14  
% 1.55/1.14  Inference rules
% 1.55/1.14  ----------------------
% 1.55/1.14  #Ref     : 0
% 1.55/1.14  #Sup     : 5
% 1.55/1.14  #Fact    : 0
% 1.55/1.14  #Define  : 0
% 1.55/1.14  #Split   : 0
% 1.55/1.14  #Chain   : 0
% 1.55/1.14  #Close   : 0
% 1.55/1.14  
% 1.55/1.14  Ordering : KBO
% 1.55/1.14  
% 1.55/1.14  Simplification rules
% 1.55/1.14  ----------------------
% 1.55/1.14  #Subsume      : 0
% 1.55/1.14  #Demod        : 9
% 1.55/1.14  #Tautology    : 2
% 1.55/1.14  #SimpNegUnit  : 0
% 1.55/1.14  #BackRed      : 0
% 1.55/1.14  
% 1.55/1.14  #Partial instantiations: 0
% 1.55/1.14  #Strategies tried      : 1
% 1.55/1.14  
% 1.55/1.14  Timing (in seconds)
% 1.55/1.14  ----------------------
% 1.55/1.14  Preprocessing        : 0.25
% 1.55/1.14  Parsing              : 0.14
% 1.55/1.14  CNF conversion       : 0.02
% 1.55/1.14  Main loop            : 0.09
% 1.55/1.14  Inferencing          : 0.04
% 1.55/1.14  Reduction            : 0.03
% 1.55/1.14  Demodulation         : 0.02
% 1.55/1.14  BG Simplification    : 0.01
% 1.55/1.14  Subsumption          : 0.01
% 1.55/1.14  Abstraction          : 0.00
% 1.55/1.14  MUC search           : 0.00
% 1.55/1.14  Cooper               : 0.00
% 1.55/1.14  Total                : 0.37
% 1.55/1.14  Index Insertion      : 0.00
% 1.55/1.14  Index Deletion       : 0.00
% 1.55/1.14  Index Matching       : 0.00
% 1.55/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
