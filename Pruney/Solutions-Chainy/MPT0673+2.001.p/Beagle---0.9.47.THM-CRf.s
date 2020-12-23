%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:22 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   29 (  33 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   48 (  62 expanded)
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

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( v2_funct_1(B)
         => v2_funct_1(k8_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_52,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & v2_funct_1(B) )
           => v2_funct_1(k5_relat_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_funct_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_4] : v1_relat_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_4] : v1_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( k5_relat_1(B_3,k6_relat_1(A_2)) = k8_relat_1(A_2,B_3)
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [A_14,B_15] :
      ( v2_funct_1(k5_relat_1(A_14,B_15))
      | ~ v2_funct_1(B_15)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_37,plain,(
    ! [A_2,B_3] :
      ( v2_funct_1(k8_relat_1(A_2,B_3))
      | ~ v2_funct_1(k6_relat_1(A_2))
      | ~ v2_funct_1(B_3)
      | ~ v1_funct_1(k6_relat_1(A_2))
      | ~ v1_relat_1(k6_relat_1(A_2))
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3)
      | ~ v1_relat_1(B_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_34])).

tff(c_40,plain,(
    ! [A_16,B_17] :
      ( v2_funct_1(k8_relat_1(A_16,B_17))
      | ~ v2_funct_1(B_17)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8,c_12,c_37])).

tff(c_14,plain,(
    ~ v2_funct_1(k8_relat_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_43,plain,
    ( ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_14])).

tff(c_47,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:07:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.14  
% 1.74/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.15  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_1
% 1.74/1.15  
% 1.74/1.15  %Foreground sorts:
% 1.74/1.15  
% 1.74/1.15  
% 1.74/1.15  %Background operators:
% 1.74/1.15  
% 1.74/1.15  
% 1.74/1.15  %Foreground operators:
% 1.74/1.15  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.74/1.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.74/1.15  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.74/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.15  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.74/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.74/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.74/1.15  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.74/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.15  
% 1.74/1.16  tff(f_61, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => v2_funct_1(k8_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_funct_1)).
% 1.74/1.16  tff(f_35, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.74/1.16  tff(f_52, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 1.74/1.16  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 1.74/1.16  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(A) & v2_funct_1(B)) => v2_funct_1(k5_relat_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_funct_1)).
% 1.74/1.16  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.74/1.16  tff(c_18, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.74/1.16  tff(c_16, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.74/1.16  tff(c_6, plain, (![A_4]: (v1_relat_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.74/1.16  tff(c_8, plain, (![A_4]: (v1_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.74/1.16  tff(c_12, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.74/1.16  tff(c_4, plain, (![B_3, A_2]: (k5_relat_1(B_3, k6_relat_1(A_2))=k8_relat_1(A_2, B_3) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.74/1.16  tff(c_34, plain, (![A_14, B_15]: (v2_funct_1(k5_relat_1(A_14, B_15)) | ~v2_funct_1(B_15) | ~v2_funct_1(A_14) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.74/1.16  tff(c_37, plain, (![A_2, B_3]: (v2_funct_1(k8_relat_1(A_2, B_3)) | ~v2_funct_1(k6_relat_1(A_2)) | ~v2_funct_1(B_3) | ~v1_funct_1(k6_relat_1(A_2)) | ~v1_relat_1(k6_relat_1(A_2)) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3) | ~v1_relat_1(B_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_34])).
% 1.74/1.16  tff(c_40, plain, (![A_16, B_17]: (v2_funct_1(k8_relat_1(A_16, B_17)) | ~v2_funct_1(B_17) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8, c_12, c_37])).
% 1.74/1.16  tff(c_14, plain, (~v2_funct_1(k8_relat_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.74/1.16  tff(c_43, plain, (~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_40, c_14])).
% 1.74/1.16  tff(c_47, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_43])).
% 1.74/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.16  
% 1.74/1.16  Inference rules
% 1.74/1.16  ----------------------
% 1.74/1.16  #Ref     : 0
% 1.74/1.16  #Sup     : 4
% 1.74/1.16  #Fact    : 0
% 1.74/1.16  #Define  : 0
% 1.74/1.16  #Split   : 0
% 1.74/1.16  #Chain   : 0
% 1.74/1.16  #Close   : 0
% 1.74/1.16  
% 1.74/1.16  Ordering : KBO
% 1.74/1.16  
% 1.74/1.16  Simplification rules
% 1.74/1.16  ----------------------
% 1.74/1.16  #Subsume      : 0
% 1.74/1.16  #Demod        : 7
% 1.74/1.16  #Tautology    : 3
% 1.74/1.16  #SimpNegUnit  : 0
% 1.74/1.16  #BackRed      : 0
% 1.74/1.16  
% 1.74/1.16  #Partial instantiations: 0
% 1.74/1.16  #Strategies tried      : 1
% 1.74/1.16  
% 1.74/1.16  Timing (in seconds)
% 1.74/1.16  ----------------------
% 1.74/1.16  Preprocessing        : 0.29
% 1.74/1.16  Parsing              : 0.16
% 1.74/1.16  CNF conversion       : 0.02
% 1.74/1.16  Main loop            : 0.09
% 1.74/1.16  Inferencing          : 0.04
% 1.74/1.17  Reduction            : 0.03
% 1.74/1.17  Demodulation         : 0.02
% 1.74/1.17  BG Simplification    : 0.01
% 1.74/1.17  Subsumption          : 0.01
% 1.74/1.17  Abstraction          : 0.00
% 1.74/1.17  MUC search           : 0.00
% 1.74/1.17  Cooper               : 0.00
% 1.74/1.17  Total                : 0.40
% 1.74/1.17  Index Insertion      : 0.00
% 1.74/1.17  Index Deletion       : 0.00
% 1.74/1.17  Index Matching       : 0.00
% 1.74/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
