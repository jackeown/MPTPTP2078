%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:31 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   28 (  32 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 (  56 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_relat_1(A_4)) = k8_relat_1(A_4,B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    ! [A_21,B_22,C_23] :
      ( k5_relat_1(k5_relat_1(A_21,B_22),C_23) = k5_relat_1(A_21,k5_relat_1(B_22,C_23))
      | ~ v1_relat_1(C_23)
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_42,plain,(
    ! [A_21,B_22,A_4] :
      ( k5_relat_1(A_21,k5_relat_1(B_22,k6_relat_1(A_4))) = k8_relat_1(A_4,k5_relat_1(A_21,B_22))
      | ~ v1_relat_1(k5_relat_1(A_21,B_22))
      | ~ v1_relat_1(k6_relat_1(A_4))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_6])).

tff(c_285,plain,(
    ! [A_58,B_59,A_60] :
      ( k5_relat_1(A_58,k5_relat_1(B_59,k6_relat_1(A_60))) = k8_relat_1(A_60,k5_relat_1(A_58,B_59))
      | ~ v1_relat_1(k5_relat_1(A_58,B_59))
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_42])).

tff(c_654,plain,(
    ! [A_83,A_84,B_85] :
      ( k8_relat_1(A_83,k5_relat_1(A_84,B_85)) = k5_relat_1(A_84,k8_relat_1(A_83,B_85))
      | ~ v1_relat_1(k5_relat_1(A_84,B_85))
      | ~ v1_relat_1(B_85)
      | ~ v1_relat_1(A_84)
      | ~ v1_relat_1(B_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_285])).

tff(c_707,plain,(
    ! [A_89,A_90,B_91] :
      ( k8_relat_1(A_89,k5_relat_1(A_90,B_91)) = k5_relat_1(A_90,k8_relat_1(A_89,B_91))
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(resolution,[status(thm)],[c_2,c_654])).

tff(c_10,plain,(
    k8_relat_1('#skF_1',k5_relat_1('#skF_2','#skF_3')) != k5_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_741,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_707,c_10])).

tff(c_778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_741])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.38  
% 2.77/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.38  %$ v1_relat_1 > k8_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.77/1.38  
% 2.77/1.38  %Foreground sorts:
% 2.77/1.38  
% 2.77/1.38  
% 2.77/1.38  %Background operators:
% 2.77/1.38  
% 2.77/1.38  
% 2.77/1.38  %Foreground operators:
% 2.77/1.38  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.77/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.77/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.77/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.77/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.38  
% 2.77/1.39  tff(f_55, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_relat_1)).
% 2.77/1.39  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.77/1.39  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.77/1.39  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.77/1.39  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 2.77/1.39  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.77/1.39  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.77/1.39  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.77/1.39  tff(c_6, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_relat_1(A_4))=k8_relat_1(A_4, B_5) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.77/1.39  tff(c_4, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.77/1.39  tff(c_32, plain, (![A_21, B_22, C_23]: (k5_relat_1(k5_relat_1(A_21, B_22), C_23)=k5_relat_1(A_21, k5_relat_1(B_22, C_23)) | ~v1_relat_1(C_23) | ~v1_relat_1(B_22) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.77/1.39  tff(c_42, plain, (![A_21, B_22, A_4]: (k5_relat_1(A_21, k5_relat_1(B_22, k6_relat_1(A_4)))=k8_relat_1(A_4, k5_relat_1(A_21, B_22)) | ~v1_relat_1(k5_relat_1(A_21, B_22)) | ~v1_relat_1(k6_relat_1(A_4)) | ~v1_relat_1(B_22) | ~v1_relat_1(A_21))), inference(superposition, [status(thm), theory('equality')], [c_32, c_6])).
% 2.77/1.39  tff(c_285, plain, (![A_58, B_59, A_60]: (k5_relat_1(A_58, k5_relat_1(B_59, k6_relat_1(A_60)))=k8_relat_1(A_60, k5_relat_1(A_58, B_59)) | ~v1_relat_1(k5_relat_1(A_58, B_59)) | ~v1_relat_1(B_59) | ~v1_relat_1(A_58))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_42])).
% 2.77/1.39  tff(c_654, plain, (![A_83, A_84, B_85]: (k8_relat_1(A_83, k5_relat_1(A_84, B_85))=k5_relat_1(A_84, k8_relat_1(A_83, B_85)) | ~v1_relat_1(k5_relat_1(A_84, B_85)) | ~v1_relat_1(B_85) | ~v1_relat_1(A_84) | ~v1_relat_1(B_85))), inference(superposition, [status(thm), theory('equality')], [c_6, c_285])).
% 2.77/1.39  tff(c_707, plain, (![A_89, A_90, B_91]: (k8_relat_1(A_89, k5_relat_1(A_90, B_91))=k5_relat_1(A_90, k8_relat_1(A_89, B_91)) | ~v1_relat_1(B_91) | ~v1_relat_1(A_90))), inference(resolution, [status(thm)], [c_2, c_654])).
% 2.77/1.39  tff(c_10, plain, (k8_relat_1('#skF_1', k5_relat_1('#skF_2', '#skF_3'))!=k5_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.77/1.39  tff(c_741, plain, (~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_707, c_10])).
% 2.77/1.39  tff(c_778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_741])).
% 2.77/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.39  
% 2.77/1.39  Inference rules
% 2.77/1.39  ----------------------
% 2.77/1.39  #Ref     : 0
% 2.77/1.39  #Sup     : 186
% 2.77/1.39  #Fact    : 0
% 2.77/1.39  #Define  : 0
% 2.77/1.39  #Split   : 0
% 2.77/1.39  #Chain   : 0
% 2.77/1.39  #Close   : 0
% 2.77/1.39  
% 2.77/1.39  Ordering : KBO
% 2.77/1.39  
% 2.77/1.39  Simplification rules
% 2.77/1.39  ----------------------
% 2.77/1.39  #Subsume      : 31
% 2.77/1.39  #Demod        : 70
% 2.77/1.39  #Tautology    : 21
% 2.77/1.39  #SimpNegUnit  : 0
% 2.77/1.39  #BackRed      : 0
% 2.77/1.39  
% 2.77/1.39  #Partial instantiations: 0
% 2.77/1.39  #Strategies tried      : 1
% 2.77/1.39  
% 2.77/1.39  Timing (in seconds)
% 2.77/1.39  ----------------------
% 2.77/1.39  Preprocessing        : 0.27
% 2.77/1.39  Parsing              : 0.14
% 2.77/1.39  CNF conversion       : 0.02
% 2.77/1.39  Main loop            : 0.37
% 2.77/1.39  Inferencing          : 0.16
% 2.77/1.39  Reduction            : 0.10
% 2.77/1.39  Demodulation         : 0.07
% 2.77/1.39  BG Simplification    : 0.02
% 2.77/1.39  Subsumption          : 0.07
% 2.77/1.39  Abstraction          : 0.03
% 2.77/1.39  MUC search           : 0.00
% 2.77/1.39  Cooper               : 0.00
% 2.77/1.39  Total                : 0.66
% 2.77/1.39  Index Insertion      : 0.00
% 2.77/1.39  Index Deletion       : 0.00
% 2.77/1.39  Index Matching       : 0.00
% 2.77/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
