%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:31 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   32 (  37 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  53 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( k5_relat_1(k6_relat_1(A_19),B_20) = k7_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ! [B_20,A_19] :
      ( v1_relat_1(k7_relat_1(B_20,A_19))
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(k6_relat_1(A_19))
      | ~ v1_relat_1(B_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2])).

tff(c_54,plain,(
    ! [B_20,A_19] :
      ( v1_relat_1(k7_relat_1(B_20,A_19))
      | ~ v1_relat_1(B_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_42])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_relat_1(A_8)) = k8_relat_1(A_8,B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_75,plain,(
    ! [B_27,C_28,A_29] :
      ( k7_relat_1(k5_relat_1(B_27,C_28),A_29) = k5_relat_1(k7_relat_1(B_27,A_29),C_28)
      | ~ v1_relat_1(C_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_90,plain,(
    ! [B_9,A_29,A_8] :
      ( k5_relat_1(k7_relat_1(B_9,A_29),k6_relat_1(A_8)) = k7_relat_1(k8_relat_1(A_8,B_9),A_29)
      | ~ v1_relat_1(k6_relat_1(A_8))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_75])).

tff(c_146,plain,(
    ! [B_39,A_40,A_41] :
      ( k5_relat_1(k7_relat_1(B_39,A_40),k6_relat_1(A_41)) = k7_relat_1(k8_relat_1(A_41,B_39),A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_90])).

tff(c_232,plain,(
    ! [A_58,B_59,A_60] :
      ( k8_relat_1(A_58,k7_relat_1(B_59,A_60)) = k7_relat_1(k8_relat_1(A_58,B_59),A_60)
      | ~ v1_relat_1(k7_relat_1(B_59,A_60))
      | ~ v1_relat_1(B_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_8])).

tff(c_262,plain,(
    ! [A_61,B_62,A_63] :
      ( k8_relat_1(A_61,k7_relat_1(B_62,A_63)) = k7_relat_1(k8_relat_1(A_61,B_62),A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_54,c_232])).

tff(c_12,plain,(
    k8_relat_1('#skF_1',k7_relat_1('#skF_3','#skF_2')) != k7_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_278,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_12])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.27  
% 2.10/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.27  %$ v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.10/1.27  
% 2.10/1.27  %Foreground sorts:
% 2.10/1.27  
% 2.10/1.27  
% 2.10/1.27  %Background operators:
% 2.10/1.27  
% 2.10/1.27  
% 2.10/1.27  %Foreground operators:
% 2.10/1.27  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.10/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.10/1.27  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.10/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.27  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.10/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.27  
% 2.10/1.28  tff(f_53, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_relat_1)).
% 2.10/1.28  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.10/1.28  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.10/1.28  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.10/1.28  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 2.10/1.28  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 2.10/1.28  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.10/1.28  tff(c_4, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.28  tff(c_32, plain, (![A_19, B_20]: (k5_relat_1(k6_relat_1(A_19), B_20)=k7_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.10/1.28  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.28  tff(c_42, plain, (![B_20, A_19]: (v1_relat_1(k7_relat_1(B_20, A_19)) | ~v1_relat_1(B_20) | ~v1_relat_1(k6_relat_1(A_19)) | ~v1_relat_1(B_20))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2])).
% 2.10/1.28  tff(c_54, plain, (![B_20, A_19]: (v1_relat_1(k7_relat_1(B_20, A_19)) | ~v1_relat_1(B_20))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_42])).
% 2.10/1.28  tff(c_8, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_relat_1(A_8))=k8_relat_1(A_8, B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.10/1.28  tff(c_75, plain, (![B_27, C_28, A_29]: (k7_relat_1(k5_relat_1(B_27, C_28), A_29)=k5_relat_1(k7_relat_1(B_27, A_29), C_28) | ~v1_relat_1(C_28) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.10/1.28  tff(c_90, plain, (![B_9, A_29, A_8]: (k5_relat_1(k7_relat_1(B_9, A_29), k6_relat_1(A_8))=k7_relat_1(k8_relat_1(A_8, B_9), A_29) | ~v1_relat_1(k6_relat_1(A_8)) | ~v1_relat_1(B_9) | ~v1_relat_1(B_9))), inference(superposition, [status(thm), theory('equality')], [c_8, c_75])).
% 2.10/1.28  tff(c_146, plain, (![B_39, A_40, A_41]: (k5_relat_1(k7_relat_1(B_39, A_40), k6_relat_1(A_41))=k7_relat_1(k8_relat_1(A_41, B_39), A_40) | ~v1_relat_1(B_39))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_90])).
% 2.10/1.28  tff(c_232, plain, (![A_58, B_59, A_60]: (k8_relat_1(A_58, k7_relat_1(B_59, A_60))=k7_relat_1(k8_relat_1(A_58, B_59), A_60) | ~v1_relat_1(k7_relat_1(B_59, A_60)) | ~v1_relat_1(B_59))), inference(superposition, [status(thm), theory('equality')], [c_146, c_8])).
% 2.10/1.28  tff(c_262, plain, (![A_61, B_62, A_63]: (k8_relat_1(A_61, k7_relat_1(B_62, A_63))=k7_relat_1(k8_relat_1(A_61, B_62), A_63) | ~v1_relat_1(B_62))), inference(resolution, [status(thm)], [c_54, c_232])).
% 2.10/1.28  tff(c_12, plain, (k8_relat_1('#skF_1', k7_relat_1('#skF_3', '#skF_2'))!=k7_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.10/1.28  tff(c_278, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_262, c_12])).
% 2.10/1.28  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_278])).
% 2.10/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.28  
% 2.10/1.28  Inference rules
% 2.10/1.28  ----------------------
% 2.10/1.28  #Ref     : 0
% 2.10/1.28  #Sup     : 60
% 2.10/1.28  #Fact    : 0
% 2.10/1.28  #Define  : 0
% 2.10/1.28  #Split   : 0
% 2.10/1.28  #Chain   : 0
% 2.10/1.28  #Close   : 0
% 2.10/1.28  
% 2.10/1.28  Ordering : KBO
% 2.10/1.28  
% 2.10/1.28  Simplification rules
% 2.10/1.28  ----------------------
% 2.10/1.28  #Subsume      : 3
% 2.10/1.28  #Demod        : 47
% 2.10/1.28  #Tautology    : 24
% 2.10/1.28  #SimpNegUnit  : 0
% 2.10/1.28  #BackRed      : 0
% 2.10/1.28  
% 2.10/1.28  #Partial instantiations: 0
% 2.10/1.28  #Strategies tried      : 1
% 2.10/1.28  
% 2.10/1.28  Timing (in seconds)
% 2.10/1.28  ----------------------
% 2.10/1.29  Preprocessing        : 0.27
% 2.10/1.29  Parsing              : 0.14
% 2.10/1.29  CNF conversion       : 0.02
% 2.10/1.29  Main loop            : 0.22
% 2.10/1.29  Inferencing          : 0.09
% 2.10/1.29  Reduction            : 0.07
% 2.10/1.29  Demodulation         : 0.05
% 2.10/1.29  BG Simplification    : 0.01
% 2.10/1.29  Subsumption          : 0.04
% 2.10/1.29  Abstraction          : 0.01
% 2.10/1.29  MUC search           : 0.00
% 2.10/1.29  Cooper               : 0.00
% 2.10/1.29  Total                : 0.52
% 2.10/1.29  Index Insertion      : 0.00
% 2.10/1.29  Index Deletion       : 0.00
% 2.10/1.29  Index Matching       : 0.00
% 2.10/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
