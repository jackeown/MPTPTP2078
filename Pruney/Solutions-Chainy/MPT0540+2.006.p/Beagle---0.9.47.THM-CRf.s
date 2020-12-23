%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:31 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   28 (  31 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  39 expanded)
%              Number of equality atoms :   10 (  13 expanded)
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

tff(f_47,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k7_relat_1(k8_relat_1(A,C),B) = k8_relat_1(A,k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( v1_relat_1(k7_relat_1(A_2,B_3))
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_relat_1(A_8)) = k8_relat_1(A_8,B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [B_15,C_16,A_17] :
      ( k7_relat_1(k5_relat_1(B_15,C_16),A_17) = k5_relat_1(k7_relat_1(B_15,A_17),C_16)
      | ~ v1_relat_1(C_16)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36,plain,(
    ! [B_9,A_17,A_8] :
      ( k5_relat_1(k7_relat_1(B_9,A_17),k6_relat_1(A_8)) = k7_relat_1(k8_relat_1(A_8,B_9),A_17)
      | ~ v1_relat_1(k6_relat_1(A_8))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_24])).

tff(c_41,plain,(
    ! [B_18,A_19,A_20] :
      ( k5_relat_1(k7_relat_1(B_18,A_19),k6_relat_1(A_20)) = k7_relat_1(k8_relat_1(A_20,B_18),A_19)
      | ~ v1_relat_1(B_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_81,plain,(
    ! [A_27,B_28,A_29] :
      ( k8_relat_1(A_27,k7_relat_1(B_28,A_29)) = k7_relat_1(k8_relat_1(A_27,B_28),A_29)
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(k7_relat_1(B_28,A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_41])).

tff(c_90,plain,(
    ! [A_30,A_31,B_32] :
      ( k8_relat_1(A_30,k7_relat_1(A_31,B_32)) = k7_relat_1(k8_relat_1(A_30,A_31),B_32)
      | ~ v1_relat_1(A_31) ) ),
    inference(resolution,[status(thm)],[c_4,c_81])).

tff(c_10,plain,(
    k8_relat_1('#skF_1',k7_relat_1('#skF_3','#skF_2')) != k7_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_99,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_10])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_99])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:26:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.14  
% 1.77/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.15  %$ v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.77/1.15  
% 1.77/1.15  %Foreground sorts:
% 1.77/1.15  
% 1.77/1.15  
% 1.77/1.15  %Background operators:
% 1.77/1.15  
% 1.77/1.15  
% 1.77/1.15  %Foreground operators:
% 1.77/1.15  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.77/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.15  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.77/1.15  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.77/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.77/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.77/1.15  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.77/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.15  
% 1.77/1.15  tff(f_47, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_relat_1)).
% 1.77/1.15  tff(f_31, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.77/1.15  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 1.77/1.15  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.77/1.15  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 1.77/1.15  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.77/1.15  tff(c_4, plain, (![A_2, B_3]: (v1_relat_1(k7_relat_1(A_2, B_3)) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.77/1.15  tff(c_8, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_relat_1(A_8))=k8_relat_1(A_8, B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.77/1.15  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.77/1.15  tff(c_24, plain, (![B_15, C_16, A_17]: (k7_relat_1(k5_relat_1(B_15, C_16), A_17)=k5_relat_1(k7_relat_1(B_15, A_17), C_16) | ~v1_relat_1(C_16) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.77/1.15  tff(c_36, plain, (![B_9, A_17, A_8]: (k5_relat_1(k7_relat_1(B_9, A_17), k6_relat_1(A_8))=k7_relat_1(k8_relat_1(A_8, B_9), A_17) | ~v1_relat_1(k6_relat_1(A_8)) | ~v1_relat_1(B_9) | ~v1_relat_1(B_9))), inference(superposition, [status(thm), theory('equality')], [c_8, c_24])).
% 1.77/1.15  tff(c_41, plain, (![B_18, A_19, A_20]: (k5_relat_1(k7_relat_1(B_18, A_19), k6_relat_1(A_20))=k7_relat_1(k8_relat_1(A_20, B_18), A_19) | ~v1_relat_1(B_18))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 1.77/1.15  tff(c_81, plain, (![A_27, B_28, A_29]: (k8_relat_1(A_27, k7_relat_1(B_28, A_29))=k7_relat_1(k8_relat_1(A_27, B_28), A_29) | ~v1_relat_1(B_28) | ~v1_relat_1(k7_relat_1(B_28, A_29)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_41])).
% 1.77/1.15  tff(c_90, plain, (![A_30, A_31, B_32]: (k8_relat_1(A_30, k7_relat_1(A_31, B_32))=k7_relat_1(k8_relat_1(A_30, A_31), B_32) | ~v1_relat_1(A_31))), inference(resolution, [status(thm)], [c_4, c_81])).
% 1.77/1.15  tff(c_10, plain, (k8_relat_1('#skF_1', k7_relat_1('#skF_3', '#skF_2'))!=k7_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.77/1.15  tff(c_99, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_90, c_10])).
% 1.77/1.15  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_99])).
% 1.77/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.15  
% 1.77/1.15  Inference rules
% 1.77/1.15  ----------------------
% 1.77/1.15  #Ref     : 0
% 1.77/1.15  #Sup     : 23
% 1.77/1.15  #Fact    : 0
% 1.77/1.15  #Define  : 0
% 1.77/1.15  #Split   : 0
% 1.77/1.15  #Chain   : 0
% 1.77/1.15  #Close   : 0
% 1.77/1.15  
% 1.77/1.15  Ordering : KBO
% 1.77/1.15  
% 1.77/1.15  Simplification rules
% 1.77/1.15  ----------------------
% 1.77/1.15  #Subsume      : 1
% 1.77/1.15  #Demod        : 5
% 1.77/1.15  #Tautology    : 7
% 1.77/1.15  #SimpNegUnit  : 0
% 1.77/1.15  #BackRed      : 0
% 1.77/1.15  
% 1.77/1.15  #Partial instantiations: 0
% 1.77/1.15  #Strategies tried      : 1
% 1.77/1.16  
% 1.77/1.16  Timing (in seconds)
% 1.77/1.16  ----------------------
% 1.77/1.16  Preprocessing        : 0.27
% 1.77/1.16  Parsing              : 0.14
% 1.77/1.16  CNF conversion       : 0.02
% 1.77/1.16  Main loop            : 0.13
% 1.77/1.16  Inferencing          : 0.06
% 1.77/1.16  Reduction            : 0.03
% 1.77/1.16  Demodulation         : 0.03
% 1.77/1.16  BG Simplification    : 0.01
% 1.77/1.16  Subsumption          : 0.02
% 1.77/1.16  Abstraction          : 0.01
% 1.77/1.16  MUC search           : 0.00
% 1.87/1.16  Cooper               : 0.00
% 1.87/1.16  Total                : 0.43
% 1.87/1.16  Index Insertion      : 0.00
% 1.87/1.16  Index Deletion       : 0.00
% 1.87/1.16  Index Matching       : 0.00
% 1.87/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
