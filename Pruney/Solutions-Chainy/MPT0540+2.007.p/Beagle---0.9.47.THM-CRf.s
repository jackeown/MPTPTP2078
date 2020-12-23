%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:31 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).

tff(c_12,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( v1_relat_1(k8_relat_1(A_2,B_3))
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( k5_relat_1(k6_relat_1(A_8),B_9) = k7_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_15,B_16,C_17] :
      ( k8_relat_1(A_15,k5_relat_1(B_16,C_17)) = k5_relat_1(B_16,k8_relat_1(A_15,C_17))
      | ~ v1_relat_1(C_17)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36,plain,(
    ! [A_8,A_15,B_9] :
      ( k5_relat_1(k6_relat_1(A_8),k8_relat_1(A_15,B_9)) = k8_relat_1(A_15,k7_relat_1(B_9,A_8))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(k6_relat_1(A_8))
      | ~ v1_relat_1(B_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_24])).

tff(c_41,plain,(
    ! [A_18,A_19,B_20] :
      ( k5_relat_1(k6_relat_1(A_18),k8_relat_1(A_19,B_20)) = k8_relat_1(A_19,k7_relat_1(B_20,A_18))
      | ~ v1_relat_1(B_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_81,plain,(
    ! [A_27,B_28,A_29] :
      ( k8_relat_1(A_27,k7_relat_1(B_28,A_29)) = k7_relat_1(k8_relat_1(A_27,B_28),A_29)
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(k8_relat_1(A_27,B_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_41])).

tff(c_90,plain,(
    ! [A_30,B_31,A_32] :
      ( k8_relat_1(A_30,k7_relat_1(B_31,A_32)) = k7_relat_1(k8_relat_1(A_30,B_31),A_32)
      | ~ v1_relat_1(B_31) ) ),
    inference(resolution,[status(thm)],[c_4,c_81])).

tff(c_10,plain,(
    k8_relat_1('#skF_1',k7_relat_1('#skF_3','#skF_2')) != k7_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_105,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_10])).

tff(c_116,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:40:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.28  
% 1.87/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.28  %$ v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.87/1.28  
% 1.87/1.28  %Foreground sorts:
% 1.87/1.28  
% 1.87/1.28  
% 1.87/1.28  %Background operators:
% 1.87/1.28  
% 1.87/1.28  
% 1.87/1.28  %Foreground operators:
% 1.87/1.28  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.87/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.87/1.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.87/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.28  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.28  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.87/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.28  
% 1.87/1.29  tff(f_47, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k8_relat_1(A, C), B) = k8_relat_1(A, k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_relat_1)).
% 1.87/1.29  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 1.87/1.29  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.87/1.29  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.87/1.29  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_relat_1)).
% 1.87/1.29  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.87/1.29  tff(c_4, plain, (![A_2, B_3]: (v1_relat_1(k8_relat_1(A_2, B_3)) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.87/1.29  tff(c_8, plain, (![A_8, B_9]: (k5_relat_1(k6_relat_1(A_8), B_9)=k7_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.87/1.29  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.87/1.29  tff(c_24, plain, (![A_15, B_16, C_17]: (k8_relat_1(A_15, k5_relat_1(B_16, C_17))=k5_relat_1(B_16, k8_relat_1(A_15, C_17)) | ~v1_relat_1(C_17) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.87/1.29  tff(c_36, plain, (![A_8, A_15, B_9]: (k5_relat_1(k6_relat_1(A_8), k8_relat_1(A_15, B_9))=k8_relat_1(A_15, k7_relat_1(B_9, A_8)) | ~v1_relat_1(B_9) | ~v1_relat_1(k6_relat_1(A_8)) | ~v1_relat_1(B_9))), inference(superposition, [status(thm), theory('equality')], [c_8, c_24])).
% 1.87/1.29  tff(c_41, plain, (![A_18, A_19, B_20]: (k5_relat_1(k6_relat_1(A_18), k8_relat_1(A_19, B_20))=k8_relat_1(A_19, k7_relat_1(B_20, A_18)) | ~v1_relat_1(B_20))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 1.87/1.29  tff(c_81, plain, (![A_27, B_28, A_29]: (k8_relat_1(A_27, k7_relat_1(B_28, A_29))=k7_relat_1(k8_relat_1(A_27, B_28), A_29) | ~v1_relat_1(B_28) | ~v1_relat_1(k8_relat_1(A_27, B_28)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_41])).
% 1.87/1.29  tff(c_90, plain, (![A_30, B_31, A_32]: (k8_relat_1(A_30, k7_relat_1(B_31, A_32))=k7_relat_1(k8_relat_1(A_30, B_31), A_32) | ~v1_relat_1(B_31))), inference(resolution, [status(thm)], [c_4, c_81])).
% 1.87/1.29  tff(c_10, plain, (k8_relat_1('#skF_1', k7_relat_1('#skF_3', '#skF_2'))!=k7_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.87/1.29  tff(c_105, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_90, c_10])).
% 1.87/1.29  tff(c_116, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_105])).
% 1.87/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.29  
% 1.87/1.29  Inference rules
% 1.87/1.29  ----------------------
% 1.87/1.29  #Ref     : 0
% 1.87/1.29  #Sup     : 25
% 1.87/1.29  #Fact    : 0
% 1.87/1.29  #Define  : 0
% 1.87/1.29  #Split   : 0
% 1.87/1.29  #Chain   : 0
% 1.87/1.29  #Close   : 0
% 1.87/1.29  
% 1.87/1.29  Ordering : KBO
% 1.87/1.29  
% 1.87/1.29  Simplification rules
% 1.87/1.29  ----------------------
% 1.87/1.29  #Subsume      : 1
% 1.87/1.29  #Demod        : 5
% 1.87/1.29  #Tautology    : 7
% 1.87/1.29  #SimpNegUnit  : 0
% 1.87/1.29  #BackRed      : 0
% 1.87/1.29  
% 1.87/1.29  #Partial instantiations: 0
% 1.87/1.29  #Strategies tried      : 1
% 1.87/1.29  
% 1.87/1.29  Timing (in seconds)
% 1.87/1.29  ----------------------
% 1.87/1.29  Preprocessing        : 0.33
% 1.87/1.29  Parsing              : 0.18
% 1.87/1.29  CNF conversion       : 0.02
% 1.87/1.30  Main loop            : 0.14
% 1.87/1.30  Inferencing          : 0.06
% 1.87/1.30  Reduction            : 0.04
% 1.87/1.30  Demodulation         : 0.03
% 1.87/1.30  BG Simplification    : 0.01
% 1.87/1.30  Subsumption          : 0.02
% 1.87/1.30  Abstraction          : 0.01
% 1.87/1.30  MUC search           : 0.00
% 1.87/1.30  Cooper               : 0.00
% 1.87/1.30  Total                : 0.50
% 1.87/1.30  Index Insertion      : 0.00
% 1.87/1.30  Index Deletion       : 0.00
% 1.87/1.30  Index Matching       : 0.00
% 1.87/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
