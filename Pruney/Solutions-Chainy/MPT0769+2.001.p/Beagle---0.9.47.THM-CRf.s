%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:36 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   32 (  37 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :   40 (  49 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_wellord1 > #nlpp > k6_relat_1 > #skF_2 > #skF_1

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

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k2_wellord1(B,A) = k8_relat_1(A,k7_relat_1(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k7_relat_1(k8_relat_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k8_relat_1(A,k5_relat_1(B,C)) = k5_relat_1(B,k8_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k7_relat_1(k8_relat_1(A_10,B_11),A_10) = k2_wellord1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( v1_relat_1(k8_relat_1(A_2,B_3))
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( k5_relat_1(k6_relat_1(A_8),B_9) = k7_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_35,plain,(
    ! [A_19,B_20,C_21] :
      ( k8_relat_1(A_19,k5_relat_1(B_20,C_21)) = k5_relat_1(B_20,k8_relat_1(A_19,C_21))
      | ~ v1_relat_1(C_21)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_50,plain,(
    ! [A_8,A_19,B_9] :
      ( k5_relat_1(k6_relat_1(A_8),k8_relat_1(A_19,B_9)) = k8_relat_1(A_19,k7_relat_1(B_9,A_8))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(k6_relat_1(A_8))
      | ~ v1_relat_1(B_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_35])).

tff(c_55,plain,(
    ! [A_22,A_23,B_24] :
      ( k5_relat_1(k6_relat_1(A_22),k8_relat_1(A_23,B_24)) = k8_relat_1(A_23,k7_relat_1(B_24,A_22))
      | ~ v1_relat_1(B_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_50])).

tff(c_94,plain,(
    ! [A_28,B_29,A_30] :
      ( k8_relat_1(A_28,k7_relat_1(B_29,A_30)) = k7_relat_1(k8_relat_1(A_28,B_29),A_30)
      | ~ v1_relat_1(k8_relat_1(A_28,B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_8])).

tff(c_100,plain,(
    ! [A_31,B_32,A_33] :
      ( k8_relat_1(A_31,k7_relat_1(B_32,A_33)) = k7_relat_1(k8_relat_1(A_31,B_32),A_33)
      | ~ v1_relat_1(B_32) ) ),
    inference(resolution,[status(thm)],[c_4,c_94])).

tff(c_12,plain,(
    k8_relat_1('#skF_1',k7_relat_1('#skF_2','#skF_1')) != k2_wellord1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_115,plain,
    ( k7_relat_1(k8_relat_1('#skF_1','#skF_2'),'#skF_1') != k2_wellord1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_12])).

tff(c_127,plain,(
    k7_relat_1(k8_relat_1('#skF_1','#skF_2'),'#skF_1') != k2_wellord1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_115])).

tff(c_131,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_127])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:54:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.11  
% 1.66/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.11  %$ v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_wellord1 > #nlpp > k6_relat_1 > #skF_2 > #skF_1
% 1.66/1.11  
% 1.66/1.11  %Foreground sorts:
% 1.66/1.11  
% 1.66/1.11  
% 1.66/1.11  %Background operators:
% 1.66/1.11  
% 1.66/1.11  
% 1.66/1.11  %Foreground operators:
% 1.66/1.11  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.11  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.66/1.11  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.66/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.11  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.11  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.66/1.11  
% 1.66/1.12  tff(f_51, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k8_relat_1(A, k7_relat_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_wellord1)).
% 1.66/1.12  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k7_relat_1(k8_relat_1(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_wellord1)).
% 1.66/1.12  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 1.66/1.12  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.66/1.12  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 1.66/1.12  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k8_relat_1(A, k5_relat_1(B, C)) = k5_relat_1(B, k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_relat_1)).
% 1.66/1.12  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.66/1.12  tff(c_10, plain, (![A_10, B_11]: (k7_relat_1(k8_relat_1(A_10, B_11), A_10)=k2_wellord1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.66/1.12  tff(c_4, plain, (![A_2, B_3]: (v1_relat_1(k8_relat_1(A_2, B_3)) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.66/1.12  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.66/1.12  tff(c_8, plain, (![A_8, B_9]: (k5_relat_1(k6_relat_1(A_8), B_9)=k7_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.66/1.12  tff(c_35, plain, (![A_19, B_20, C_21]: (k8_relat_1(A_19, k5_relat_1(B_20, C_21))=k5_relat_1(B_20, k8_relat_1(A_19, C_21)) | ~v1_relat_1(C_21) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.66/1.12  tff(c_50, plain, (![A_8, A_19, B_9]: (k5_relat_1(k6_relat_1(A_8), k8_relat_1(A_19, B_9))=k8_relat_1(A_19, k7_relat_1(B_9, A_8)) | ~v1_relat_1(B_9) | ~v1_relat_1(k6_relat_1(A_8)) | ~v1_relat_1(B_9))), inference(superposition, [status(thm), theory('equality')], [c_8, c_35])).
% 1.66/1.12  tff(c_55, plain, (![A_22, A_23, B_24]: (k5_relat_1(k6_relat_1(A_22), k8_relat_1(A_23, B_24))=k8_relat_1(A_23, k7_relat_1(B_24, A_22)) | ~v1_relat_1(B_24))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_50])).
% 1.66/1.12  tff(c_94, plain, (![A_28, B_29, A_30]: (k8_relat_1(A_28, k7_relat_1(B_29, A_30))=k7_relat_1(k8_relat_1(A_28, B_29), A_30) | ~v1_relat_1(k8_relat_1(A_28, B_29)) | ~v1_relat_1(B_29))), inference(superposition, [status(thm), theory('equality')], [c_55, c_8])).
% 1.66/1.12  tff(c_100, plain, (![A_31, B_32, A_33]: (k8_relat_1(A_31, k7_relat_1(B_32, A_33))=k7_relat_1(k8_relat_1(A_31, B_32), A_33) | ~v1_relat_1(B_32))), inference(resolution, [status(thm)], [c_4, c_94])).
% 1.66/1.12  tff(c_12, plain, (k8_relat_1('#skF_1', k7_relat_1('#skF_2', '#skF_1'))!=k2_wellord1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.66/1.12  tff(c_115, plain, (k7_relat_1(k8_relat_1('#skF_1', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_100, c_12])).
% 1.66/1.12  tff(c_127, plain, (k7_relat_1(k8_relat_1('#skF_1', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_115])).
% 1.66/1.12  tff(c_131, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10, c_127])).
% 1.66/1.12  tff(c_135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_131])).
% 1.66/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.12  
% 1.66/1.12  Inference rules
% 1.66/1.12  ----------------------
% 1.66/1.12  #Ref     : 0
% 1.66/1.12  #Sup     : 29
% 1.66/1.12  #Fact    : 0
% 1.66/1.12  #Define  : 0
% 1.66/1.12  #Split   : 0
% 1.66/1.12  #Chain   : 0
% 1.66/1.12  #Close   : 0
% 1.66/1.12  
% 1.66/1.12  Ordering : KBO
% 1.66/1.12  
% 1.66/1.12  Simplification rules
% 1.66/1.12  ----------------------
% 1.66/1.12  #Subsume      : 1
% 1.66/1.12  #Demod        : 6
% 1.66/1.12  #Tautology    : 10
% 1.66/1.12  #SimpNegUnit  : 0
% 1.66/1.12  #BackRed      : 0
% 1.66/1.12  
% 1.66/1.12  #Partial instantiations: 0
% 1.66/1.12  #Strategies tried      : 1
% 1.66/1.12  
% 1.66/1.12  Timing (in seconds)
% 1.66/1.12  ----------------------
% 1.66/1.13  Preprocessing        : 0.26
% 1.66/1.13  Parsing              : 0.14
% 1.66/1.13  CNF conversion       : 0.02
% 1.66/1.13  Main loop            : 0.13
% 1.66/1.13  Inferencing          : 0.06
% 1.66/1.13  Reduction            : 0.03
% 1.66/1.13  Demodulation         : 0.03
% 1.66/1.13  BG Simplification    : 0.01
% 1.66/1.13  Subsumption          : 0.02
% 1.66/1.13  Abstraction          : 0.01
% 1.66/1.13  MUC search           : 0.00
% 1.66/1.13  Cooper               : 0.00
% 1.66/1.13  Total                : 0.41
% 1.66/1.13  Index Insertion      : 0.00
% 1.66/1.13  Index Deletion       : 0.00
% 1.66/1.13  Index Matching       : 0.00
% 1.66/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
