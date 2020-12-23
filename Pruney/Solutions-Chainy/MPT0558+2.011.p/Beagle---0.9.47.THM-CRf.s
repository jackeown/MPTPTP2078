%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:09 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   34 (  39 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 (  80 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_13] :
      ( k7_relat_1(A_13,k1_relat_1(A_13)) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_27,plain,(
    ! [B_18,A_19] :
      ( k2_relat_1(k7_relat_1(B_18,A_19)) = k9_relat_1(B_18,A_19)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,(
    ! [A_13] :
      ( k9_relat_1(A_13,k1_relat_1(A_13)) = k2_relat_1(A_13)
      | ~ v1_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_27])).

tff(c_48,plain,(
    ! [B_21,C_22,A_23] :
      ( k7_relat_1(k5_relat_1(B_21,C_22),A_23) = k5_relat_1(k7_relat_1(B_21,A_23),C_22)
      | ~ v1_relat_1(C_22)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [B_8,A_7] :
      ( k2_relat_1(k7_relat_1(B_8,A_7)) = k9_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_113,plain,(
    ! [B_29,A_30,C_31] :
      ( k2_relat_1(k5_relat_1(k7_relat_1(B_29,A_30),C_31)) = k9_relat_1(k5_relat_1(B_29,C_31),A_30)
      | ~ v1_relat_1(k5_relat_1(B_29,C_31))
      | ~ v1_relat_1(C_31)
      | ~ v1_relat_1(B_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_6])).

tff(c_131,plain,(
    ! [A_32,C_33] :
      ( k9_relat_1(k5_relat_1(A_32,C_33),k1_relat_1(A_32)) = k2_relat_1(k5_relat_1(A_32,C_33))
      | ~ v1_relat_1(k5_relat_1(A_32,C_33))
      | ~ v1_relat_1(C_33)
      | ~ v1_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_113])).

tff(c_8,plain,(
    ! [B_10,C_12,A_9] :
      ( k9_relat_1(k5_relat_1(B_10,C_12),A_9) = k9_relat_1(C_12,k9_relat_1(B_10,A_9))
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_192,plain,(
    ! [C_40,A_41] :
      ( k9_relat_1(C_40,k9_relat_1(A_41,k1_relat_1(A_41))) = k2_relat_1(k5_relat_1(A_41,C_40))
      | ~ v1_relat_1(C_40)
      | ~ v1_relat_1(A_41)
      | ~ v1_relat_1(k5_relat_1(A_41,C_40))
      | ~ v1_relat_1(C_40)
      | ~ v1_relat_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_8])).

tff(c_216,plain,(
    ! [C_42,A_43] :
      ( k9_relat_1(C_42,k2_relat_1(A_43)) = k2_relat_1(k5_relat_1(A_43,C_42))
      | ~ v1_relat_1(C_42)
      | ~ v1_relat_1(A_43)
      | ~ v1_relat_1(k5_relat_1(A_43,C_42))
      | ~ v1_relat_1(C_42)
      | ~ v1_relat_1(A_43)
      | ~ v1_relat_1(A_43)
      | ~ v1_relat_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_192])).

tff(c_224,plain,(
    ! [B_44,A_45] :
      ( k9_relat_1(B_44,k2_relat_1(A_45)) = k2_relat_1(k5_relat_1(A_45,B_44))
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_2,c_216])).

tff(c_12,plain,(
    k9_relat_1('#skF_2',k2_relat_1('#skF_1')) != k2_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_234,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_12])).

tff(c_255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:03:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.30  
% 2.00/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.30  %$ v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.00/1.30  
% 2.00/1.30  %Foreground sorts:
% 2.00/1.30  
% 2.00/1.30  
% 2.00/1.30  %Background operators:
% 2.00/1.30  
% 2.00/1.30  
% 2.00/1.30  %Foreground operators:
% 2.00/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.00/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.00/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.00/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.00/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.30  
% 2.00/1.31  tff(f_61, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.00/1.31  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.00/1.31  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.00/1.31  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.00/1.31  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 2.00/1.31  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_relat_1)).
% 2.00/1.31  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.00/1.31  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.00/1.31  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.31  tff(c_10, plain, (![A_13]: (k7_relat_1(A_13, k1_relat_1(A_13))=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.00/1.31  tff(c_27, plain, (![B_18, A_19]: (k2_relat_1(k7_relat_1(B_18, A_19))=k9_relat_1(B_18, A_19) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.00/1.31  tff(c_36, plain, (![A_13]: (k9_relat_1(A_13, k1_relat_1(A_13))=k2_relat_1(A_13) | ~v1_relat_1(A_13) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_10, c_27])).
% 2.00/1.31  tff(c_48, plain, (![B_21, C_22, A_23]: (k7_relat_1(k5_relat_1(B_21, C_22), A_23)=k5_relat_1(k7_relat_1(B_21, A_23), C_22) | ~v1_relat_1(C_22) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.00/1.31  tff(c_6, plain, (![B_8, A_7]: (k2_relat_1(k7_relat_1(B_8, A_7))=k9_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.00/1.31  tff(c_113, plain, (![B_29, A_30, C_31]: (k2_relat_1(k5_relat_1(k7_relat_1(B_29, A_30), C_31))=k9_relat_1(k5_relat_1(B_29, C_31), A_30) | ~v1_relat_1(k5_relat_1(B_29, C_31)) | ~v1_relat_1(C_31) | ~v1_relat_1(B_29))), inference(superposition, [status(thm), theory('equality')], [c_48, c_6])).
% 2.00/1.31  tff(c_131, plain, (![A_32, C_33]: (k9_relat_1(k5_relat_1(A_32, C_33), k1_relat_1(A_32))=k2_relat_1(k5_relat_1(A_32, C_33)) | ~v1_relat_1(k5_relat_1(A_32, C_33)) | ~v1_relat_1(C_33) | ~v1_relat_1(A_32) | ~v1_relat_1(A_32))), inference(superposition, [status(thm), theory('equality')], [c_10, c_113])).
% 2.00/1.31  tff(c_8, plain, (![B_10, C_12, A_9]: (k9_relat_1(k5_relat_1(B_10, C_12), A_9)=k9_relat_1(C_12, k9_relat_1(B_10, A_9)) | ~v1_relat_1(C_12) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.00/1.31  tff(c_192, plain, (![C_40, A_41]: (k9_relat_1(C_40, k9_relat_1(A_41, k1_relat_1(A_41)))=k2_relat_1(k5_relat_1(A_41, C_40)) | ~v1_relat_1(C_40) | ~v1_relat_1(A_41) | ~v1_relat_1(k5_relat_1(A_41, C_40)) | ~v1_relat_1(C_40) | ~v1_relat_1(A_41) | ~v1_relat_1(A_41))), inference(superposition, [status(thm), theory('equality')], [c_131, c_8])).
% 2.00/1.31  tff(c_216, plain, (![C_42, A_43]: (k9_relat_1(C_42, k2_relat_1(A_43))=k2_relat_1(k5_relat_1(A_43, C_42)) | ~v1_relat_1(C_42) | ~v1_relat_1(A_43) | ~v1_relat_1(k5_relat_1(A_43, C_42)) | ~v1_relat_1(C_42) | ~v1_relat_1(A_43) | ~v1_relat_1(A_43) | ~v1_relat_1(A_43) | ~v1_relat_1(A_43))), inference(superposition, [status(thm), theory('equality')], [c_36, c_192])).
% 2.00/1.31  tff(c_224, plain, (![B_44, A_45]: (k9_relat_1(B_44, k2_relat_1(A_45))=k2_relat_1(k5_relat_1(A_45, B_44)) | ~v1_relat_1(B_44) | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_2, c_216])).
% 2.00/1.31  tff(c_12, plain, (k9_relat_1('#skF_2', k2_relat_1('#skF_1'))!=k2_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.00/1.31  tff(c_234, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_224, c_12])).
% 2.00/1.31  tff(c_255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_234])).
% 2.00/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.31  
% 2.00/1.31  Inference rules
% 2.00/1.31  ----------------------
% 2.00/1.31  #Ref     : 0
% 2.00/1.31  #Sup     : 61
% 2.00/1.31  #Fact    : 0
% 2.00/1.31  #Define  : 0
% 2.00/1.31  #Split   : 0
% 2.00/1.31  #Chain   : 0
% 2.00/1.31  #Close   : 0
% 2.00/1.31  
% 2.00/1.31  Ordering : KBO
% 2.00/1.31  
% 2.00/1.31  Simplification rules
% 2.00/1.31  ----------------------
% 2.00/1.31  #Subsume      : 7
% 2.00/1.31  #Demod        : 2
% 2.00/1.31  #Tautology    : 23
% 2.00/1.31  #SimpNegUnit  : 0
% 2.00/1.31  #BackRed      : 0
% 2.00/1.31  
% 2.00/1.31  #Partial instantiations: 0
% 2.00/1.31  #Strategies tried      : 1
% 2.00/1.31  
% 2.00/1.31  Timing (in seconds)
% 2.00/1.31  ----------------------
% 2.00/1.31  Preprocessing        : 0.28
% 2.00/1.31  Parsing              : 0.14
% 2.00/1.31  CNF conversion       : 0.02
% 2.00/1.31  Main loop            : 0.25
% 2.00/1.31  Inferencing          : 0.12
% 2.00/1.31  Reduction            : 0.06
% 2.00/1.31  Demodulation         : 0.05
% 2.00/1.31  BG Simplification    : 0.02
% 2.00/1.31  Subsumption          : 0.05
% 2.00/1.31  Abstraction          : 0.02
% 2.00/1.31  MUC search           : 0.00
% 2.00/1.31  Cooper               : 0.00
% 2.00/1.31  Total                : 0.56
% 2.00/1.31  Index Insertion      : 0.00
% 2.00/1.31  Index Deletion       : 0.00
% 2.00/1.31  Index Matching       : 0.00
% 2.00/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
