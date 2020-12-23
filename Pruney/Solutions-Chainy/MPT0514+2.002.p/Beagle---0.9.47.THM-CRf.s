%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:06 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   28 (  32 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   44 (  54 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_43,axiom,(
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

tff(c_8,plain,(
    ! [A_11,B_12] :
      ( k5_relat_1(k6_relat_1(A_11),B_12) = k7_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_32,plain,(
    ! [A_21,B_22,C_23] :
      ( k5_relat_1(k5_relat_1(A_21,B_22),C_23) = k5_relat_1(A_21,k5_relat_1(B_22,C_23))
      | ~ v1_relat_1(C_23)
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    ! [A_11,B_12,C_23] :
      ( k5_relat_1(k6_relat_1(A_11),k5_relat_1(B_12,C_23)) = k5_relat_1(k7_relat_1(B_12,A_11),C_23)
      | ~ v1_relat_1(C_23)
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(k6_relat_1(A_11))
      | ~ v1_relat_1(B_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_32])).

tff(c_55,plain,(
    ! [A_24,B_25,C_26] :
      ( k5_relat_1(k6_relat_1(A_24),k5_relat_1(B_25,C_26)) = k5_relat_1(k7_relat_1(B_25,A_24),C_26)
      | ~ v1_relat_1(C_26)
      | ~ v1_relat_1(B_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_50])).

tff(c_280,plain,(
    ! [B_55,C_56,A_57] :
      ( k7_relat_1(k5_relat_1(B_55,C_56),A_57) = k5_relat_1(k7_relat_1(B_55,A_57),C_56)
      | ~ v1_relat_1(C_56)
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(k5_relat_1(B_55,C_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_55])).

tff(c_325,plain,(
    ! [A_58,B_59,A_60] :
      ( k7_relat_1(k5_relat_1(A_58,B_59),A_60) = k5_relat_1(k7_relat_1(A_58,A_60),B_59)
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(resolution,[status(thm)],[c_2,c_280])).

tff(c_10,plain,(
    k7_relat_1(k5_relat_1('#skF_2','#skF_3'),'#skF_1') != k5_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_352,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_10])).

tff(c_375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_352])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.35  
% 2.22/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.35  %$ v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.40/1.35  
% 2.40/1.35  %Foreground sorts:
% 2.40/1.35  
% 2.40/1.35  
% 2.40/1.35  %Background operators:
% 2.40/1.35  
% 2.40/1.35  
% 2.40/1.35  %Foreground operators:
% 2.40/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.40/1.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.40/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.40/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.40/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.40/1.35  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.40/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.36  
% 2.40/1.36  tff(f_55, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 2.40/1.36  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.40/1.36  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.40/1.36  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.40/1.36  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 2.40/1.36  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.40/1.36  tff(c_12, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.40/1.36  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.40/1.36  tff(c_8, plain, (![A_11, B_12]: (k5_relat_1(k6_relat_1(A_11), B_12)=k7_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.40/1.36  tff(c_4, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.40/1.36  tff(c_32, plain, (![A_21, B_22, C_23]: (k5_relat_1(k5_relat_1(A_21, B_22), C_23)=k5_relat_1(A_21, k5_relat_1(B_22, C_23)) | ~v1_relat_1(C_23) | ~v1_relat_1(B_22) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.40/1.36  tff(c_50, plain, (![A_11, B_12, C_23]: (k5_relat_1(k6_relat_1(A_11), k5_relat_1(B_12, C_23))=k5_relat_1(k7_relat_1(B_12, A_11), C_23) | ~v1_relat_1(C_23) | ~v1_relat_1(B_12) | ~v1_relat_1(k6_relat_1(A_11)) | ~v1_relat_1(B_12))), inference(superposition, [status(thm), theory('equality')], [c_8, c_32])).
% 2.40/1.36  tff(c_55, plain, (![A_24, B_25, C_26]: (k5_relat_1(k6_relat_1(A_24), k5_relat_1(B_25, C_26))=k5_relat_1(k7_relat_1(B_25, A_24), C_26) | ~v1_relat_1(C_26) | ~v1_relat_1(B_25))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_50])).
% 2.40/1.36  tff(c_280, plain, (![B_55, C_56, A_57]: (k7_relat_1(k5_relat_1(B_55, C_56), A_57)=k5_relat_1(k7_relat_1(B_55, A_57), C_56) | ~v1_relat_1(C_56) | ~v1_relat_1(B_55) | ~v1_relat_1(k5_relat_1(B_55, C_56)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_55])).
% 2.40/1.36  tff(c_325, plain, (![A_58, B_59, A_60]: (k7_relat_1(k5_relat_1(A_58, B_59), A_60)=k5_relat_1(k7_relat_1(A_58, A_60), B_59) | ~v1_relat_1(B_59) | ~v1_relat_1(A_58))), inference(resolution, [status(thm)], [c_2, c_280])).
% 2.40/1.36  tff(c_10, plain, (k7_relat_1(k5_relat_1('#skF_2', '#skF_3'), '#skF_1')!=k5_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.40/1.36  tff(c_352, plain, (~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_325, c_10])).
% 2.40/1.36  tff(c_375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_12, c_352])).
% 2.40/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.36  
% 2.40/1.36  Inference rules
% 2.40/1.36  ----------------------
% 2.40/1.36  #Ref     : 0
% 2.40/1.36  #Sup     : 90
% 2.40/1.36  #Fact    : 0
% 2.40/1.36  #Define  : 0
% 2.40/1.36  #Split   : 0
% 2.40/1.36  #Chain   : 0
% 2.40/1.36  #Close   : 0
% 2.40/1.36  
% 2.40/1.36  Ordering : KBO
% 2.40/1.36  
% 2.40/1.36  Simplification rules
% 2.40/1.36  ----------------------
% 2.40/1.36  #Subsume      : 7
% 2.40/1.36  #Demod        : 25
% 2.40/1.36  #Tautology    : 11
% 2.40/1.36  #SimpNegUnit  : 0
% 2.40/1.36  #BackRed      : 0
% 2.40/1.36  
% 2.40/1.36  #Partial instantiations: 0
% 2.40/1.36  #Strategies tried      : 1
% 2.40/1.36  
% 2.40/1.36  Timing (in seconds)
% 2.40/1.36  ----------------------
% 2.40/1.37  Preprocessing        : 0.30
% 2.40/1.37  Parsing              : 0.16
% 2.40/1.37  CNF conversion       : 0.02
% 2.40/1.37  Main loop            : 0.27
% 2.40/1.37  Inferencing          : 0.11
% 2.40/1.37  Reduction            : 0.07
% 2.40/1.37  Demodulation         : 0.06
% 2.40/1.37  BG Simplification    : 0.02
% 2.40/1.37  Subsumption          : 0.05
% 2.40/1.37  Abstraction          : 0.02
% 2.40/1.37  MUC search           : 0.00
% 2.40/1.37  Cooper               : 0.00
% 2.40/1.37  Total                : 0.59
% 2.40/1.37  Index Insertion      : 0.00
% 2.40/1.37  Index Deletion       : 0.00
% 2.40/1.37  Index Matching       : 0.00
% 2.40/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
