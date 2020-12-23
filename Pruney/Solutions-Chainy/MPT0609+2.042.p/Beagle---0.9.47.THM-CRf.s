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
% DateTime   : Thu Dec  3 10:02:36 EST 2020

% Result     : Theorem 4.79s
% Output     : CNFRefutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :   31 (  32 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  44 expanded)
%              Number of equality atoms :   16 (  17 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k7_relat_1 > k6_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,k6_subset_1(k1_relat_1(B),A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( k3_xboole_0(k1_relat_1(B_11),A_10) = k1_relat_1(k7_relat_1(B_11,A_10))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    ! [B_18,A_19] :
      ( k7_relat_1(B_18,k3_xboole_0(k1_relat_1(B_18),A_19)) = k7_relat_1(B_18,A_19)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_53,plain,(
    ! [B_11,A_10] :
      ( k7_relat_1(B_11,k1_relat_1(k7_relat_1(B_11,A_10))) = k7_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_44])).

tff(c_12,plain,(
    ! [A_12] :
      ( k7_relat_1(A_12,k1_relat_1(A_12)) = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_108,plain,(
    ! [C_24,A_25,B_26] :
      ( k6_subset_1(k7_relat_1(C_24,A_25),k7_relat_1(C_24,B_26)) = k7_relat_1(C_24,k6_subset_1(A_25,B_26))
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [A_27,B_28] :
      ( k7_relat_1(A_27,k6_subset_1(k1_relat_1(A_27),B_28)) = k6_subset_1(A_27,k7_relat_1(A_27,B_28))
      | ~ v1_relat_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_108])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k1_relat_1(k7_relat_1(B_7,k6_subset_1(k1_relat_1(B_7),A_6))) = k6_subset_1(k1_relat_1(B_7),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_192,plain,(
    ! [A_31,B_32] :
      ( k1_relat_1(k6_subset_1(A_31,k7_relat_1(A_31,B_32))) = k6_subset_1(k1_relat_1(A_31),B_32)
      | ~ v1_relat_1(A_31)
      | ~ v1_relat_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_6])).

tff(c_2550,plain,(
    ! [B_81,A_82] :
      ( k6_subset_1(k1_relat_1(B_81),k1_relat_1(k7_relat_1(B_81,A_82))) = k1_relat_1(k6_subset_1(B_81,k7_relat_1(B_81,A_82)))
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_192])).

tff(c_14,plain,(
    k6_subset_1(k1_relat_1('#skF_2'),k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2587,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2550,c_14])).

tff(c_2676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2587])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:00:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.79/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.89  
% 4.79/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.90  %$ v1_relat_1 > k7_relat_1 > k6_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.79/1.90  
% 4.79/1.90  %Foreground sorts:
% 4.79/1.90  
% 4.79/1.90  
% 4.79/1.90  %Background operators:
% 4.79/1.90  
% 4.79/1.90  
% 4.79/1.90  %Foreground operators:
% 4.79/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.79/1.90  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.79/1.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.79/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.79/1.90  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 4.79/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.79/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.79/1.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.79/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.79/1.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.79/1.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.79/1.90  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.79/1.90  
% 5.14/1.90  tff(f_52, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t213_relat_1)).
% 5.14/1.90  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 5.14/1.90  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 5.14/1.90  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 5.14/1.90  tff(f_31, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_relat_1)).
% 5.14/1.90  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, k6_subset_1(k1_relat_1(B), A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t191_relat_1)).
% 5.14/1.90  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.14/1.90  tff(c_10, plain, (![B_11, A_10]: (k3_xboole_0(k1_relat_1(B_11), A_10)=k1_relat_1(k7_relat_1(B_11, A_10)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.14/1.90  tff(c_44, plain, (![B_18, A_19]: (k7_relat_1(B_18, k3_xboole_0(k1_relat_1(B_18), A_19))=k7_relat_1(B_18, A_19) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.14/1.90  tff(c_53, plain, (![B_11, A_10]: (k7_relat_1(B_11, k1_relat_1(k7_relat_1(B_11, A_10)))=k7_relat_1(B_11, A_10) | ~v1_relat_1(B_11) | ~v1_relat_1(B_11))), inference(superposition, [status(thm), theory('equality')], [c_10, c_44])).
% 5.14/1.90  tff(c_12, plain, (![A_12]: (k7_relat_1(A_12, k1_relat_1(A_12))=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.14/1.90  tff(c_108, plain, (![C_24, A_25, B_26]: (k6_subset_1(k7_relat_1(C_24, A_25), k7_relat_1(C_24, B_26))=k7_relat_1(C_24, k6_subset_1(A_25, B_26)) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.14/1.90  tff(c_135, plain, (![A_27, B_28]: (k7_relat_1(A_27, k6_subset_1(k1_relat_1(A_27), B_28))=k6_subset_1(A_27, k7_relat_1(A_27, B_28)) | ~v1_relat_1(A_27) | ~v1_relat_1(A_27))), inference(superposition, [status(thm), theory('equality')], [c_12, c_108])).
% 5.14/1.90  tff(c_6, plain, (![B_7, A_6]: (k1_relat_1(k7_relat_1(B_7, k6_subset_1(k1_relat_1(B_7), A_6)))=k6_subset_1(k1_relat_1(B_7), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.14/1.90  tff(c_192, plain, (![A_31, B_32]: (k1_relat_1(k6_subset_1(A_31, k7_relat_1(A_31, B_32)))=k6_subset_1(k1_relat_1(A_31), B_32) | ~v1_relat_1(A_31) | ~v1_relat_1(A_31) | ~v1_relat_1(A_31))), inference(superposition, [status(thm), theory('equality')], [c_135, c_6])).
% 5.14/1.90  tff(c_2550, plain, (![B_81, A_82]: (k6_subset_1(k1_relat_1(B_81), k1_relat_1(k7_relat_1(B_81, A_82)))=k1_relat_1(k6_subset_1(B_81, k7_relat_1(B_81, A_82))) | ~v1_relat_1(B_81) | ~v1_relat_1(B_81) | ~v1_relat_1(B_81) | ~v1_relat_1(B_81) | ~v1_relat_1(B_81))), inference(superposition, [status(thm), theory('equality')], [c_53, c_192])).
% 5.14/1.90  tff(c_14, plain, (k6_subset_1(k1_relat_1('#skF_2'), k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.14/1.90  tff(c_2587, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2550, c_14])).
% 5.14/1.90  tff(c_2676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_2587])).
% 5.14/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.14/1.90  
% 5.14/1.90  Inference rules
% 5.14/1.90  ----------------------
% 5.14/1.90  #Ref     : 0
% 5.14/1.90  #Sup     : 804
% 5.14/1.90  #Fact    : 0
% 5.14/1.90  #Define  : 0
% 5.14/1.90  #Split   : 0
% 5.14/1.90  #Chain   : 0
% 5.14/1.90  #Close   : 0
% 5.14/1.90  
% 5.14/1.90  Ordering : KBO
% 5.14/1.91  
% 5.14/1.91  Simplification rules
% 5.14/1.91  ----------------------
% 5.14/1.91  #Subsume      : 18
% 5.14/1.91  #Demod        : 1
% 5.14/1.91  #Tautology    : 84
% 5.14/1.91  #SimpNegUnit  : 0
% 5.14/1.91  #BackRed      : 0
% 5.14/1.91  
% 5.14/1.91  #Partial instantiations: 0
% 5.14/1.91  #Strategies tried      : 1
% 5.14/1.91  
% 5.14/1.91  Timing (in seconds)
% 5.14/1.91  ----------------------
% 5.14/1.91  Preprocessing        : 0.28
% 5.14/1.91  Parsing              : 0.16
% 5.14/1.91  CNF conversion       : 0.01
% 5.14/1.91  Main loop            : 0.87
% 5.14/1.91  Inferencing          : 0.38
% 5.14/1.91  Reduction            : 0.18
% 5.14/1.91  Demodulation         : 0.12
% 5.14/1.91  BG Simplification    : 0.07
% 5.14/1.91  Subsumption          : 0.19
% 5.14/1.91  Abstraction          : 0.08
% 5.14/1.91  MUC search           : 0.00
% 5.14/1.91  Cooper               : 0.00
% 5.14/1.91  Total                : 1.18
% 5.14/1.91  Index Insertion      : 0.00
% 5.14/1.91  Index Deletion       : 0.00
% 5.14/1.91  Index Matching       : 0.00
% 5.14/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
