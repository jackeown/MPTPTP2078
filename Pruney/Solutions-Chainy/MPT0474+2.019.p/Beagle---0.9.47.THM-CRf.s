%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:30 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   34 (  46 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  47 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k4_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_38,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relat_1)).

tff(f_47,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k6_subset_1(A,B)) = k6_subset_1(k4_relat_1(A),k4_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

tff(c_10,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_43,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_43])).

tff(c_55,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_52])).

tff(c_8,plain,(
    ! [A_6,B_7] : k6_subset_1(A_6,B_7) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_8,B_10] :
      ( k6_subset_1(k4_relat_1(A_8),k4_relat_1(B_10)) = k4_relat_1(k6_subset_1(A_8,B_10))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_63,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(k4_relat_1(A_18),k4_relat_1(B_19)) = k4_relat_1(k4_xboole_0(A_18,B_19))
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_14])).

tff(c_70,plain,(
    ! [B_19] :
      ( k4_relat_1(k4_xboole_0(B_19,B_19)) = k1_xboole_0
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_55])).

tff(c_79,plain,(
    ! [B_19] :
      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_70])).

tff(c_84,plain,(
    ! [B_20] :
      ( ~ v1_relat_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_79])).

tff(c_86,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_84])).

tff(c_90,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:18:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.50/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.15  
% 1.50/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.15  %$ v1_xboole_0 > v1_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k4_relat_1 > k1_xboole_0 > #skF_1
% 1.50/1.15  
% 1.50/1.15  %Foreground sorts:
% 1.50/1.15  
% 1.50/1.15  
% 1.50/1.15  %Background operators:
% 1.50/1.15  
% 1.50/1.15  
% 1.50/1.15  %Foreground operators:
% 1.50/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.50/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.50/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.50/1.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.50/1.15  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.50/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.50/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.50/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.50/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.50/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.50/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.50/1.15  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.50/1.15  
% 1.50/1.16  tff(f_38, axiom, (?[A]: (~v1_xboole_0(A) & v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_relat_1)).
% 1.50/1.16  tff(f_47, negated_conjecture, ~(k4_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_relat_1)).
% 1.50/1.16  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.50/1.16  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.50/1.16  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.50/1.16  tff(f_33, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.50/1.16  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k6_subset_1(A, B)) = k6_subset_1(k4_relat_1(A), k4_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_relat_1)).
% 1.50/1.16  tff(c_10, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.50/1.16  tff(c_16, plain, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.50/1.16  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.50/1.16  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.50/1.16  tff(c_43, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.50/1.16  tff(c_52, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_43])).
% 1.50/1.16  tff(c_55, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_52])).
% 1.50/1.16  tff(c_8, plain, (![A_6, B_7]: (k6_subset_1(A_6, B_7)=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.50/1.16  tff(c_14, plain, (![A_8, B_10]: (k6_subset_1(k4_relat_1(A_8), k4_relat_1(B_10))=k4_relat_1(k6_subset_1(A_8, B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.50/1.16  tff(c_63, plain, (![A_18, B_19]: (k4_xboole_0(k4_relat_1(A_18), k4_relat_1(B_19))=k4_relat_1(k4_xboole_0(A_18, B_19)) | ~v1_relat_1(B_19) | ~v1_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_14])).
% 1.50/1.16  tff(c_70, plain, (![B_19]: (k4_relat_1(k4_xboole_0(B_19, B_19))=k1_xboole_0 | ~v1_relat_1(B_19) | ~v1_relat_1(B_19))), inference(superposition, [status(thm), theory('equality')], [c_63, c_55])).
% 1.50/1.16  tff(c_79, plain, (![B_19]: (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_19) | ~v1_relat_1(B_19))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_70])).
% 1.50/1.16  tff(c_84, plain, (![B_20]: (~v1_relat_1(B_20) | ~v1_relat_1(B_20))), inference(negUnitSimplification, [status(thm)], [c_16, c_79])).
% 1.50/1.16  tff(c_86, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_10, c_84])).
% 1.50/1.16  tff(c_90, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_86])).
% 1.50/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.16  
% 1.50/1.16  Inference rules
% 1.50/1.16  ----------------------
% 1.50/1.16  #Ref     : 0
% 1.50/1.16  #Sup     : 16
% 1.50/1.16  #Fact    : 0
% 1.50/1.16  #Define  : 0
% 1.50/1.16  #Split   : 0
% 1.50/1.16  #Chain   : 0
% 1.50/1.16  #Close   : 0
% 1.50/1.16  
% 1.50/1.16  Ordering : KBO
% 1.50/1.16  
% 1.50/1.16  Simplification rules
% 1.50/1.16  ----------------------
% 1.50/1.16  #Subsume      : 0
% 1.50/1.16  #Demod        : 6
% 1.50/1.17  #Tautology    : 12
% 1.50/1.17  #SimpNegUnit  : 2
% 1.50/1.17  #BackRed      : 0
% 1.50/1.17  
% 1.66/1.17  #Partial instantiations: 0
% 1.66/1.17  #Strategies tried      : 1
% 1.66/1.17  
% 1.66/1.17  Timing (in seconds)
% 1.66/1.17  ----------------------
% 1.66/1.17  Preprocessing        : 0.25
% 1.66/1.17  Parsing              : 0.13
% 1.66/1.17  CNF conversion       : 0.01
% 1.66/1.17  Main loop            : 0.08
% 1.66/1.17  Inferencing          : 0.03
% 1.66/1.17  Reduction            : 0.03
% 1.66/1.17  Demodulation         : 0.02
% 1.66/1.17  BG Simplification    : 0.01
% 1.66/1.17  Subsumption          : 0.01
% 1.66/1.17  Abstraction          : 0.01
% 1.66/1.17  MUC search           : 0.00
% 1.66/1.17  Cooper               : 0.00
% 1.66/1.17  Total                : 0.35
% 1.66/1.17  Index Insertion      : 0.00
% 1.66/1.17  Index Deletion       : 0.00
% 1.66/1.17  Index Matching       : 0.00
% 1.66/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
