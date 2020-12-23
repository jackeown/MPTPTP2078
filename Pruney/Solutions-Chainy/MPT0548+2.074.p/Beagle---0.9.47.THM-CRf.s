%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:45 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   41 (  54 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  53 expanded)
%              Number of equality atoms :   25 (  34 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_43,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_42,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_16,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_29,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_31,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_29])).

tff(c_12,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_43,plain,(
    ! [A_12] :
      ( k7_relat_1(A_12,k1_relat_1(A_12)) = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_52,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_43])).

tff(c_56,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_52])).

tff(c_97,plain,(
    ! [B_16,A_17] :
      ( k2_relat_1(k7_relat_1(B_16,A_17)) = k9_relat_1(B_16,A_17)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_106,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_97])).

tff(c_113,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_12,c_106])).

tff(c_61,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    ! [B_14] : k3_xboole_0(k1_xboole_0,B_14) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_4])).

tff(c_118,plain,(
    ! [B_18,A_19] :
      ( k9_relat_1(B_18,k3_xboole_0(k1_relat_1(B_18),A_19)) = k9_relat_1(B_18,A_19)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_127,plain,(
    ! [A_19] :
      ( k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_19)) = k9_relat_1(k1_xboole_0,A_19)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_118])).

tff(c_131,plain,(
    ! [A_19] : k9_relat_1(k1_xboole_0,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_113,c_71,c_127])).

tff(c_20,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:10:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.17  
% 1.86/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.17  %$ v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.86/1.17  
% 1.86/1.17  %Foreground sorts:
% 1.86/1.17  
% 1.86/1.17  
% 1.86/1.17  %Background operators:
% 1.86/1.17  
% 1.86/1.17  
% 1.86/1.17  %Foreground operators:
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.86/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.86/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.86/1.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.86/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.86/1.17  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.86/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.86/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.86/1.17  
% 1.86/1.18  tff(f_43, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.86/1.18  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.86/1.18  tff(f_42, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.86/1.18  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 1.86/1.18  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.86/1.18  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.86/1.18  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.86/1.18  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_relat_1)).
% 1.86/1.18  tff(f_50, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.86/1.18  tff(c_16, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.86/1.18  tff(c_29, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.18  tff(c_31, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_29])).
% 1.86/1.18  tff(c_12, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.86/1.18  tff(c_14, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.86/1.18  tff(c_43, plain, (![A_12]: (k7_relat_1(A_12, k1_relat_1(A_12))=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.86/1.18  tff(c_52, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_43])).
% 1.86/1.18  tff(c_56, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_31, c_52])).
% 1.86/1.18  tff(c_97, plain, (![B_16, A_17]: (k2_relat_1(k7_relat_1(B_16, A_17))=k9_relat_1(B_16, A_17) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.86/1.18  tff(c_106, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_56, c_97])).
% 1.86/1.18  tff(c_113, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_31, c_12, c_106])).
% 1.86/1.18  tff(c_61, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.86/1.18  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.86/1.18  tff(c_71, plain, (![B_14]: (k3_xboole_0(k1_xboole_0, B_14)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_61, c_4])).
% 1.86/1.18  tff(c_118, plain, (![B_18, A_19]: (k9_relat_1(B_18, k3_xboole_0(k1_relat_1(B_18), A_19))=k9_relat_1(B_18, A_19) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.86/1.18  tff(c_127, plain, (![A_19]: (k9_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_19))=k9_relat_1(k1_xboole_0, A_19) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_118])).
% 1.86/1.18  tff(c_131, plain, (![A_19]: (k9_relat_1(k1_xboole_0, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_31, c_113, c_71, c_127])).
% 1.86/1.18  tff(c_20, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.86/1.18  tff(c_135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_20])).
% 1.86/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.18  
% 1.86/1.18  Inference rules
% 1.86/1.18  ----------------------
% 1.86/1.18  #Ref     : 0
% 1.86/1.18  #Sup     : 32
% 1.86/1.18  #Fact    : 0
% 1.86/1.18  #Define  : 0
% 1.86/1.18  #Split   : 0
% 1.86/1.18  #Chain   : 0
% 1.86/1.18  #Close   : 0
% 1.86/1.18  
% 1.86/1.18  Ordering : KBO
% 1.86/1.18  
% 1.86/1.18  Simplification rules
% 1.86/1.18  ----------------------
% 1.86/1.18  #Subsume      : 0
% 1.86/1.18  #Demod        : 11
% 1.86/1.18  #Tautology    : 25
% 1.86/1.18  #SimpNegUnit  : 0
% 1.86/1.18  #BackRed      : 1
% 1.86/1.18  
% 1.86/1.18  #Partial instantiations: 0
% 1.86/1.18  #Strategies tried      : 1
% 1.86/1.18  
% 1.86/1.18  Timing (in seconds)
% 1.86/1.18  ----------------------
% 1.86/1.18  Preprocessing        : 0.26
% 1.86/1.18  Parsing              : 0.15
% 1.86/1.18  CNF conversion       : 0.02
% 1.86/1.18  Main loop            : 0.12
% 1.86/1.18  Inferencing          : 0.05
% 1.86/1.18  Reduction            : 0.04
% 1.86/1.18  Demodulation         : 0.03
% 1.86/1.18  BG Simplification    : 0.01
% 1.86/1.18  Subsumption          : 0.01
% 1.86/1.18  Abstraction          : 0.01
% 1.86/1.18  MUC search           : 0.00
% 1.86/1.18  Cooper               : 0.00
% 1.86/1.18  Total                : 0.40
% 1.86/1.18  Index Insertion      : 0.00
% 1.86/1.18  Index Deletion       : 0.00
% 1.86/1.18  Index Matching       : 0.00
% 1.86/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
