%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:29 EST 2020

% Result     : Theorem 8.31s
% Output     : CNFRefutation 8.31s
% Verified   : 
% Statistics : Number of formulae       :   41 (  48 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  44 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_59,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_42,plain,(
    ! [A_54] :
      ( k7_relat_1(A_54,k1_relat_1(A_54)) = A_54
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    ! [A_41,B_42] : k6_subset_1(A_41,B_42) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    ! [C_47,A_45,B_46] :
      ( k6_subset_1(k7_relat_1(C_47,A_45),k7_relat_1(C_47,B_46)) = k7_relat_1(C_47,k6_subset_1(A_45,B_46))
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_729,plain,(
    ! [C_134,A_135,B_136] :
      ( k4_xboole_0(k7_relat_1(C_134,A_135),k7_relat_1(C_134,B_136)) = k7_relat_1(C_134,k4_xboole_0(A_135,B_136))
      | ~ v1_relat_1(C_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_34])).

tff(c_2953,plain,(
    ! [A_285,B_286] :
      ( k7_relat_1(A_285,k4_xboole_0(k1_relat_1(A_285),B_286)) = k4_xboole_0(A_285,k7_relat_1(A_285,B_286))
      | ~ v1_relat_1(A_285)
      | ~ v1_relat_1(A_285) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_729])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_548,plain,(
    ! [B_118,A_119] :
      ( k1_relat_1(k7_relat_1(B_118,A_119)) = A_119
      | ~ r1_tarski(A_119,k1_relat_1(B_118))
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_602,plain,(
    ! [B_118,B_9] :
      ( k1_relat_1(k7_relat_1(B_118,k4_xboole_0(k1_relat_1(B_118),B_9))) = k4_xboole_0(k1_relat_1(B_118),B_9)
      | ~ v1_relat_1(B_118) ) ),
    inference(resolution,[status(thm)],[c_12,c_548])).

tff(c_12527,plain,(
    ! [A_556,B_557] :
      ( k1_relat_1(k4_xboole_0(A_556,k7_relat_1(A_556,B_557))) = k4_xboole_0(k1_relat_1(A_556),B_557)
      | ~ v1_relat_1(A_556)
      | ~ v1_relat_1(A_556)
      | ~ v1_relat_1(A_556) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2953,c_602])).

tff(c_44,plain,(
    k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k6_subset_1(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_47,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_44])).

tff(c_12587,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12527,c_47])).

tff(c_12607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12587])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:17:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.31/3.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.31/3.30  
% 8.31/3.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.31/3.31  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 8.31/3.31  
% 8.31/3.31  %Foreground sorts:
% 8.31/3.31  
% 8.31/3.31  
% 8.31/3.31  %Background operators:
% 8.31/3.31  
% 8.31/3.31  
% 8.31/3.31  %Foreground operators:
% 8.31/3.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.31/3.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.31/3.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.31/3.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.31/3.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.31/3.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.31/3.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.31/3.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.31/3.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.31/3.31  tff('#skF_2', type, '#skF_2': $i).
% 8.31/3.31  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 8.31/3.31  tff('#skF_1', type, '#skF_1': $i).
% 8.31/3.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.31/3.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.31/3.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.31/3.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.31/3.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.31/3.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.31/3.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.31/3.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.31/3.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.31/3.31  
% 8.31/3.31  tff(f_88, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 8.31/3.31  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 8.31/3.31  tff(f_59, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 8.31/3.31  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_relat_1)).
% 8.31/3.31  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.31/3.31  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 8.31/3.31  tff(c_46, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.31/3.31  tff(c_42, plain, (![A_54]: (k7_relat_1(A_54, k1_relat_1(A_54))=A_54 | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.31/3.31  tff(c_30, plain, (![A_41, B_42]: (k6_subset_1(A_41, B_42)=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.31/3.31  tff(c_34, plain, (![C_47, A_45, B_46]: (k6_subset_1(k7_relat_1(C_47, A_45), k7_relat_1(C_47, B_46))=k7_relat_1(C_47, k6_subset_1(A_45, B_46)) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.31/3.31  tff(c_729, plain, (![C_134, A_135, B_136]: (k4_xboole_0(k7_relat_1(C_134, A_135), k7_relat_1(C_134, B_136))=k7_relat_1(C_134, k4_xboole_0(A_135, B_136)) | ~v1_relat_1(C_134))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_34])).
% 8.31/3.31  tff(c_2953, plain, (![A_285, B_286]: (k7_relat_1(A_285, k4_xboole_0(k1_relat_1(A_285), B_286))=k4_xboole_0(A_285, k7_relat_1(A_285, B_286)) | ~v1_relat_1(A_285) | ~v1_relat_1(A_285))), inference(superposition, [status(thm), theory('equality')], [c_42, c_729])).
% 8.31/3.31  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.31/3.31  tff(c_548, plain, (![B_118, A_119]: (k1_relat_1(k7_relat_1(B_118, A_119))=A_119 | ~r1_tarski(A_119, k1_relat_1(B_118)) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.31/3.31  tff(c_602, plain, (![B_118, B_9]: (k1_relat_1(k7_relat_1(B_118, k4_xboole_0(k1_relat_1(B_118), B_9)))=k4_xboole_0(k1_relat_1(B_118), B_9) | ~v1_relat_1(B_118))), inference(resolution, [status(thm)], [c_12, c_548])).
% 8.31/3.31  tff(c_12527, plain, (![A_556, B_557]: (k1_relat_1(k4_xboole_0(A_556, k7_relat_1(A_556, B_557)))=k4_xboole_0(k1_relat_1(A_556), B_557) | ~v1_relat_1(A_556) | ~v1_relat_1(A_556) | ~v1_relat_1(A_556))), inference(superposition, [status(thm), theory('equality')], [c_2953, c_602])).
% 8.31/3.31  tff(c_44, plain, (k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k6_subset_1(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.31/3.31  tff(c_47, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_44])).
% 8.31/3.31  tff(c_12587, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12527, c_47])).
% 8.31/3.31  tff(c_12607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_12587])).
% 8.31/3.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.31/3.31  
% 8.31/3.31  Inference rules
% 8.31/3.31  ----------------------
% 8.31/3.31  #Ref     : 0
% 8.31/3.31  #Sup     : 2889
% 8.31/3.31  #Fact    : 0
% 8.31/3.31  #Define  : 0
% 8.31/3.31  #Split   : 0
% 8.31/3.31  #Chain   : 0
% 8.31/3.31  #Close   : 0
% 8.31/3.31  
% 8.31/3.31  Ordering : KBO
% 8.31/3.31  
% 8.31/3.31  Simplification rules
% 8.31/3.31  ----------------------
% 8.31/3.31  #Subsume      : 121
% 8.31/3.31  #Demod        : 511
% 8.31/3.31  #Tautology    : 560
% 8.31/3.31  #SimpNegUnit  : 0
% 8.31/3.31  #BackRed      : 0
% 8.31/3.31  
% 8.31/3.31  #Partial instantiations: 0
% 8.31/3.31  #Strategies tried      : 1
% 8.31/3.31  
% 8.31/3.31  Timing (in seconds)
% 8.31/3.31  ----------------------
% 8.31/3.32  Preprocessing        : 0.33
% 8.31/3.32  Parsing              : 0.18
% 8.31/3.32  CNF conversion       : 0.02
% 8.31/3.32  Main loop            : 2.24
% 8.31/3.32  Inferencing          : 0.51
% 8.31/3.32  Reduction            : 0.86
% 8.31/3.32  Demodulation         : 0.73
% 8.31/3.32  BG Simplification    : 0.08
% 8.31/3.32  Subsumption          : 0.65
% 8.31/3.32  Abstraction          : 0.08
% 8.31/3.32  MUC search           : 0.00
% 8.31/3.32  Cooper               : 0.00
% 8.31/3.32  Total                : 2.59
% 8.31/3.32  Index Insertion      : 0.00
% 8.31/3.32  Index Deletion       : 0.00
% 8.31/3.32  Index Matching       : 0.00
% 8.31/3.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
