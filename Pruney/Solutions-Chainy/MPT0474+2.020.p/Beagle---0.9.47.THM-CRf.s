%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:30 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   45 (  63 expanded)
%              Number of leaves         :   26 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :   40 (  59 expanded)
%              Number of equality atoms :   23 (  39 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_46,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_relat_1)).

tff(f_55,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k6_subset_1(A,B)) = k6_subset_1(k4_relat_1(A),k4_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24,plain,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_12] : k1_setfam_1(k1_tarski(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [A_23,B_24] : k1_setfam_1(k2_tarski(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_69,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = k1_setfam_1(k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_60])).

tff(c_72,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_69])).

tff(c_91,plain,(
    ! [A_28,B_29] : k5_xboole_0(A_28,k3_xboole_0(A_28,B_29)) = k4_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_100,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = k4_xboole_0(A_4,A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_91])).

tff(c_103,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_100])).

tff(c_12,plain,(
    ! [A_10,B_11] : k6_subset_1(A_10,B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_15,B_17] :
      ( k6_subset_1(k4_relat_1(A_15),k4_relat_1(B_17)) = k4_relat_1(k6_subset_1(A_15,B_17))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_120,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(k4_relat_1(A_34),k4_relat_1(B_35)) = k4_relat_1(k4_xboole_0(A_34,B_35))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_22])).

tff(c_127,plain,(
    ! [B_35] :
      ( k4_relat_1(k4_xboole_0(B_35,B_35)) = k1_xboole_0
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_103])).

tff(c_136,plain,(
    ! [B_35] :
      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_127])).

tff(c_141,plain,(
    ! [B_36] :
      ( ~ v1_relat_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_136])).

tff(c_143,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_141])).

tff(c_147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:21:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.21  
% 1.82/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.21  %$ v1_xboole_0 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k4_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1
% 1.82/1.21  
% 1.82/1.21  %Foreground sorts:
% 1.82/1.21  
% 1.82/1.21  
% 1.82/1.21  %Background operators:
% 1.82/1.21  
% 1.82/1.21  
% 1.82/1.21  %Foreground operators:
% 1.82/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.82/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.82/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.82/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.82/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.82/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.82/1.21  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.82/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.82/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.82/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.82/1.21  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.82/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.82/1.21  
% 1.82/1.22  tff(f_46, axiom, (?[A]: (~v1_xboole_0(A) & v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_relat_1)).
% 1.82/1.22  tff(f_55, negated_conjecture, ~(k4_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_relat_1)).
% 1.82/1.22  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.82/1.22  tff(f_39, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 1.82/1.22  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.82/1.22  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.82/1.22  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.82/1.22  tff(f_37, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.82/1.22  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k6_subset_1(A, B)) = k6_subset_1(k4_relat_1(A), k4_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_relat_1)).
% 1.82/1.22  tff(c_18, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.82/1.22  tff(c_24, plain, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.82/1.22  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.82/1.22  tff(c_14, plain, (![A_12]: (k1_setfam_1(k1_tarski(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.82/1.22  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.82/1.22  tff(c_60, plain, (![A_23, B_24]: (k1_setfam_1(k2_tarski(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.82/1.22  tff(c_69, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=k1_setfam_1(k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_60])).
% 1.82/1.22  tff(c_72, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_69])).
% 1.82/1.22  tff(c_91, plain, (![A_28, B_29]: (k5_xboole_0(A_28, k3_xboole_0(A_28, B_29))=k4_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.82/1.22  tff(c_100, plain, (![A_4]: (k5_xboole_0(A_4, A_4)=k4_xboole_0(A_4, A_4))), inference(superposition, [status(thm), theory('equality')], [c_72, c_91])).
% 1.82/1.22  tff(c_103, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_100])).
% 1.82/1.22  tff(c_12, plain, (![A_10, B_11]: (k6_subset_1(A_10, B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.82/1.22  tff(c_22, plain, (![A_15, B_17]: (k6_subset_1(k4_relat_1(A_15), k4_relat_1(B_17))=k4_relat_1(k6_subset_1(A_15, B_17)) | ~v1_relat_1(B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.82/1.22  tff(c_120, plain, (![A_34, B_35]: (k4_xboole_0(k4_relat_1(A_34), k4_relat_1(B_35))=k4_relat_1(k4_xboole_0(A_34, B_35)) | ~v1_relat_1(B_35) | ~v1_relat_1(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_22])).
% 1.82/1.22  tff(c_127, plain, (![B_35]: (k4_relat_1(k4_xboole_0(B_35, B_35))=k1_xboole_0 | ~v1_relat_1(B_35) | ~v1_relat_1(B_35))), inference(superposition, [status(thm), theory('equality')], [c_120, c_103])).
% 1.82/1.22  tff(c_136, plain, (![B_35]: (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_35) | ~v1_relat_1(B_35))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_127])).
% 1.82/1.22  tff(c_141, plain, (![B_36]: (~v1_relat_1(B_36) | ~v1_relat_1(B_36))), inference(negUnitSimplification, [status(thm)], [c_24, c_136])).
% 1.82/1.22  tff(c_143, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_141])).
% 1.82/1.22  tff(c_147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_143])).
% 1.82/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.22  
% 1.82/1.22  Inference rules
% 1.82/1.22  ----------------------
% 1.82/1.22  #Ref     : 0
% 1.82/1.22  #Sup     : 27
% 1.82/1.22  #Fact    : 0
% 1.82/1.22  #Define  : 0
% 1.82/1.22  #Split   : 0
% 1.82/1.22  #Chain   : 0
% 1.82/1.22  #Close   : 0
% 1.82/1.22  
% 1.82/1.22  Ordering : KBO
% 1.82/1.22  
% 1.82/1.22  Simplification rules
% 1.82/1.22  ----------------------
% 1.82/1.22  #Subsume      : 0
% 1.82/1.22  #Demod        : 7
% 1.82/1.22  #Tautology    : 22
% 1.82/1.22  #SimpNegUnit  : 2
% 1.82/1.22  #BackRed      : 0
% 1.82/1.22  
% 1.82/1.22  #Partial instantiations: 0
% 1.82/1.22  #Strategies tried      : 1
% 1.82/1.22  
% 1.82/1.22  Timing (in seconds)
% 1.82/1.22  ----------------------
% 1.82/1.22  Preprocessing        : 0.27
% 1.82/1.22  Parsing              : 0.14
% 1.82/1.22  CNF conversion       : 0.02
% 1.82/1.22  Main loop            : 0.10
% 1.82/1.22  Inferencing          : 0.04
% 1.82/1.22  Reduction            : 0.03
% 1.82/1.23  Demodulation         : 0.03
% 1.82/1.23  BG Simplification    : 0.01
% 1.82/1.23  Subsumption          : 0.01
% 1.82/1.23  Abstraction          : 0.01
% 1.82/1.23  MUC search           : 0.00
% 1.82/1.23  Cooper               : 0.00
% 1.82/1.23  Total                : 0.40
% 1.82/1.23  Index Insertion      : 0.00
% 1.82/1.23  Index Deletion       : 0.00
% 1.82/1.23  Index Matching       : 0.00
% 1.82/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
