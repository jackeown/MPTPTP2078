%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:33 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   39 (  47 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  41 expanded)
%              Number of equality atoms :   21 (  28 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_47,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_35,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_46,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_20,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_35,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_37,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_35])).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_63,plain,(
    ! [A_18] :
      ( k10_relat_1(A_18,k2_relat_1(A_18)) = k1_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_72,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_63])).

tff(c_76,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_18,c_72])).

tff(c_81,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_91,plain,(
    ! [B_20] : k3_xboole_0(k1_xboole_0,B_20) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_4])).

tff(c_117,plain,(
    ! [B_22,A_23] :
      ( k10_relat_1(B_22,k3_xboole_0(k2_relat_1(B_22),A_23)) = k10_relat_1(B_22,A_23)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_126,plain,(
    ! [A_23] :
      ( k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_23)) = k10_relat_1(k1_xboole_0,A_23)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_117])).

tff(c_130,plain,(
    ! [A_23] : k10_relat_1(k1_xboole_0,A_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_76,c_91,c_126])).

tff(c_22,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.20  
% 1.74/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.20  %$ v1_relat_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.74/1.20  
% 1.74/1.20  %Foreground sorts:
% 1.74/1.20  
% 1.74/1.20  
% 1.74/1.20  %Background operators:
% 1.74/1.20  
% 1.74/1.20  
% 1.74/1.20  %Foreground operators:
% 1.74/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.74/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.74/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.74/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.74/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.74/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.20  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.74/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.74/1.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.74/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.74/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.74/1.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.74/1.20  
% 1.74/1.21  tff(f_47, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.74/1.21  tff(f_35, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.74/1.21  tff(f_46, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.74/1.21  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 1.74/1.21  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.74/1.21  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.74/1.21  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 1.74/1.21  tff(f_50, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.74/1.21  tff(c_20, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.74/1.21  tff(c_35, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.74/1.21  tff(c_37, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_35])).
% 1.74/1.21  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.74/1.21  tff(c_16, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.74/1.21  tff(c_63, plain, (![A_18]: (k10_relat_1(A_18, k2_relat_1(A_18))=k1_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.74/1.21  tff(c_72, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_63])).
% 1.74/1.21  tff(c_76, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_37, c_18, c_72])).
% 1.74/1.21  tff(c_81, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.74/1.21  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.74/1.21  tff(c_91, plain, (![B_20]: (k3_xboole_0(k1_xboole_0, B_20)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_81, c_4])).
% 1.74/1.21  tff(c_117, plain, (![B_22, A_23]: (k10_relat_1(B_22, k3_xboole_0(k2_relat_1(B_22), A_23))=k10_relat_1(B_22, A_23) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.74/1.21  tff(c_126, plain, (![A_23]: (k10_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_23))=k10_relat_1(k1_xboole_0, A_23) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_117])).
% 1.74/1.21  tff(c_130, plain, (![A_23]: (k10_relat_1(k1_xboole_0, A_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_37, c_76, c_91, c_126])).
% 1.74/1.21  tff(c_22, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.74/1.21  tff(c_134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_22])).
% 1.74/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.21  
% 1.74/1.21  Inference rules
% 1.74/1.21  ----------------------
% 1.74/1.21  #Ref     : 0
% 1.74/1.21  #Sup     : 30
% 1.74/1.21  #Fact    : 0
% 1.74/1.21  #Define  : 0
% 1.74/1.21  #Split   : 0
% 1.74/1.21  #Chain   : 0
% 1.74/1.21  #Close   : 0
% 1.74/1.21  
% 1.74/1.21  Ordering : KBO
% 1.74/1.21  
% 1.74/1.21  Simplification rules
% 1.74/1.21  ----------------------
% 1.74/1.21  #Subsume      : 0
% 1.74/1.21  #Demod        : 10
% 1.74/1.21  #Tautology    : 25
% 1.74/1.21  #SimpNegUnit  : 0
% 1.74/1.21  #BackRed      : 1
% 1.74/1.21  
% 1.74/1.21  #Partial instantiations: 0
% 1.74/1.21  #Strategies tried      : 1
% 1.74/1.21  
% 1.74/1.21  Timing (in seconds)
% 1.74/1.21  ----------------------
% 1.74/1.21  Preprocessing        : 0.29
% 1.74/1.21  Parsing              : 0.16
% 1.74/1.21  CNF conversion       : 0.01
% 1.74/1.21  Main loop            : 0.10
% 1.74/1.21  Inferencing          : 0.05
% 1.74/1.21  Reduction            : 0.03
% 1.74/1.21  Demodulation         : 0.02
% 1.74/1.21  BG Simplification    : 0.01
% 1.74/1.21  Subsumption          : 0.01
% 1.74/1.21  Abstraction          : 0.01
% 1.74/1.21  MUC search           : 0.00
% 1.74/1.21  Cooper               : 0.00
% 1.74/1.21  Total                : 0.42
% 1.74/1.21  Index Insertion      : 0.00
% 1.74/1.21  Index Deletion       : 0.00
% 1.74/1.21  Index Matching       : 0.00
% 1.74/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
