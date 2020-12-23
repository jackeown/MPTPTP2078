%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:23 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   37 (  42 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  37 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_28,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_30,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_49,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_38,plain,(
    ! [A_13] :
      ( v1_relat_1(A_13)
      | ~ v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_42,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_38])).

tff(c_43,plain,(
    ! [A_14] :
      ( k10_relat_1(A_14,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_47,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_43])).

tff(c_70,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_80,plain,(
    ! [B_20] : k3_xboole_0(k1_xboole_0,B_20) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_6])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_106,plain,(
    ! [B_22,A_23] :
      ( k10_relat_1(B_22,k3_xboole_0(k2_relat_1(B_22),A_23)) = k10_relat_1(B_22,A_23)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_115,plain,(
    ! [A_23] :
      ( k10_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_23)) = k10_relat_1(k1_xboole_0,A_23)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_106])).

tff(c_119,plain,(
    ! [A_23] : k10_relat_1(k1_xboole_0,A_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_47,c_80,c_115])).

tff(c_22,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:09:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.11  
% 1.64/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.11  %$ v1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.64/1.11  
% 1.64/1.11  %Foreground sorts:
% 1.64/1.11  
% 1.64/1.11  
% 1.64/1.11  %Background operators:
% 1.64/1.11  
% 1.64/1.11  
% 1.64/1.11  %Foreground operators:
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.64/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.64/1.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.64/1.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.64/1.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.64/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.11  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.64/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.64/1.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.64/1.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.64/1.11  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.64/1.11  
% 1.64/1.12  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.64/1.12  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.64/1.12  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 1.64/1.12  tff(f_28, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.64/1.12  tff(f_30, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.64/1.12  tff(f_49, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.64/1.12  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 1.64/1.12  tff(f_52, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.64/1.12  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.64/1.12  tff(c_38, plain, (![A_13]: (v1_relat_1(A_13) | ~v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.64/1.12  tff(c_42, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_38])).
% 1.64/1.12  tff(c_43, plain, (![A_14]: (k10_relat_1(A_14, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.64/1.12  tff(c_47, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_43])).
% 1.64/1.12  tff(c_70, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.64/1.12  tff(c_6, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.64/1.12  tff(c_80, plain, (![B_20]: (k3_xboole_0(k1_xboole_0, B_20)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_70, c_6])).
% 1.64/1.12  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.64/1.12  tff(c_106, plain, (![B_22, A_23]: (k10_relat_1(B_22, k3_xboole_0(k2_relat_1(B_22), A_23))=k10_relat_1(B_22, A_23) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.64/1.12  tff(c_115, plain, (![A_23]: (k10_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_23))=k10_relat_1(k1_xboole_0, A_23) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_106])).
% 1.64/1.12  tff(c_119, plain, (![A_23]: (k10_relat_1(k1_xboole_0, A_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_47, c_80, c_115])).
% 1.64/1.12  tff(c_22, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.64/1.12  tff(c_123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_22])).
% 1.64/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.12  
% 1.64/1.12  Inference rules
% 1.64/1.12  ----------------------
% 1.64/1.12  #Ref     : 0
% 1.64/1.12  #Sup     : 26
% 1.64/1.12  #Fact    : 0
% 1.64/1.12  #Define  : 0
% 1.64/1.12  #Split   : 0
% 1.64/1.12  #Chain   : 0
% 1.64/1.12  #Close   : 0
% 1.64/1.12  
% 1.64/1.12  Ordering : KBO
% 1.64/1.12  
% 1.64/1.12  Simplification rules
% 1.64/1.12  ----------------------
% 1.64/1.12  #Subsume      : 0
% 1.64/1.12  #Demod        : 8
% 1.64/1.12  #Tautology    : 21
% 1.64/1.12  #SimpNegUnit  : 0
% 1.64/1.12  #BackRed      : 1
% 1.64/1.12  
% 1.64/1.12  #Partial instantiations: 0
% 1.64/1.12  #Strategies tried      : 1
% 1.64/1.12  
% 1.64/1.12  Timing (in seconds)
% 1.64/1.12  ----------------------
% 1.64/1.12  Preprocessing        : 0.27
% 1.64/1.12  Parsing              : 0.15
% 1.64/1.12  CNF conversion       : 0.01
% 1.64/1.12  Main loop            : 0.10
% 1.64/1.12  Inferencing          : 0.04
% 1.64/1.12  Reduction            : 0.03
% 1.64/1.12  Demodulation         : 0.02
% 1.64/1.12  BG Simplification    : 0.01
% 1.64/1.12  Subsumption          : 0.01
% 1.64/1.12  Abstraction          : 0.01
% 1.64/1.12  MUC search           : 0.00
% 1.64/1.12  Cooper               : 0.00
% 1.64/1.12  Total                : 0.40
% 1.64/1.12  Index Insertion      : 0.00
% 1.64/1.13  Index Deletion       : 0.00
% 1.64/1.13  Index Matching       : 0.00
% 1.64/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
