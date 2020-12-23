%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:22 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   43 (  52 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   29 (  39 expanded)
%              Number of equality atoms :   22 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_60,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

tff(c_30,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_84,plain,(
    ! [A_48,B_49] : k5_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = k4_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_96,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_84])).

tff(c_99,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_96])).

tff(c_188,plain,(
    ! [C_65,A_66,B_67] : k4_xboole_0(k2_zfmisc_1(C_65,A_66),k2_zfmisc_1(C_65,B_67)) = k2_zfmisc_1(C_65,k4_xboole_0(A_66,B_67)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_216,plain,(
    ! [C_65,A_66] : k2_zfmisc_1(C_65,k4_xboole_0(A_66,A_66)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_188])).

tff(c_226,plain,(
    ! [C_68] : k2_zfmisc_1(C_68,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_216])).

tff(c_28,plain,(
    ! [B_40,A_39] :
      ( k3_xboole_0(B_40,k2_zfmisc_1(k1_relat_1(B_40),A_39)) = k8_relat_1(A_39,B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_247,plain,(
    ! [B_40] :
      ( k8_relat_1(k1_xboole_0,B_40) = k3_xboole_0(B_40,k1_xboole_0)
      | ~ v1_relat_1(B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_28])).

tff(c_272,plain,(
    ! [B_74] :
      ( k8_relat_1(k1_xboole_0,B_74) = k1_xboole_0
      | ~ v1_relat_1(B_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_247])).

tff(c_275,plain,(
    k8_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_272])).

tff(c_279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_275])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.24  
% 2.03/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.24  %$ v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.03/1.24  
% 2.03/1.24  %Foreground sorts:
% 2.03/1.24  
% 2.03/1.24  
% 2.03/1.24  %Background operators:
% 2.03/1.24  
% 2.03/1.24  
% 2.03/1.24  %Foreground operators:
% 2.03/1.24  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.03/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.03/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.03/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.24  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.03/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.03/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.03/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.03/1.24  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.03/1.24  
% 2.08/1.25  tff(f_60, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 2.08/1.25  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.08/1.25  tff(f_33, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.08/1.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.08/1.25  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.08/1.25  tff(f_49, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 2.08/1.25  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_relat_1)).
% 2.08/1.25  tff(c_30, plain, (k8_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.08/1.25  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.08/1.25  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.25  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.25  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.08/1.25  tff(c_84, plain, (![A_48, B_49]: (k5_xboole_0(A_48, k3_xboole_0(A_48, B_49))=k4_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.25  tff(c_96, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_84])).
% 2.08/1.25  tff(c_99, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_96])).
% 2.08/1.25  tff(c_188, plain, (![C_65, A_66, B_67]: (k4_xboole_0(k2_zfmisc_1(C_65, A_66), k2_zfmisc_1(C_65, B_67))=k2_zfmisc_1(C_65, k4_xboole_0(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.08/1.25  tff(c_216, plain, (![C_65, A_66]: (k2_zfmisc_1(C_65, k4_xboole_0(A_66, A_66))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_99, c_188])).
% 2.08/1.25  tff(c_226, plain, (![C_68]: (k2_zfmisc_1(C_68, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_99, c_216])).
% 2.08/1.25  tff(c_28, plain, (![B_40, A_39]: (k3_xboole_0(B_40, k2_zfmisc_1(k1_relat_1(B_40), A_39))=k8_relat_1(A_39, B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.08/1.25  tff(c_247, plain, (![B_40]: (k8_relat_1(k1_xboole_0, B_40)=k3_xboole_0(B_40, k1_xboole_0) | ~v1_relat_1(B_40))), inference(superposition, [status(thm), theory('equality')], [c_226, c_28])).
% 2.08/1.25  tff(c_272, plain, (![B_74]: (k8_relat_1(k1_xboole_0, B_74)=k1_xboole_0 | ~v1_relat_1(B_74))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_247])).
% 2.08/1.25  tff(c_275, plain, (k8_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_272])).
% 2.08/1.25  tff(c_279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_275])).
% 2.08/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.25  
% 2.08/1.25  Inference rules
% 2.08/1.25  ----------------------
% 2.08/1.25  #Ref     : 0
% 2.08/1.25  #Sup     : 57
% 2.08/1.25  #Fact    : 0
% 2.08/1.25  #Define  : 0
% 2.08/1.25  #Split   : 0
% 2.08/1.25  #Chain   : 0
% 2.08/1.25  #Close   : 0
% 2.08/1.25  
% 2.08/1.25  Ordering : KBO
% 2.08/1.25  
% 2.08/1.25  Simplification rules
% 2.08/1.25  ----------------------
% 2.08/1.25  #Subsume      : 0
% 2.08/1.25  #Demod        : 30
% 2.08/1.25  #Tautology    : 46
% 2.08/1.25  #SimpNegUnit  : 1
% 2.08/1.25  #BackRed      : 0
% 2.08/1.25  
% 2.08/1.25  #Partial instantiations: 0
% 2.08/1.25  #Strategies tried      : 1
% 2.08/1.25  
% 2.08/1.25  Timing (in seconds)
% 2.08/1.25  ----------------------
% 2.08/1.26  Preprocessing        : 0.29
% 2.08/1.26  Parsing              : 0.15
% 2.08/1.26  CNF conversion       : 0.02
% 2.08/1.26  Main loop            : 0.15
% 2.08/1.26  Inferencing          : 0.06
% 2.08/1.26  Reduction            : 0.05
% 2.08/1.26  Demodulation         : 0.04
% 2.08/1.26  BG Simplification    : 0.01
% 2.08/1.26  Subsumption          : 0.02
% 2.08/1.26  Abstraction          : 0.01
% 2.08/1.26  MUC search           : 0.00
% 2.08/1.26  Cooper               : 0.00
% 2.08/1.26  Total                : 0.46
% 2.08/1.26  Index Insertion      : 0.00
% 2.08/1.26  Index Deletion       : 0.00
% 2.08/1.26  Index Matching       : 0.00
% 2.08/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
