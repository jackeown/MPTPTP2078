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
% DateTime   : Thu Dec  3 10:00:22 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   48 (  48 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_28,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_29,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_4,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_6,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_54,plain,(
    ! [A_41] :
      ( v1_relat_1(A_41)
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_58,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_33,c_54])).

tff(c_213,plain,(
    ! [B_59,A_60] :
      ( k3_xboole_0(B_59,k2_zfmisc_1(k1_relat_1(B_59),A_60)) = k8_relat_1(A_60,B_59)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_164,plain,(
    ! [A_49,B_50] : k5_xboole_0(A_49,k3_xboole_0(A_49,B_50)) = k4_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [B_42,A_43] : k5_xboole_0(B_42,A_43) = k5_xboole_0(A_43,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_75,plain,(
    ! [A_43] : k5_xboole_0(k1_xboole_0,A_43) = A_43 ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_12])).

tff(c_171,plain,(
    ! [B_50] : k4_xboole_0(k1_xboole_0,B_50) = k3_xboole_0(k1_xboole_0,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_75])).

tff(c_180,plain,(
    ! [B_50] : k3_xboole_0(k1_xboole_0,B_50) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_171])).

tff(c_220,plain,(
    ! [A_60] :
      ( k8_relat_1(A_60,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_180])).

tff(c_233,plain,(
    ! [A_60] : k8_relat_1(A_60,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_220])).

tff(c_32,plain,(
    k8_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:14:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.18  
% 1.92/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.18  %$ v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1
% 1.92/1.18  
% 1.92/1.18  %Foreground sorts:
% 1.92/1.18  
% 1.92/1.18  
% 1.92/1.18  %Background operators:
% 1.92/1.18  
% 1.92/1.18  
% 1.92/1.18  %Foreground operators:
% 1.92/1.18  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.92/1.18  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 1.92/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.92/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.92/1.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.92/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.92/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.92/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.92/1.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.92/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.92/1.18  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.92/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.92/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.92/1.18  
% 1.92/1.19  tff(f_28, axiom, (k1_xboole_0 = o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_xboole_0)).
% 1.92/1.19  tff(f_29, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 1.92/1.19  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.92/1.19  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_relat_1)).
% 1.92/1.19  tff(f_33, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.92/1.19  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.92/1.19  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 1.92/1.19  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.92/1.19  tff(f_60, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_relat_1)).
% 1.92/1.19  tff(c_4, plain, (o_0_0_xboole_0=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.92/1.19  tff(c_6, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.19  tff(c_33, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.92/1.19  tff(c_54, plain, (![A_41]: (v1_relat_1(A_41) | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.92/1.19  tff(c_58, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_33, c_54])).
% 1.92/1.19  tff(c_213, plain, (![B_59, A_60]: (k3_xboole_0(B_59, k2_zfmisc_1(k1_relat_1(B_59), A_60))=k8_relat_1(A_60, B_59) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.92/1.19  tff(c_10, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.19  tff(c_164, plain, (![A_49, B_50]: (k5_xboole_0(A_49, k3_xboole_0(A_49, B_50))=k4_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.19  tff(c_59, plain, (![B_42, A_43]: (k5_xboole_0(B_42, A_43)=k5_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.92/1.19  tff(c_12, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.19  tff(c_75, plain, (![A_43]: (k5_xboole_0(k1_xboole_0, A_43)=A_43)), inference(superposition, [status(thm), theory('equality')], [c_59, c_12])).
% 1.92/1.19  tff(c_171, plain, (![B_50]: (k4_xboole_0(k1_xboole_0, B_50)=k3_xboole_0(k1_xboole_0, B_50))), inference(superposition, [status(thm), theory('equality')], [c_164, c_75])).
% 1.92/1.19  tff(c_180, plain, (![B_50]: (k3_xboole_0(k1_xboole_0, B_50)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_171])).
% 1.92/1.19  tff(c_220, plain, (![A_60]: (k8_relat_1(A_60, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_213, c_180])).
% 1.92/1.19  tff(c_233, plain, (![A_60]: (k8_relat_1(A_60, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_220])).
% 1.92/1.19  tff(c_32, plain, (k8_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.92/1.19  tff(c_239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_233, c_32])).
% 1.92/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.19  
% 1.92/1.19  Inference rules
% 1.92/1.19  ----------------------
% 1.92/1.19  #Ref     : 0
% 1.92/1.19  #Sup     : 47
% 1.92/1.19  #Fact    : 0
% 1.92/1.19  #Define  : 0
% 1.92/1.19  #Split   : 0
% 1.92/1.19  #Chain   : 0
% 1.92/1.19  #Close   : 0
% 1.92/1.19  
% 1.92/1.19  Ordering : KBO
% 1.92/1.19  
% 1.92/1.19  Simplification rules
% 1.92/1.19  ----------------------
% 1.92/1.19  #Subsume      : 0
% 1.92/1.19  #Demod        : 16
% 1.92/1.19  #Tautology    : 41
% 1.92/1.19  #SimpNegUnit  : 0
% 1.92/1.19  #BackRed      : 1
% 1.92/1.19  
% 1.92/1.19  #Partial instantiations: 0
% 1.92/1.19  #Strategies tried      : 1
% 1.92/1.19  
% 1.92/1.19  Timing (in seconds)
% 1.92/1.19  ----------------------
% 1.92/1.19  Preprocessing        : 0.30
% 1.92/1.19  Parsing              : 0.17
% 1.92/1.19  CNF conversion       : 0.02
% 1.92/1.19  Main loop            : 0.13
% 1.92/1.19  Inferencing          : 0.05
% 1.92/1.19  Reduction            : 0.05
% 1.92/1.19  Demodulation         : 0.04
% 1.92/1.19  BG Simplification    : 0.01
% 1.92/1.19  Subsumption          : 0.01
% 1.92/1.19  Abstraction          : 0.01
% 1.92/1.19  MUC search           : 0.00
% 1.92/1.19  Cooper               : 0.00
% 1.92/1.19  Total                : 0.46
% 1.92/1.19  Index Insertion      : 0.00
% 1.92/1.19  Index Deletion       : 0.00
% 1.92/1.19  Index Matching       : 0.00
% 1.92/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
