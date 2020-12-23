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
% DateTime   : Thu Dec  3 09:59:59 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   43 (  45 expanded)
%              Number of leaves         :   29 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  34 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_26,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_45,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_45])).

tff(c_50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_2])).

tff(c_91,plain,(
    ! [A_42] :
      ( v1_relat_1(A_42)
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_95,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_50,c_91])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_22,plain,(
    ! [A_31] : k2_zfmisc_1(A_31,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_134,plain,(
    ! [B_52,A_53] :
      ( k3_xboole_0(B_52,k2_zfmisc_1(A_53,k2_relat_1(B_52))) = k7_relat_1(B_52,A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_147,plain,(
    ! [A_53] :
      ( k3_xboole_0(k1_xboole_0,k2_zfmisc_1(A_53,k1_xboole_0)) = k7_relat_1(k1_xboole_0,A_53)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_134])).

tff(c_151,plain,(
    ! [A_53] : k7_relat_1(k1_xboole_0,A_53) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_4,c_22,c_147])).

tff(c_36,plain,(
    k7_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:21:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.14  
% 1.79/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.14  %$ v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1
% 1.79/1.14  
% 1.79/1.14  %Foreground sorts:
% 1.79/1.14  
% 1.79/1.14  
% 1.79/1.14  %Background operators:
% 1.79/1.14  
% 1.79/1.14  
% 1.79/1.14  %Foreground operators:
% 1.79/1.14  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 1.79/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.79/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.14  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.79/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.79/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.79/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.79/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.79/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.14  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.79/1.14  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.79/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.79/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.79/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.79/1.14  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.79/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.79/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.79/1.14  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.79/1.14  
% 1.79/1.15  tff(f_26, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 1.79/1.15  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.79/1.15  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.79/1.15  tff(f_28, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.79/1.15  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.79/1.15  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.79/1.15  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_relat_1)).
% 1.79/1.15  tff(f_66, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.79/1.15  tff(c_2, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.79/1.15  tff(c_45, plain, (![A_38]: (k1_xboole_0=A_38 | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.79/1.15  tff(c_49, plain, (o_0_0_xboole_0=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_45])).
% 1.79/1.15  tff(c_50, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_49, c_2])).
% 1.79/1.15  tff(c_91, plain, (![A_42]: (v1_relat_1(A_42) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.79/1.15  tff(c_95, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_91])).
% 1.79/1.15  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.79/1.15  tff(c_22, plain, (![A_31]: (k2_zfmisc_1(A_31, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.79/1.15  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.79/1.15  tff(c_134, plain, (![B_52, A_53]: (k3_xboole_0(B_52, k2_zfmisc_1(A_53, k2_relat_1(B_52)))=k7_relat_1(B_52, A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.79/1.15  tff(c_147, plain, (![A_53]: (k3_xboole_0(k1_xboole_0, k2_zfmisc_1(A_53, k1_xboole_0))=k7_relat_1(k1_xboole_0, A_53) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_134])).
% 1.79/1.15  tff(c_151, plain, (![A_53]: (k7_relat_1(k1_xboole_0, A_53)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_95, c_4, c_22, c_147])).
% 1.79/1.15  tff(c_36, plain, (k7_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.79/1.15  tff(c_154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151, c_36])).
% 1.79/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.15  
% 1.79/1.15  Inference rules
% 1.79/1.15  ----------------------
% 1.79/1.15  #Ref     : 0
% 1.79/1.15  #Sup     : 29
% 1.79/1.15  #Fact    : 0
% 1.79/1.15  #Define  : 0
% 1.79/1.15  #Split   : 0
% 1.79/1.15  #Chain   : 0
% 1.79/1.15  #Close   : 0
% 1.79/1.15  
% 1.79/1.15  Ordering : KBO
% 1.79/1.15  
% 1.79/1.15  Simplification rules
% 1.79/1.15  ----------------------
% 1.79/1.15  #Subsume      : 0
% 1.79/1.15  #Demod        : 5
% 1.79/1.15  #Tautology    : 25
% 1.79/1.15  #SimpNegUnit  : 0
% 1.79/1.15  #BackRed      : 2
% 1.79/1.15  
% 1.79/1.15  #Partial instantiations: 0
% 1.79/1.15  #Strategies tried      : 1
% 1.79/1.15  
% 1.79/1.15  Timing (in seconds)
% 1.79/1.15  ----------------------
% 1.79/1.15  Preprocessing        : 0.30
% 1.79/1.15  Parsing              : 0.16
% 1.79/1.15  CNF conversion       : 0.02
% 1.79/1.15  Main loop            : 0.10
% 1.79/1.15  Inferencing          : 0.04
% 1.79/1.15  Reduction            : 0.04
% 1.79/1.15  Demodulation         : 0.03
% 1.79/1.15  BG Simplification    : 0.01
% 1.79/1.15  Subsumption          : 0.01
% 1.79/1.15  Abstraction          : 0.01
% 1.79/1.15  MUC search           : 0.00
% 1.79/1.15  Cooper               : 0.00
% 1.79/1.15  Total                : 0.42
% 1.79/1.15  Index Insertion      : 0.00
% 1.79/1.15  Index Deletion       : 0.00
% 1.79/1.15  Index Matching       : 0.00
% 1.79/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
