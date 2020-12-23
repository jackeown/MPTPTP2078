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
% DateTime   : Thu Dec  3 10:00:30 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  20 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_36,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_39,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_10,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_17,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_19,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_17])).

tff(c_63,plain,(
    ! [B_12,A_13] :
      ( k3_xboole_0(B_12,k2_zfmisc_1(k1_relat_1(B_12),A_13)) = k8_relat_1(A_13,B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_27,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [B_10] : k3_xboole_0(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_4])).

tff(c_70,plain,(
    ! [A_13] :
      ( k8_relat_1(A_13,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_37])).

tff(c_80,plain,(
    ! [A_13] : k8_relat_1(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_19,c_70])).

tff(c_12,plain,(
    k8_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:05:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.09  
% 1.61/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.09  %$ v1_relat_1 > k8_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.61/1.09  
% 1.61/1.09  %Foreground sorts:
% 1.61/1.09  
% 1.61/1.09  
% 1.61/1.09  %Background operators:
% 1.61/1.09  
% 1.61/1.09  
% 1.61/1.09  %Foreground operators:
% 1.61/1.09  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.61/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.61/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.61/1.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.61/1.09  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.61/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.61/1.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.61/1.09  
% 1.61/1.10  tff(f_36, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.61/1.10  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.61/1.10  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_relat_1)).
% 1.61/1.10  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.61/1.10  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.61/1.10  tff(f_39, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 1.61/1.10  tff(c_10, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.61/1.10  tff(c_17, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.61/1.10  tff(c_19, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_17])).
% 1.61/1.10  tff(c_63, plain, (![B_12, A_13]: (k3_xboole_0(B_12, k2_zfmisc_1(k1_relat_1(B_12), A_13))=k8_relat_1(A_13, B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.61/1.10  tff(c_27, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.61/1.10  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.61/1.10  tff(c_37, plain, (![B_10]: (k3_xboole_0(k1_xboole_0, B_10)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_27, c_4])).
% 1.61/1.10  tff(c_70, plain, (![A_13]: (k8_relat_1(A_13, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_63, c_37])).
% 1.61/1.10  tff(c_80, plain, (![A_13]: (k8_relat_1(A_13, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_19, c_70])).
% 1.61/1.10  tff(c_12, plain, (k8_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.61/1.10  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_12])).
% 1.61/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.10  
% 1.61/1.10  Inference rules
% 1.61/1.10  ----------------------
% 1.61/1.10  #Ref     : 0
% 1.61/1.10  #Sup     : 18
% 1.61/1.10  #Fact    : 0
% 1.61/1.10  #Define  : 0
% 1.61/1.10  #Split   : 0
% 1.61/1.10  #Chain   : 0
% 1.61/1.10  #Close   : 0
% 1.61/1.10  
% 1.61/1.10  Ordering : KBO
% 1.61/1.10  
% 1.61/1.10  Simplification rules
% 1.61/1.10  ----------------------
% 1.61/1.10  #Subsume      : 0
% 1.61/1.10  #Demod        : 6
% 1.61/1.10  #Tautology    : 12
% 1.61/1.10  #SimpNegUnit  : 0
% 1.61/1.10  #BackRed      : 1
% 1.61/1.10  
% 1.61/1.10  #Partial instantiations: 0
% 1.61/1.10  #Strategies tried      : 1
% 1.61/1.10  
% 1.61/1.10  Timing (in seconds)
% 1.61/1.10  ----------------------
% 1.61/1.10  Preprocessing        : 0.25
% 1.61/1.11  Parsing              : 0.14
% 1.61/1.11  CNF conversion       : 0.01
% 1.61/1.11  Main loop            : 0.09
% 1.61/1.11  Inferencing          : 0.04
% 1.61/1.11  Reduction            : 0.03
% 1.61/1.11  Demodulation         : 0.02
% 1.61/1.11  BG Simplification    : 0.01
% 1.61/1.11  Subsumption          : 0.01
% 1.61/1.11  Abstraction          : 0.00
% 1.61/1.11  MUC search           : 0.00
% 1.61/1.11  Cooper               : 0.00
% 1.61/1.11  Total                : 0.36
% 1.61/1.11  Index Insertion      : 0.00
% 1.61/1.11  Index Deletion       : 0.00
% 1.61/1.11  Index Matching       : 0.00
% 1.61/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
