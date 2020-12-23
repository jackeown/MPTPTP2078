%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:29 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   22 (  22 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_38,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_10,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_17,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_19,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_17])).

tff(c_33,plain,(
    ! [B_12,A_13] :
      ( k3_xboole_0(B_12,k2_zfmisc_1(k1_relat_1(B_12),A_13)) = k8_relat_1(A_13,B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_21,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_25,plain,(
    ! [A_3] : k3_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_21])).

tff(c_40,plain,(
    ! [A_13] :
      ( k8_relat_1(A_13,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_25])).

tff(c_50,plain,(
    ! [A_13] : k8_relat_1(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_19,c_40])).

tff(c_12,plain,(
    k8_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_56,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:14:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.14  
% 1.58/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.14  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.58/1.14  
% 1.58/1.14  %Foreground sorts:
% 1.58/1.14  
% 1.58/1.14  
% 1.58/1.14  %Background operators:
% 1.58/1.14  
% 1.58/1.14  
% 1.58/1.14  %Foreground operators:
% 1.58/1.14  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.58/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.58/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.58/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.58/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.58/1.14  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.58/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.58/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.58/1.14  
% 1.58/1.15  tff(f_38, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.58/1.15  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.58/1.15  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_relat_1)).
% 1.58/1.15  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.58/1.15  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.58/1.15  tff(f_41, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 1.58/1.15  tff(c_10, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.58/1.15  tff(c_17, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.58/1.15  tff(c_19, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_17])).
% 1.58/1.15  tff(c_33, plain, (![B_12, A_13]: (k3_xboole_0(B_12, k2_zfmisc_1(k1_relat_1(B_12), A_13))=k8_relat_1(A_13, B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.58/1.15  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.58/1.15  tff(c_21, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.58/1.15  tff(c_25, plain, (![A_3]: (k3_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_21])).
% 1.58/1.15  tff(c_40, plain, (![A_13]: (k8_relat_1(A_13, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_33, c_25])).
% 1.58/1.15  tff(c_50, plain, (![A_13]: (k8_relat_1(A_13, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_19, c_40])).
% 1.58/1.15  tff(c_12, plain, (k8_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.58/1.15  tff(c_56, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_12])).
% 1.58/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.15  
% 1.58/1.15  Inference rules
% 1.58/1.15  ----------------------
% 1.58/1.15  #Ref     : 0
% 1.58/1.15  #Sup     : 10
% 1.58/1.15  #Fact    : 0
% 1.58/1.15  #Define  : 0
% 1.58/1.15  #Split   : 0
% 1.58/1.15  #Chain   : 0
% 1.58/1.15  #Close   : 0
% 1.58/1.15  
% 1.58/1.15  Ordering : KBO
% 1.58/1.15  
% 1.58/1.15  Simplification rules
% 1.58/1.15  ----------------------
% 1.58/1.15  #Subsume      : 0
% 1.58/1.15  #Demod        : 3
% 1.58/1.15  #Tautology    : 6
% 1.58/1.15  #SimpNegUnit  : 0
% 1.58/1.15  #BackRed      : 1
% 1.58/1.15  
% 1.58/1.15  #Partial instantiations: 0
% 1.58/1.15  #Strategies tried      : 1
% 1.58/1.15  
% 1.58/1.15  Timing (in seconds)
% 1.58/1.15  ----------------------
% 1.58/1.16  Preprocessing        : 0.26
% 1.58/1.16  Parsing              : 0.15
% 1.58/1.16  CNF conversion       : 0.02
% 1.58/1.16  Main loop            : 0.08
% 1.58/1.16  Inferencing          : 0.04
% 1.58/1.16  Reduction            : 0.02
% 1.58/1.16  Demodulation         : 0.02
% 1.58/1.16  BG Simplification    : 0.01
% 1.58/1.16  Subsumption          : 0.01
% 1.58/1.16  Abstraction          : 0.00
% 1.58/1.16  MUC search           : 0.00
% 1.58/1.16  Cooper               : 0.00
% 1.58/1.16  Total                : 0.36
% 1.58/1.16  Index Insertion      : 0.00
% 1.58/1.16  Index Deletion       : 0.00
% 1.58/1.16  Index Matching       : 0.00
% 1.58/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
