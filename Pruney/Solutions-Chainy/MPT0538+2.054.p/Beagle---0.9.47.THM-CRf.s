%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:29 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   19 (  19 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_36,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_39,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_8,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_15,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_17,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_15])).

tff(c_19,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k8_relat_1(A_7,B_8),B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_23,plain,(
    ! [A_7] :
      ( k8_relat_1(A_7,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_19,c_2])).

tff(c_26,plain,(
    ! [A_7] : k8_relat_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17,c_23])).

tff(c_10,plain,(
    k8_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_29,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:46:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.16  
% 1.61/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.17  %$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1
% 1.72/1.17  
% 1.72/1.17  %Foreground sorts:
% 1.72/1.17  
% 1.72/1.17  
% 1.72/1.17  %Background operators:
% 1.72/1.17  
% 1.72/1.17  
% 1.72/1.17  %Foreground operators:
% 1.72/1.17  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.72/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.72/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.72/1.17  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.72/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.17  
% 1.72/1.18  tff(f_36, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.72/1.18  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.72/1.18  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 1.72/1.18  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.72/1.18  tff(f_39, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 1.72/1.18  tff(c_8, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.72/1.18  tff(c_15, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.72/1.18  tff(c_17, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_15])).
% 1.72/1.18  tff(c_19, plain, (![A_7, B_8]: (r1_tarski(k8_relat_1(A_7, B_8), B_8) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.72/1.18  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.72/1.18  tff(c_23, plain, (![A_7]: (k8_relat_1(A_7, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_19, c_2])).
% 1.72/1.18  tff(c_26, plain, (![A_7]: (k8_relat_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_17, c_23])).
% 1.72/1.18  tff(c_10, plain, (k8_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.72/1.18  tff(c_29, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_10])).
% 1.72/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.18  
% 1.72/1.18  Inference rules
% 1.72/1.18  ----------------------
% 1.72/1.18  #Ref     : 0
% 1.72/1.18  #Sup     : 4
% 1.72/1.18  #Fact    : 0
% 1.72/1.18  #Define  : 0
% 1.72/1.18  #Split   : 0
% 1.72/1.18  #Chain   : 0
% 1.72/1.18  #Close   : 0
% 1.72/1.18  
% 1.72/1.18  Ordering : KBO
% 1.72/1.18  
% 1.72/1.18  Simplification rules
% 1.72/1.18  ----------------------
% 1.72/1.18  #Subsume      : 0
% 1.72/1.18  #Demod        : 2
% 1.72/1.18  #Tautology    : 2
% 1.72/1.18  #SimpNegUnit  : 0
% 1.72/1.18  #BackRed      : 1
% 1.72/1.18  
% 1.72/1.18  #Partial instantiations: 0
% 1.72/1.18  #Strategies tried      : 1
% 1.72/1.18  
% 1.72/1.18  Timing (in seconds)
% 1.72/1.18  ----------------------
% 1.72/1.18  Preprocessing        : 0.28
% 1.72/1.18  Parsing              : 0.16
% 1.72/1.18  CNF conversion       : 0.01
% 1.72/1.18  Main loop            : 0.07
% 1.72/1.18  Inferencing          : 0.03
% 1.72/1.18  Reduction            : 0.02
% 1.72/1.18  Demodulation         : 0.02
% 1.72/1.19  BG Simplification    : 0.01
% 1.72/1.19  Subsumption          : 0.01
% 1.72/1.19  Abstraction          : 0.00
% 1.72/1.19  MUC search           : 0.00
% 1.72/1.19  Cooper               : 0.00
% 1.72/1.19  Total                : 0.38
% 1.72/1.19  Index Insertion      : 0.00
% 1.72/1.19  Index Deletion       : 0.00
% 1.72/1.19  Index Matching       : 0.00
% 1.72/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
