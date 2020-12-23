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

% Result     : Theorem 1.52s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   23 (  23 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_39,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_29,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_20])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_31,plain,(
    ! [A_7,B_8] :
      ( k8_relat_1(A_7,B_8) = B_8
      | ~ r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ! [A_7] :
      ( k8_relat_1(A_7,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_7)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_31])).

tff(c_36,plain,(
    ! [A_7] : k8_relat_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2,c_34])).

tff(c_14,plain,(
    k8_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_39,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:46:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.52/1.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.07  
% 1.52/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.52/1.07  %$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.52/1.07  
% 1.52/1.07  %Foreground sorts:
% 1.52/1.07  
% 1.52/1.07  
% 1.52/1.07  %Background operators:
% 1.52/1.07  
% 1.52/1.07  
% 1.52/1.07  %Foreground operators:
% 1.52/1.07  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.52/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.52/1.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.52/1.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.52/1.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.52/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.52/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.52/1.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.52/1.07  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.52/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.52/1.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.52/1.07  
% 1.64/1.08  tff(f_39, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.64/1.08  tff(f_29, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.64/1.08  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.64/1.08  tff(f_38, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.64/1.08  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 1.64/1.08  tff(f_42, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 1.64/1.08  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.64/1.08  tff(c_20, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.08  tff(c_22, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_20])).
% 1.64/1.08  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.64/1.08  tff(c_8, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.64/1.08  tff(c_31, plain, (![A_7, B_8]: (k8_relat_1(A_7, B_8)=B_8 | ~r1_tarski(k2_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.64/1.08  tff(c_34, plain, (![A_7]: (k8_relat_1(A_7, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_7) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_31])).
% 1.64/1.08  tff(c_36, plain, (![A_7]: (k8_relat_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2, c_34])).
% 1.64/1.08  tff(c_14, plain, (k8_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.64/1.08  tff(c_39, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_14])).
% 1.64/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.08  
% 1.64/1.08  Inference rules
% 1.64/1.08  ----------------------
% 1.64/1.08  #Ref     : 0
% 1.64/1.08  #Sup     : 8
% 1.64/1.08  #Fact    : 0
% 1.64/1.08  #Define  : 0
% 1.64/1.08  #Split   : 0
% 1.64/1.08  #Chain   : 0
% 1.64/1.08  #Close   : 0
% 1.64/1.08  
% 1.64/1.08  Ordering : KBO
% 1.64/1.08  
% 1.64/1.08  Simplification rules
% 1.64/1.08  ----------------------
% 1.64/1.08  #Subsume      : 0
% 1.64/1.08  #Demod        : 3
% 1.64/1.08  #Tautology    : 6
% 1.64/1.08  #SimpNegUnit  : 0
% 1.64/1.08  #BackRed      : 1
% 1.64/1.08  
% 1.64/1.08  #Partial instantiations: 0
% 1.64/1.08  #Strategies tried      : 1
% 1.64/1.08  
% 1.64/1.08  Timing (in seconds)
% 1.64/1.08  ----------------------
% 1.64/1.08  Preprocessing        : 0.25
% 1.64/1.08  Parsing              : 0.14
% 1.64/1.08  CNF conversion       : 0.01
% 1.64/1.08  Main loop            : 0.08
% 1.64/1.08  Inferencing          : 0.04
% 1.64/1.08  Reduction            : 0.02
% 1.64/1.08  Demodulation         : 0.02
% 1.64/1.08  BG Simplification    : 0.01
% 1.64/1.08  Subsumption          : 0.01
% 1.64/1.08  Abstraction          : 0.00
% 1.64/1.08  MUC search           : 0.00
% 1.64/1.08  Cooper               : 0.00
% 1.64/1.08  Total                : 0.35
% 1.64/1.09  Index Insertion      : 0.00
% 1.64/1.09  Index Deletion       : 0.00
% 1.64/1.09  Index Matching       : 0.00
% 1.64/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
