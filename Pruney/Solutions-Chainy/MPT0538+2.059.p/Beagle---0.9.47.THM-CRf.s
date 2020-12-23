%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:30 EST 2020

% Result     : Theorem 1.56s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   31 (  47 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  50 expanded)
%              Number of equality atoms :   15 (  26 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_43,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_29,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_25,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_27,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_25])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_33,plain,(
    ! [A_9] :
      ( k8_relat_1(k2_relat_1(A_9),A_9) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,
    ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_33])).

tff(c_46,plain,(
    k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_42])).

tff(c_51,plain,(
    ! [B_10,A_11,C_12] :
      ( k8_relat_1(B_10,k8_relat_1(A_11,C_12)) = k8_relat_1(A_11,C_12)
      | ~ r1_tarski(A_11,B_10)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_70,plain,(
    ! [B_10] :
      ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k8_relat_1(B_10,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,B_10)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_51])).

tff(c_82,plain,(
    ! [B_10] : k8_relat_1(B_10,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_2,c_46,c_70])).

tff(c_16,plain,(
    k8_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_87,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:17:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.56/1.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.04  
% 1.56/1.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.04  %$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.56/1.04  
% 1.56/1.04  %Foreground sorts:
% 1.56/1.04  
% 1.56/1.04  
% 1.56/1.04  %Background operators:
% 1.56/1.04  
% 1.56/1.04  
% 1.56/1.04  %Foreground operators:
% 1.56/1.04  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.56/1.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.56/1.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.56/1.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.56/1.04  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.56/1.04  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.56/1.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.56/1.04  
% 1.56/1.05  tff(f_43, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.56/1.05  tff(f_29, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.56/1.05  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.56/1.05  tff(f_42, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.56/1.05  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_relat_1)).
% 1.56/1.05  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 1.56/1.05  tff(f_46, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 1.56/1.05  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.56/1.05  tff(c_25, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.56/1.05  tff(c_27, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_25])).
% 1.56/1.05  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.56/1.05  tff(c_10, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.56/1.05  tff(c_33, plain, (![A_9]: (k8_relat_1(k2_relat_1(A_9), A_9)=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.56/1.05  tff(c_42, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_33])).
% 1.56/1.05  tff(c_46, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_27, c_42])).
% 1.56/1.05  tff(c_51, plain, (![B_10, A_11, C_12]: (k8_relat_1(B_10, k8_relat_1(A_11, C_12))=k8_relat_1(A_11, C_12) | ~r1_tarski(A_11, B_10) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.56/1.05  tff(c_70, plain, (![B_10]: (k8_relat_1(k1_xboole_0, k1_xboole_0)=k8_relat_1(B_10, k1_xboole_0) | ~r1_tarski(k1_xboole_0, B_10) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_51])).
% 1.56/1.05  tff(c_82, plain, (![B_10]: (k8_relat_1(B_10, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_27, c_2, c_46, c_70])).
% 1.56/1.05  tff(c_16, plain, (k8_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.56/1.05  tff(c_87, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_16])).
% 1.56/1.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.05  
% 1.56/1.05  Inference rules
% 1.56/1.05  ----------------------
% 1.56/1.05  #Ref     : 0
% 1.56/1.05  #Sup     : 20
% 1.56/1.05  #Fact    : 0
% 1.56/1.05  #Define  : 0
% 1.56/1.05  #Split   : 0
% 1.56/1.05  #Chain   : 0
% 1.56/1.05  #Close   : 0
% 1.56/1.05  
% 1.56/1.05  Ordering : KBO
% 1.56/1.05  
% 1.56/1.05  Simplification rules
% 1.56/1.05  ----------------------
% 1.56/1.05  #Subsume      : 0
% 1.56/1.05  #Demod        : 6
% 1.56/1.05  #Tautology    : 15
% 1.56/1.05  #SimpNegUnit  : 0
% 1.56/1.05  #BackRed      : 1
% 1.56/1.05  
% 1.56/1.05  #Partial instantiations: 0
% 1.56/1.05  #Strategies tried      : 1
% 1.56/1.05  
% 1.56/1.05  Timing (in seconds)
% 1.56/1.05  ----------------------
% 1.56/1.06  Preprocessing        : 0.25
% 1.56/1.06  Parsing              : 0.15
% 1.56/1.06  CNF conversion       : 0.01
% 1.56/1.06  Main loop            : 0.09
% 1.56/1.06  Inferencing          : 0.04
% 1.56/1.06  Reduction            : 0.03
% 1.56/1.06  Demodulation         : 0.02
% 1.56/1.06  BG Simplification    : 0.01
% 1.56/1.06  Subsumption          : 0.01
% 1.56/1.06  Abstraction          : 0.00
% 1.56/1.06  MUC search           : 0.00
% 1.56/1.06  Cooper               : 0.00
% 1.56/1.06  Total                : 0.38
% 1.56/1.06  Index Insertion      : 0.00
% 1.56/1.06  Index Deletion       : 0.00
% 1.56/1.06  Index Matching       : 0.00
% 1.56/1.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
