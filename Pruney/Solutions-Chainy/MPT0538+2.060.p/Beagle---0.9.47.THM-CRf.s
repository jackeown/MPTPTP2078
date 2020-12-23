%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:30 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   32 (  53 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  56 expanded)
%              Number of equality atoms :   16 (  32 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_44,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_29,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

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

tff(f_47,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_22,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_22])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_25,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_25])).

tff(c_57,plain,(
    ! [A_12] :
      ( k8_relat_1(k2_relat_1(A_12),A_12) = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,
    ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_57])).

tff(c_73,plain,(
    k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_66])).

tff(c_93,plain,(
    ! [B_14,A_15,C_16] :
      ( k8_relat_1(B_14,k8_relat_1(A_15,C_16)) = k8_relat_1(A_15,C_16)
      | ~ r1_tarski(A_15,B_14)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_115,plain,(
    ! [B_14] :
      ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k8_relat_1(B_14,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,B_14)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_93])).

tff(c_129,plain,(
    ! [B_14] : k8_relat_1(B_14,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2,c_73,c_115])).

tff(c_16,plain,(
    k8_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:25:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.16  
% 1.62/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.16  %$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.62/1.16  
% 1.62/1.16  %Foreground sorts:
% 1.62/1.16  
% 1.62/1.16  
% 1.62/1.16  %Background operators:
% 1.62/1.16  
% 1.62/1.16  
% 1.62/1.16  %Foreground operators:
% 1.62/1.16  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.62/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.62/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.16  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.62/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.62/1.16  
% 1.62/1.17  tff(f_44, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.62/1.17  tff(f_29, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.62/1.17  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.62/1.17  tff(f_43, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.62/1.17  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_relat_1)).
% 1.62/1.17  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 1.62/1.17  tff(f_47, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 1.62/1.17  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.62/1.17  tff(c_22, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.17  tff(c_24, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_22])).
% 1.62/1.17  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.62/1.17  tff(c_25, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.62/1.17  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14, c_25])).
% 1.62/1.17  tff(c_57, plain, (![A_12]: (k8_relat_1(k2_relat_1(A_12), A_12)=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.62/1.17  tff(c_66, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_57])).
% 1.62/1.17  tff(c_73, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_66])).
% 1.62/1.17  tff(c_93, plain, (![B_14, A_15, C_16]: (k8_relat_1(B_14, k8_relat_1(A_15, C_16))=k8_relat_1(A_15, C_16) | ~r1_tarski(A_15, B_14) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.62/1.17  tff(c_115, plain, (![B_14]: (k8_relat_1(k1_xboole_0, k1_xboole_0)=k8_relat_1(B_14, k1_xboole_0) | ~r1_tarski(k1_xboole_0, B_14) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_73, c_93])).
% 1.62/1.17  tff(c_129, plain, (![B_14]: (k8_relat_1(B_14, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2, c_73, c_115])).
% 1.62/1.17  tff(c_16, plain, (k8_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.62/1.17  tff(c_134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_129, c_16])).
% 1.62/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.17  
% 1.62/1.17  Inference rules
% 1.62/1.17  ----------------------
% 1.62/1.17  #Ref     : 0
% 1.62/1.17  #Sup     : 31
% 1.62/1.17  #Fact    : 0
% 1.62/1.17  #Define  : 0
% 1.62/1.17  #Split   : 0
% 1.62/1.17  #Chain   : 0
% 1.62/1.17  #Close   : 0
% 1.62/1.17  
% 1.62/1.17  Ordering : KBO
% 1.62/1.17  
% 1.62/1.17  Simplification rules
% 1.62/1.17  ----------------------
% 1.62/1.17  #Subsume      : 0
% 1.62/1.17  #Demod        : 11
% 1.62/1.17  #Tautology    : 22
% 1.62/1.17  #SimpNegUnit  : 0
% 1.62/1.17  #BackRed      : 1
% 1.62/1.17  
% 1.62/1.17  #Partial instantiations: 0
% 1.62/1.17  #Strategies tried      : 1
% 1.62/1.17  
% 1.62/1.17  Timing (in seconds)
% 1.62/1.17  ----------------------
% 1.82/1.17  Preprocessing        : 0.27
% 1.82/1.17  Parsing              : 0.15
% 1.82/1.17  CNF conversion       : 0.02
% 1.82/1.17  Main loop            : 0.13
% 1.82/1.18  Inferencing          : 0.06
% 1.82/1.18  Reduction            : 0.04
% 1.82/1.18  Demodulation         : 0.03
% 1.82/1.18  BG Simplification    : 0.01
% 1.82/1.18  Subsumption          : 0.01
% 1.82/1.18  Abstraction          : 0.01
% 1.82/1.18  MUC search           : 0.00
% 1.82/1.18  Cooper               : 0.00
% 1.82/1.18  Total                : 0.43
% 1.82/1.18  Index Insertion      : 0.00
% 1.82/1.18  Index Deletion       : 0.00
% 1.82/1.18  Index Matching       : 0.00
% 1.82/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
