%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:22 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   31 (  32 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    4
%              Number of atoms          :   28 (  30 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_45,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_43,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_16,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_26,plain,(
    ! [A_7] :
      ( v1_relat_1(A_7)
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_26])).

tff(c_6,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_31,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_35,plain,(
    ! [A_3] : k2_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(resolution,[status(thm)],[c_6,c_31])).

tff(c_14,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_45,plain,(
    ! [A_11] :
      ( k2_xboole_0(k1_relat_1(A_11),k2_relat_1(A_11)) = k3_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_54,plain,
    ( k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_45])).

tff(c_61,plain,(
    k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_35,c_14,c_54])).

tff(c_63,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:52:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.09  
% 1.62/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.09  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0
% 1.62/1.09  
% 1.62/1.09  %Foreground sorts:
% 1.62/1.09  
% 1.62/1.09  
% 1.62/1.09  %Background operators:
% 1.62/1.09  
% 1.62/1.09  
% 1.62/1.09  %Foreground operators:
% 1.62/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.09  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.62/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.62/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.62/1.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.62/1.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.62/1.09  
% 1.62/1.10  tff(f_45, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_relat_1)).
% 1.62/1.10  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.62/1.10  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.62/1.10  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.62/1.10  tff(f_30, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.62/1.10  tff(f_43, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.62/1.10  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 1.62/1.10  tff(c_16, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.62/1.10  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.62/1.10  tff(c_26, plain, (![A_7]: (v1_relat_1(A_7) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.62/1.10  tff(c_30, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_26])).
% 1.62/1.10  tff(c_6, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.62/1.10  tff(c_31, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.62/1.10  tff(c_35, plain, (![A_3]: (k2_xboole_0(k1_xboole_0, A_3)=A_3)), inference(resolution, [status(thm)], [c_6, c_31])).
% 1.62/1.10  tff(c_14, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.62/1.10  tff(c_12, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.62/1.10  tff(c_45, plain, (![A_11]: (k2_xboole_0(k1_relat_1(A_11), k2_relat_1(A_11))=k3_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.62/1.10  tff(c_54, plain, (k2_xboole_0(k1_relat_1(k1_xboole_0), k1_xboole_0)=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_45])).
% 1.62/1.10  tff(c_61, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_35, c_14, c_54])).
% 1.62/1.10  tff(c_63, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_61])).
% 1.62/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.10  
% 1.62/1.10  Inference rules
% 1.62/1.10  ----------------------
% 1.62/1.10  #Ref     : 0
% 1.62/1.10  #Sup     : 12
% 1.62/1.10  #Fact    : 0
% 1.62/1.10  #Define  : 0
% 1.62/1.10  #Split   : 0
% 1.62/1.10  #Chain   : 0
% 1.62/1.10  #Close   : 0
% 1.62/1.10  
% 1.62/1.10  Ordering : KBO
% 1.62/1.10  
% 1.62/1.10  Simplification rules
% 1.62/1.10  ----------------------
% 1.62/1.10  #Subsume      : 0
% 1.62/1.10  #Demod        : 3
% 1.62/1.10  #Tautology    : 8
% 1.62/1.10  #SimpNegUnit  : 1
% 1.62/1.10  #BackRed      : 0
% 1.62/1.10  
% 1.62/1.10  #Partial instantiations: 0
% 1.62/1.10  #Strategies tried      : 1
% 1.62/1.10  
% 1.62/1.10  Timing (in seconds)
% 1.62/1.10  ----------------------
% 1.62/1.10  Preprocessing        : 0.25
% 1.62/1.10  Parsing              : 0.14
% 1.62/1.10  CNF conversion       : 0.01
% 1.62/1.10  Main loop            : 0.09
% 1.62/1.10  Inferencing          : 0.04
% 1.62/1.10  Reduction            : 0.03
% 1.62/1.10  Demodulation         : 0.02
% 1.62/1.10  BG Simplification    : 0.01
% 1.62/1.10  Subsumption          : 0.01
% 1.62/1.10  Abstraction          : 0.00
% 1.62/1.10  MUC search           : 0.00
% 1.62/1.10  Cooper               : 0.00
% 1.62/1.10  Total                : 0.37
% 1.62/1.10  Index Insertion      : 0.00
% 1.62/1.10  Index Deletion       : 0.00
% 1.62/1.10  Index Matching       : 0.00
% 1.62/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
