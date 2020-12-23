%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:25 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   25 (  25 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_24,plain,(
    ! [A_6] :
      ( v1_relat_1(A_6)
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_24])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_10,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_29,plain,(
    ! [A_7,B_8] :
      ( k8_relat_1(A_7,B_8) = B_8
      | ~ r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,(
    ! [A_7] :
      ( k8_relat_1(A_7,k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_7)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_29])).

tff(c_34,plain,(
    ! [A_7] : k8_relat_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4,c_32])).

tff(c_14,plain,(
    k8_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_37,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n023.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 17:10:05 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.09  
% 1.60/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.09  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.60/1.09  
% 1.60/1.09  %Foreground sorts:
% 1.60/1.09  
% 1.60/1.09  
% 1.60/1.09  %Background operators:
% 1.60/1.09  
% 1.60/1.09  
% 1.60/1.09  %Foreground operators:
% 1.60/1.09  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.60/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.60/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.60/1.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.60/1.09  
% 1.60/1.10  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.60/1.10  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.60/1.10  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.60/1.10  tff(f_41, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.60/1.10  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 1.60/1.10  tff(f_44, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 1.60/1.10  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.60/1.10  tff(c_24, plain, (![A_6]: (v1_relat_1(A_6) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.10  tff(c_28, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_24])).
% 1.60/1.10  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.60/1.10  tff(c_10, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.60/1.10  tff(c_29, plain, (![A_7, B_8]: (k8_relat_1(A_7, B_8)=B_8 | ~r1_tarski(k2_relat_1(B_8), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.60/1.10  tff(c_32, plain, (![A_7]: (k8_relat_1(A_7, k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_7) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_29])).
% 1.60/1.10  tff(c_34, plain, (![A_7]: (k8_relat_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4, c_32])).
% 1.60/1.10  tff(c_14, plain, (k8_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.60/1.10  tff(c_37, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_14])).
% 1.60/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.10  
% 1.60/1.10  Inference rules
% 1.60/1.10  ----------------------
% 1.60/1.10  #Ref     : 0
% 1.60/1.10  #Sup     : 6
% 1.60/1.10  #Fact    : 0
% 1.60/1.10  #Define  : 0
% 1.60/1.10  #Split   : 0
% 1.60/1.10  #Chain   : 0
% 1.60/1.10  #Close   : 0
% 1.60/1.10  
% 1.60/1.10  Ordering : KBO
% 1.60/1.10  
% 1.60/1.10  Simplification rules
% 1.60/1.10  ----------------------
% 1.60/1.10  #Subsume      : 0
% 1.60/1.10  #Demod        : 3
% 1.60/1.10  #Tautology    : 4
% 1.60/1.10  #SimpNegUnit  : 0
% 1.60/1.10  #BackRed      : 1
% 1.60/1.10  
% 1.60/1.10  #Partial instantiations: 0
% 1.60/1.10  #Strategies tried      : 1
% 1.60/1.10  
% 1.60/1.10  Timing (in seconds)
% 1.60/1.10  ----------------------
% 1.60/1.10  Preprocessing        : 0.25
% 1.60/1.10  Parsing              : 0.14
% 1.60/1.10  CNF conversion       : 0.01
% 1.60/1.10  Main loop            : 0.08
% 1.60/1.10  Inferencing          : 0.04
% 1.60/1.10  Reduction            : 0.02
% 1.60/1.10  Demodulation         : 0.02
% 1.60/1.10  BG Simplification    : 0.01
% 1.60/1.10  Subsumption          : 0.01
% 1.60/1.10  Abstraction          : 0.00
% 1.60/1.10  MUC search           : 0.00
% 1.60/1.10  Cooper               : 0.00
% 1.60/1.10  Total                : 0.34
% 1.60/1.10  Index Insertion      : 0.00
% 1.60/1.10  Index Deletion       : 0.00
% 1.60/1.10  Index Matching       : 0.00
% 1.60/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
