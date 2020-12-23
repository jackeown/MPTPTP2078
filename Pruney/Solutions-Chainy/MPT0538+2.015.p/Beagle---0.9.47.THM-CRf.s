%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:24 EST 2020

% Result     : Theorem 1.46s
% Output     : CNFRefutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   21 (  21 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k1_xboole_0 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_41,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_11,plain,(
    ! [A_5] :
      ( v1_relat_1(A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_15,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_11])).

tff(c_17,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k8_relat_1(A_7,B_8),B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_21,plain,(
    ! [A_7] :
      ( k8_relat_1(A_7,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_17,c_4])).

tff(c_24,plain,(
    ! [A_7] : k8_relat_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15,c_21])).

tff(c_10,plain,(
    k8_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_27,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:37:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.46/1.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.46/1.07  
% 1.46/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.46/1.07  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > #nlpp > k1_xboole_0 > #skF_1
% 1.46/1.07  
% 1.46/1.07  %Foreground sorts:
% 1.46/1.07  
% 1.46/1.07  
% 1.46/1.07  %Background operators:
% 1.46/1.07  
% 1.46/1.07  
% 1.46/1.07  %Foreground operators:
% 1.46/1.07  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.46/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.46/1.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.46/1.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.46/1.07  tff('#skF_1', type, '#skF_1': $i).
% 1.46/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.46/1.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.46/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.46/1.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.46/1.07  
% 1.46/1.08  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.46/1.08  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.46/1.08  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 1.46/1.08  tff(f_30, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.46/1.08  tff(f_41, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 1.46/1.08  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.46/1.08  tff(c_11, plain, (![A_5]: (v1_relat_1(A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.46/1.08  tff(c_15, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_11])).
% 1.46/1.08  tff(c_17, plain, (![A_7, B_8]: (r1_tarski(k8_relat_1(A_7, B_8), B_8) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.46/1.08  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.46/1.08  tff(c_21, plain, (![A_7]: (k8_relat_1(A_7, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_17, c_4])).
% 1.46/1.08  tff(c_24, plain, (![A_7]: (k8_relat_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_15, c_21])).
% 1.46/1.08  tff(c_10, plain, (k8_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.46/1.08  tff(c_27, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_10])).
% 1.46/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.46/1.08  
% 1.46/1.08  Inference rules
% 1.46/1.08  ----------------------
% 1.46/1.08  #Ref     : 0
% 1.46/1.08  #Sup     : 2
% 1.46/1.08  #Fact    : 0
% 1.46/1.08  #Define  : 0
% 1.46/1.08  #Split   : 0
% 1.46/1.08  #Chain   : 0
% 1.46/1.08  #Close   : 0
% 1.46/1.08  
% 1.46/1.08  Ordering : KBO
% 1.46/1.08  
% 1.46/1.08  Simplification rules
% 1.46/1.08  ----------------------
% 1.46/1.08  #Subsume      : 0
% 1.46/1.08  #Demod        : 2
% 1.46/1.08  #Tautology    : 0
% 1.46/1.08  #SimpNegUnit  : 0
% 1.46/1.08  #BackRed      : 1
% 1.46/1.08  
% 1.46/1.08  #Partial instantiations: 0
% 1.46/1.08  #Strategies tried      : 1
% 1.46/1.08  
% 1.46/1.08  Timing (in seconds)
% 1.46/1.08  ----------------------
% 1.60/1.08  Preprocessing        : 0.24
% 1.60/1.08  Parsing              : 0.13
% 1.60/1.08  CNF conversion       : 0.01
% 1.60/1.08  Main loop            : 0.07
% 1.60/1.08  Inferencing          : 0.04
% 1.60/1.08  Reduction            : 0.02
% 1.60/1.08  Demodulation         : 0.01
% 1.60/1.08  BG Simplification    : 0.01
% 1.60/1.08  Subsumption          : 0.00
% 1.60/1.08  Abstraction          : 0.00
% 1.60/1.08  MUC search           : 0.00
% 1.60/1.08  Cooper               : 0.00
% 1.60/1.08  Total                : 0.33
% 1.60/1.08  Index Insertion      : 0.00
% 1.60/1.08  Index Deletion       : 0.00
% 1.60/1.08  Index Matching       : 0.00
% 1.60/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
