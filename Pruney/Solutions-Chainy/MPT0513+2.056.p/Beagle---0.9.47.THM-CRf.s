%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:05 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.49s
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
%$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_32,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_39,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_6,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_15,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_17,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_15])).

tff(c_19,plain,(
    ! [B_7,A_8] :
      ( r1_tarski(k7_relat_1(B_7,A_8),B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_23,plain,(
    ! [A_8] :
      ( k7_relat_1(k1_xboole_0,A_8) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_19,c_2])).

tff(c_26,plain,(
    ! [A_8] : k7_relat_1(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17,c_23])).

tff(c_10,plain,(
    k7_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_29,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:27:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.49/1.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.02  
% 1.49/1.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.03  %$ r1_tarski > v1_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1
% 1.49/1.03  
% 1.49/1.03  %Foreground sorts:
% 1.49/1.03  
% 1.49/1.03  
% 1.49/1.03  %Background operators:
% 1.49/1.03  
% 1.49/1.03  
% 1.49/1.03  %Foreground operators:
% 1.49/1.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.49/1.03  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.49/1.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.49/1.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.49/1.03  tff('#skF_1', type, '#skF_1': $i).
% 1.49/1.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.49/1.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.49/1.03  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.49/1.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.49/1.03  
% 1.49/1.04  tff(f_32, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.49/1.04  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.49/1.04  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 1.49/1.04  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.49/1.04  tff(f_39, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.49/1.04  tff(c_6, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.49/1.04  tff(c_15, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.49/1.04  tff(c_17, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_15])).
% 1.49/1.04  tff(c_19, plain, (![B_7, A_8]: (r1_tarski(k7_relat_1(B_7, A_8), B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.49/1.04  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.49/1.04  tff(c_23, plain, (![A_8]: (k7_relat_1(k1_xboole_0, A_8)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_19, c_2])).
% 1.49/1.04  tff(c_26, plain, (![A_8]: (k7_relat_1(k1_xboole_0, A_8)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_17, c_23])).
% 1.49/1.04  tff(c_10, plain, (k7_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.49/1.04  tff(c_29, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_10])).
% 1.49/1.04  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.49/1.04  
% 1.49/1.04  Inference rules
% 1.49/1.04  ----------------------
% 1.49/1.04  #Ref     : 0
% 1.49/1.04  #Sup     : 4
% 1.49/1.04  #Fact    : 0
% 1.49/1.04  #Define  : 0
% 1.49/1.04  #Split   : 0
% 1.49/1.04  #Chain   : 0
% 1.49/1.04  #Close   : 0
% 1.49/1.04  
% 1.49/1.04  Ordering : KBO
% 1.49/1.04  
% 1.49/1.04  Simplification rules
% 1.49/1.04  ----------------------
% 1.49/1.04  #Subsume      : 0
% 1.49/1.04  #Demod        : 2
% 1.49/1.04  #Tautology    : 2
% 1.49/1.04  #SimpNegUnit  : 0
% 1.49/1.04  #BackRed      : 1
% 1.49/1.04  
% 1.49/1.04  #Partial instantiations: 0
% 1.49/1.04  #Strategies tried      : 1
% 1.49/1.04  
% 1.49/1.04  Timing (in seconds)
% 1.49/1.04  ----------------------
% 1.49/1.04  Preprocessing        : 0.24
% 1.49/1.04  Parsing              : 0.14
% 1.49/1.04  CNF conversion       : 0.01
% 1.49/1.04  Main loop            : 0.06
% 1.49/1.04  Inferencing          : 0.03
% 1.49/1.04  Reduction            : 0.02
% 1.49/1.04  Demodulation         : 0.01
% 1.49/1.04  BG Simplification    : 0.01
% 1.49/1.04  Subsumption          : 0.00
% 1.49/1.04  Abstraction          : 0.00
% 1.49/1.04  MUC search           : 0.00
% 1.49/1.04  Cooper               : 0.00
% 1.49/1.05  Total                : 0.33
% 1.49/1.05  Index Insertion      : 0.00
% 1.49/1.05  Index Deletion       : 0.00
% 1.49/1.05  Index Matching       : 0.00
% 1.49/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
