%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:34 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  23 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_38,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_12,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_23,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_25,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_23])).

tff(c_10,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_31,plain,(
    ! [B_7,A_8] :
      ( r1_tarski(k10_relat_1(B_7,A_8),k1_relat_1(B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ! [A_8] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_8),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_31])).

tff(c_37,plain,(
    ! [A_9] : r1_tarski(k10_relat_1(k1_xboole_0,A_9),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_34])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    ! [A_9] : k10_relat_1(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37,c_2])).

tff(c_14,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_45,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.08  
% 1.54/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.09  %$ r1_tarski > v1_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
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
% 1.62/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.62/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.09  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.62/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.09  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.62/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.62/1.09  
% 1.62/1.10  tff(f_39, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.62/1.10  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.62/1.10  tff(f_38, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.62/1.10  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 1.62/1.10  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.62/1.10  tff(f_42, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.62/1.10  tff(c_12, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.62/1.10  tff(c_23, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.10  tff(c_25, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_23])).
% 1.62/1.10  tff(c_10, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.62/1.10  tff(c_31, plain, (![B_7, A_8]: (r1_tarski(k10_relat_1(B_7, A_8), k1_relat_1(B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.62/1.10  tff(c_34, plain, (![A_8]: (r1_tarski(k10_relat_1(k1_xboole_0, A_8), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_31])).
% 1.62/1.10  tff(c_37, plain, (![A_9]: (r1_tarski(k10_relat_1(k1_xboole_0, A_9), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_25, c_34])).
% 1.62/1.10  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.10  tff(c_41, plain, (![A_9]: (k10_relat_1(k1_xboole_0, A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_37, c_2])).
% 1.62/1.10  tff(c_14, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.62/1.10  tff(c_45, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41, c_14])).
% 1.62/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.62/1.10  
% 1.62/1.10  Inference rules
% 1.62/1.10  ----------------------
% 1.62/1.10  #Ref     : 0
% 1.62/1.10  #Sup     : 9
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
% 1.62/1.10  #Tautology    : 6
% 1.62/1.10  #SimpNegUnit  : 0
% 1.62/1.10  #BackRed      : 2
% 1.62/1.10  
% 1.62/1.10  #Partial instantiations: 0
% 1.62/1.10  #Strategies tried      : 1
% 1.62/1.10  
% 1.62/1.10  Timing (in seconds)
% 1.62/1.10  ----------------------
% 1.62/1.10  Preprocessing        : 0.26
% 1.62/1.10  Parsing              : 0.14
% 1.62/1.10  CNF conversion       : 0.02
% 1.62/1.10  Main loop            : 0.08
% 1.62/1.10  Inferencing          : 0.03
% 1.62/1.10  Reduction            : 0.02
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
