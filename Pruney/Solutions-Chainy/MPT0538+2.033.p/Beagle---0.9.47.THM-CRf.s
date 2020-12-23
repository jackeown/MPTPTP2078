%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:27 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  25 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    6 (   3 average)
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

tff(f_40,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_35,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_22])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(k8_relat_1(A_5,B_6),B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [B_12,A_13] :
      ( B_12 = A_13
      | ~ r1_tarski(B_12,A_13)
      | ~ r1_tarski(A_13,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_41,plain,(
    ! [A_14] :
      ( k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_28])).

tff(c_45,plain,(
    ! [A_5] :
      ( k8_relat_1(A_5,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_41])).

tff(c_56,plain,(
    ! [A_5] : k8_relat_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_45])).

tff(c_16,plain,(
    k8_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_71,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:16:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.14  
% 1.54/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.14  %$ r1_tarski > v1_relat_1 > k8_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1
% 1.54/1.14  
% 1.54/1.14  %Foreground sorts:
% 1.54/1.14  
% 1.54/1.14  
% 1.54/1.14  %Background operators:
% 1.54/1.14  
% 1.54/1.14  
% 1.54/1.14  %Foreground operators:
% 1.54/1.14  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.54/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.54/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.54/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.54/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.54/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.54/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.54/1.14  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.54/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.54/1.14  
% 1.65/1.15  tff(f_40, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.65/1.15  tff(f_35, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.65/1.15  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 1.65/1.15  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.65/1.15  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.65/1.15  tff(f_43, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_relat_1)).
% 1.65/1.15  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.65/1.15  tff(c_22, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.65/1.15  tff(c_24, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_22])).
% 1.65/1.15  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(k8_relat_1(A_5, B_6), B_6) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.65/1.15  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.65/1.15  tff(c_28, plain, (![B_12, A_13]: (B_12=A_13 | ~r1_tarski(B_12, A_13) | ~r1_tarski(A_13, B_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.15  tff(c_41, plain, (![A_14]: (k1_xboole_0=A_14 | ~r1_tarski(A_14, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_28])).
% 1.65/1.15  tff(c_45, plain, (![A_5]: (k8_relat_1(A_5, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_41])).
% 1.65/1.15  tff(c_56, plain, (![A_5]: (k8_relat_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_45])).
% 1.65/1.15  tff(c_16, plain, (k8_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.65/1.15  tff(c_71, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_16])).
% 1.65/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.15  
% 1.65/1.15  Inference rules
% 1.65/1.15  ----------------------
% 1.65/1.15  #Ref     : 0
% 1.65/1.15  #Sup     : 10
% 1.65/1.15  #Fact    : 0
% 1.65/1.15  #Define  : 0
% 1.65/1.15  #Split   : 0
% 1.65/1.15  #Chain   : 0
% 1.65/1.15  #Close   : 0
% 1.65/1.15  
% 1.65/1.15  Ordering : KBO
% 1.65/1.15  
% 1.65/1.15  Simplification rules
% 1.65/1.15  ----------------------
% 1.65/1.15  #Subsume      : 0
% 1.65/1.15  #Demod        : 5
% 1.65/1.15  #Tautology    : 6
% 1.65/1.15  #SimpNegUnit  : 0
% 1.65/1.15  #BackRed      : 1
% 1.65/1.15  
% 1.65/1.15  #Partial instantiations: 0
% 1.65/1.15  #Strategies tried      : 1
% 1.65/1.15  
% 1.65/1.15  Timing (in seconds)
% 1.65/1.15  ----------------------
% 1.65/1.15  Preprocessing        : 0.25
% 1.65/1.15  Parsing              : 0.14
% 1.65/1.15  CNF conversion       : 0.01
% 1.65/1.15  Main loop            : 0.09
% 1.65/1.15  Inferencing          : 0.04
% 1.65/1.15  Reduction            : 0.02
% 1.65/1.15  Demodulation         : 0.02
% 1.65/1.15  BG Simplification    : 0.01
% 1.65/1.15  Subsumption          : 0.01
% 1.65/1.15  Abstraction          : 0.00
% 1.65/1.15  MUC search           : 0.00
% 1.65/1.15  Cooper               : 0.00
% 1.65/1.15  Total                : 0.36
% 1.65/1.15  Index Insertion      : 0.00
% 1.65/1.15  Index Deletion       : 0.00
% 1.65/1.15  Index Matching       : 0.00
% 1.65/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
