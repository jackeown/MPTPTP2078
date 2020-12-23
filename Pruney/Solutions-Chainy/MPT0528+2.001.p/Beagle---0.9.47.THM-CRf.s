%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:11 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k8_relat_1(A,k8_relat_1(A,B)) = k8_relat_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_17,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_21,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_17])).

tff(c_38,plain,(
    ! [A_14,B_15,C_16] :
      ( k8_relat_1(k3_xboole_0(A_14,B_15),C_16) = k8_relat_1(A_14,k8_relat_1(B_15,C_16))
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,(
    ! [B_17,C_18] :
      ( k8_relat_1(B_17,k8_relat_1(B_17,C_18)) = k8_relat_1(B_17,C_18)
      | ~ v1_relat_1(C_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21,c_38])).

tff(c_12,plain,(
    k8_relat_1('#skF_1',k8_relat_1('#skF_1','#skF_2')) != k8_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_63,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_12])).

tff(c_82,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:58:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.09  
% 1.65/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.10  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.65/1.10  
% 1.65/1.10  %Foreground sorts:
% 1.65/1.10  
% 1.65/1.10  
% 1.65/1.10  %Background operators:
% 1.65/1.10  
% 1.65/1.10  
% 1.65/1.10  %Foreground operators:
% 1.65/1.10  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.65/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.65/1.10  
% 1.65/1.10  tff(f_44, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k8_relat_1(A, k8_relat_1(A, B)) = k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_relat_1)).
% 1.65/1.10  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.65/1.10  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.65/1.10  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_relat_1)).
% 1.65/1.10  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.65/1.10  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.10  tff(c_17, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.65/1.10  tff(c_21, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_17])).
% 1.65/1.10  tff(c_38, plain, (![A_14, B_15, C_16]: (k8_relat_1(k3_xboole_0(A_14, B_15), C_16)=k8_relat_1(A_14, k8_relat_1(B_15, C_16)) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.65/1.10  tff(c_50, plain, (![B_17, C_18]: (k8_relat_1(B_17, k8_relat_1(B_17, C_18))=k8_relat_1(B_17, C_18) | ~v1_relat_1(C_18))), inference(superposition, [status(thm), theory('equality')], [c_21, c_38])).
% 1.65/1.10  tff(c_12, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_1', '#skF_2'))!=k8_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.65/1.10  tff(c_63, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_50, c_12])).
% 1.65/1.10  tff(c_82, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_63])).
% 1.65/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.10  
% 1.65/1.10  Inference rules
% 1.65/1.10  ----------------------
% 1.65/1.10  #Ref     : 0
% 1.65/1.10  #Sup     : 15
% 1.65/1.10  #Fact    : 0
% 1.65/1.10  #Define  : 0
% 1.65/1.10  #Split   : 0
% 1.65/1.10  #Chain   : 0
% 1.65/1.10  #Close   : 0
% 1.65/1.10  
% 1.65/1.10  Ordering : KBO
% 1.65/1.10  
% 1.65/1.10  Simplification rules
% 1.65/1.10  ----------------------
% 1.65/1.10  #Subsume      : 0
% 1.65/1.10  #Demod        : 3
% 1.65/1.10  #Tautology    : 8
% 1.65/1.10  #SimpNegUnit  : 0
% 1.65/1.10  #BackRed      : 0
% 1.65/1.10  
% 1.65/1.10  #Partial instantiations: 0
% 1.65/1.10  #Strategies tried      : 1
% 1.65/1.10  
% 1.65/1.10  Timing (in seconds)
% 1.65/1.10  ----------------------
% 1.65/1.11  Preprocessing        : 0.25
% 1.65/1.11  Parsing              : 0.14
% 1.65/1.11  CNF conversion       : 0.02
% 1.65/1.11  Main loop            : 0.09
% 1.65/1.11  Inferencing          : 0.04
% 1.65/1.11  Reduction            : 0.02
% 1.65/1.11  Demodulation         : 0.02
% 1.65/1.11  BG Simplification    : 0.01
% 1.65/1.11  Subsumption          : 0.01
% 1.65/1.11  Abstraction          : 0.01
% 1.65/1.11  MUC search           : 0.00
% 1.65/1.11  Cooper               : 0.00
% 1.65/1.11  Total                : 0.36
% 1.65/1.11  Index Insertion      : 0.00
% 1.65/1.11  Index Deletion       : 0.00
% 1.65/1.11  Index Matching       : 0.00
% 1.65/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
