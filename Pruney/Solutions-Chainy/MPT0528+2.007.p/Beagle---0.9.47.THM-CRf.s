%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:12 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   18 (  19 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    4
%              Number of atoms          :   14 (  16 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k8_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_36,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k8_relat_1(A,k8_relat_1(A,B)) = k8_relat_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k8_relat_1(A,k8_relat_1(B,C)) = k8_relat_1(k3_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

tff(c_8,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_7,B_8,C_9] :
      ( k8_relat_1(k3_xboole_0(A_7,B_8),C_9) = k8_relat_1(A_7,k8_relat_1(B_8,C_9))
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_10,C_11] :
      ( k8_relat_1(A_10,k8_relat_1(A_10,C_11)) = k8_relat_1(A_10,C_11)
      | ~ v1_relat_1(C_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_18])).

tff(c_6,plain,(
    k8_relat_1('#skF_1',k8_relat_1('#skF_1','#skF_2')) != k8_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_43,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_6])).

tff(c_62,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:40:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.09  
% 1.61/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.09  %$ v1_relat_1 > k8_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.61/1.09  
% 1.61/1.09  %Foreground sorts:
% 1.61/1.09  
% 1.61/1.09  
% 1.61/1.09  %Background operators:
% 1.61/1.09  
% 1.61/1.09  
% 1.61/1.09  %Foreground operators:
% 1.61/1.09  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.61/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.61/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.61/1.09  
% 1.61/1.10  tff(f_36, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k8_relat_1(A, k8_relat_1(A, B)) = k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_relat_1)).
% 1.61/1.10  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.61/1.10  tff(f_31, axiom, (![A, B, C]: (v1_relat_1(C) => (k8_relat_1(A, k8_relat_1(B, C)) = k8_relat_1(k3_xboole_0(A, B), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_relat_1)).
% 1.61/1.10  tff(c_8, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.61/1.10  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.61/1.10  tff(c_18, plain, (![A_7, B_8, C_9]: (k8_relat_1(k3_xboole_0(A_7, B_8), C_9)=k8_relat_1(A_7, k8_relat_1(B_8, C_9)) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.61/1.10  tff(c_30, plain, (![A_10, C_11]: (k8_relat_1(A_10, k8_relat_1(A_10, C_11))=k8_relat_1(A_10, C_11) | ~v1_relat_1(C_11))), inference(superposition, [status(thm), theory('equality')], [c_2, c_18])).
% 1.61/1.10  tff(c_6, plain, (k8_relat_1('#skF_1', k8_relat_1('#skF_1', '#skF_2'))!=k8_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.61/1.10  tff(c_43, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30, c_6])).
% 1.61/1.10  tff(c_62, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_43])).
% 1.61/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.10  
% 1.61/1.10  Inference rules
% 1.61/1.10  ----------------------
% 1.61/1.10  #Ref     : 0
% 1.61/1.10  #Sup     : 13
% 1.61/1.10  #Fact    : 0
% 1.61/1.10  #Define  : 0
% 1.61/1.10  #Split   : 0
% 1.61/1.10  #Chain   : 0
% 1.61/1.10  #Close   : 0
% 1.61/1.10  
% 1.61/1.10  Ordering : KBO
% 1.61/1.10  
% 1.61/1.10  Simplification rules
% 1.61/1.10  ----------------------
% 1.61/1.10  #Subsume      : 0
% 1.61/1.10  #Demod        : 1
% 1.61/1.10  #Tautology    : 6
% 1.61/1.10  #SimpNegUnit  : 0
% 1.61/1.10  #BackRed      : 0
% 1.61/1.10  
% 1.61/1.10  #Partial instantiations: 0
% 1.61/1.10  #Strategies tried      : 1
% 1.61/1.10  
% 1.61/1.10  Timing (in seconds)
% 1.61/1.10  ----------------------
% 1.61/1.10  Preprocessing        : 0.26
% 1.61/1.10  Parsing              : 0.14
% 1.61/1.11  CNF conversion       : 0.02
% 1.61/1.11  Main loop            : 0.08
% 1.61/1.11  Inferencing          : 0.04
% 1.61/1.11  Reduction            : 0.02
% 1.61/1.11  Demodulation         : 0.02
% 1.61/1.11  BG Simplification    : 0.01
% 1.61/1.11  Subsumption          : 0.01
% 1.61/1.11  Abstraction          : 0.01
% 1.61/1.11  MUC search           : 0.00
% 1.61/1.11  Cooper               : 0.00
% 1.61/1.11  Total                : 0.37
% 1.61/1.11  Index Insertion      : 0.00
% 1.61/1.11  Index Deletion       : 0.00
% 1.61/1.11  Index Matching       : 0.00
% 1.61/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
