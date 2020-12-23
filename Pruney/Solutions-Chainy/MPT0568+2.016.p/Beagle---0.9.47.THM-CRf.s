%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:22 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  28 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_43,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_32,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_46,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_27,plain,(
    ! [A_7] :
      ( v1_relat_1(A_7)
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_31,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_27])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_47,plain,(
    ! [B_13,A_14] :
      ( r1_tarski(k10_relat_1(B_13,A_14),k1_relat_1(B_13))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_53,plain,(
    ! [A_14] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_14),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_47])).

tff(c_57,plain,(
    ! [A_15] : r1_tarski(k10_relat_1(k1_xboole_0,A_15),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_53])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_62,plain,(
    ! [A_16] : k4_xboole_0(k10_relat_1(k1_xboole_0,A_16),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_57,c_6])).

tff(c_8,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,(
    ! [A_16] : k10_relat_1(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_8])).

tff(c_18,plain,(
    k10_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_80,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:04:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.11  
% 1.74/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.11  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.74/1.11  
% 1.74/1.11  %Foreground sorts:
% 1.74/1.11  
% 1.74/1.11  
% 1.74/1.11  %Background operators:
% 1.74/1.11  
% 1.74/1.11  
% 1.74/1.11  %Foreground operators:
% 1.74/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.74/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.74/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.74/1.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.74/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.11  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.74/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.74/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.74/1.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.74/1.11  
% 1.74/1.12  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.74/1.12  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.74/1.12  tff(f_43, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.74/1.12  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 1.74/1.12  tff(f_30, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.74/1.12  tff(f_32, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.74/1.12  tff(f_46, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.74/1.12  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.74/1.12  tff(c_27, plain, (![A_7]: (v1_relat_1(A_7) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.74/1.12  tff(c_31, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_27])).
% 1.74/1.12  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.74/1.12  tff(c_47, plain, (![B_13, A_14]: (r1_tarski(k10_relat_1(B_13, A_14), k1_relat_1(B_13)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.74/1.12  tff(c_53, plain, (![A_14]: (r1_tarski(k10_relat_1(k1_xboole_0, A_14), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_47])).
% 1.74/1.12  tff(c_57, plain, (![A_15]: (r1_tarski(k10_relat_1(k1_xboole_0, A_15), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_53])).
% 1.74/1.12  tff(c_6, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.74/1.12  tff(c_62, plain, (![A_16]: (k4_xboole_0(k10_relat_1(k1_xboole_0, A_16), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_57, c_6])).
% 1.74/1.12  tff(c_8, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.74/1.12  tff(c_67, plain, (![A_16]: (k10_relat_1(k1_xboole_0, A_16)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_62, c_8])).
% 1.74/1.12  tff(c_18, plain, (k10_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.74/1.12  tff(c_80, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_18])).
% 1.74/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.12  
% 1.74/1.12  Inference rules
% 1.74/1.12  ----------------------
% 1.74/1.12  #Ref     : 0
% 1.74/1.12  #Sup     : 15
% 1.74/1.12  #Fact    : 0
% 1.74/1.12  #Define  : 0
% 1.74/1.12  #Split   : 0
% 1.74/1.12  #Chain   : 0
% 1.74/1.12  #Close   : 0
% 1.74/1.12  
% 1.74/1.12  Ordering : KBO
% 1.74/1.12  
% 1.74/1.12  Simplification rules
% 1.74/1.12  ----------------------
% 1.74/1.12  #Subsume      : 0
% 1.74/1.12  #Demod        : 5
% 1.74/1.12  #Tautology    : 10
% 1.74/1.12  #SimpNegUnit  : 0
% 1.74/1.12  #BackRed      : 3
% 1.74/1.12  
% 1.74/1.12  #Partial instantiations: 0
% 1.74/1.12  #Strategies tried      : 1
% 1.74/1.12  
% 1.74/1.12  Timing (in seconds)
% 1.74/1.12  ----------------------
% 1.74/1.13  Preprocessing        : 0.26
% 1.74/1.13  Parsing              : 0.15
% 1.74/1.13  CNF conversion       : 0.01
% 1.74/1.13  Main loop            : 0.11
% 1.74/1.13  Inferencing          : 0.05
% 1.74/1.13  Reduction            : 0.03
% 1.74/1.13  Demodulation         : 0.02
% 1.74/1.13  BG Simplification    : 0.01
% 1.74/1.13  Subsumption          : 0.01
% 1.74/1.13  Abstraction          : 0.00
% 1.74/1.13  MUC search           : 0.00
% 1.74/1.13  Cooper               : 0.00
% 1.74/1.13  Total                : 0.40
% 1.74/1.13  Index Insertion      : 0.00
% 1.74/1.13  Index Deletion       : 0.00
% 1.77/1.13  Index Matching       : 0.00
% 1.77/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
