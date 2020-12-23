%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:00 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   35 (  54 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  62 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_24,plain,(
    ! [A_9] :
      ( v1_relat_1(A_9)
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_24])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_45,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_54,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_45])).

tff(c_16,plain,(
    ! [A_7] :
      ( k7_relat_1(A_7,k1_relat_1(A_7)) = A_7
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_72,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_16])).

tff(c_76,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_72])).

tff(c_87,plain,(
    ! [C_14,A_15,B_16] :
      ( k7_relat_1(k7_relat_1(C_14,A_15),B_16) = k7_relat_1(C_14,A_15)
      | ~ r1_tarski(A_15,B_16)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_106,plain,(
    ! [B_16] :
      ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(k1_xboole_0,B_16)
      | ~ r1_tarski(k1_xboole_0,B_16)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_87])).

tff(c_118,plain,(
    ! [B_16] : k7_relat_1(k1_xboole_0,B_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4,c_76,c_106])).

tff(c_18,plain,(
    k7_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:18:17 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.13  
% 1.77/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.13  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.77/1.13  
% 1.77/1.13  %Foreground sorts:
% 1.77/1.13  
% 1.77/1.13  
% 1.77/1.13  %Background operators:
% 1.77/1.13  
% 1.77/1.13  
% 1.77/1.13  %Foreground operators:
% 1.77/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.77/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.77/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.77/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.77/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.77/1.13  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.77/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.77/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.77/1.13  
% 1.77/1.14  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.77/1.14  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.77/1.14  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.77/1.14  tff(f_43, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.77/1.14  tff(f_42, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.77/1.14  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 1.77/1.14  tff(f_38, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 1.77/1.14  tff(f_50, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.77/1.14  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.77/1.14  tff(c_24, plain, (![A_9]: (v1_relat_1(A_9) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.77/1.14  tff(c_28, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_24])).
% 1.77/1.14  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.77/1.14  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.77/1.14  tff(c_45, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.77/1.14  tff(c_54, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_14, c_45])).
% 1.77/1.14  tff(c_16, plain, (![A_7]: (k7_relat_1(A_7, k1_relat_1(A_7))=A_7 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.77/1.14  tff(c_72, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_54, c_16])).
% 1.77/1.14  tff(c_76, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_72])).
% 1.77/1.14  tff(c_87, plain, (![C_14, A_15, B_16]: (k7_relat_1(k7_relat_1(C_14, A_15), B_16)=k7_relat_1(C_14, A_15) | ~r1_tarski(A_15, B_16) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.77/1.14  tff(c_106, plain, (![B_16]: (k7_relat_1(k1_xboole_0, k1_xboole_0)=k7_relat_1(k1_xboole_0, B_16) | ~r1_tarski(k1_xboole_0, B_16) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_76, c_87])).
% 1.77/1.14  tff(c_118, plain, (![B_16]: (k7_relat_1(k1_xboole_0, B_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4, c_76, c_106])).
% 1.77/1.14  tff(c_18, plain, (k7_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.77/1.14  tff(c_123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_18])).
% 1.77/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.14  
% 1.77/1.14  Inference rules
% 1.77/1.14  ----------------------
% 1.77/1.14  #Ref     : 0
% 1.77/1.14  #Sup     : 28
% 1.77/1.14  #Fact    : 0
% 1.77/1.14  #Define  : 0
% 1.77/1.14  #Split   : 0
% 1.77/1.14  #Chain   : 0
% 1.77/1.14  #Close   : 0
% 1.77/1.14  
% 1.77/1.14  Ordering : KBO
% 1.77/1.14  
% 1.77/1.14  Simplification rules
% 1.77/1.14  ----------------------
% 1.77/1.14  #Subsume      : 0
% 1.77/1.14  #Demod        : 10
% 1.77/1.14  #Tautology    : 20
% 1.77/1.14  #SimpNegUnit  : 0
% 1.77/1.14  #BackRed      : 1
% 1.77/1.14  
% 1.77/1.14  #Partial instantiations: 0
% 1.77/1.14  #Strategies tried      : 1
% 1.77/1.14  
% 1.77/1.14  Timing (in seconds)
% 1.77/1.14  ----------------------
% 1.77/1.14  Preprocessing        : 0.26
% 1.77/1.14  Parsing              : 0.15
% 1.77/1.14  CNF conversion       : 0.01
% 1.77/1.14  Main loop            : 0.13
% 1.77/1.14  Inferencing          : 0.06
% 1.77/1.14  Reduction            : 0.04
% 1.77/1.14  Demodulation         : 0.03
% 1.77/1.14  BG Simplification    : 0.01
% 1.77/1.14  Subsumption          : 0.01
% 1.77/1.14  Abstraction          : 0.01
% 1.77/1.14  MUC search           : 0.00
% 1.77/1.14  Cooper               : 0.00
% 1.77/1.14  Total                : 0.42
% 1.77/1.14  Index Insertion      : 0.00
% 1.77/1.14  Index Deletion       : 0.00
% 1.77/1.14  Index Matching       : 0.00
% 1.77/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
