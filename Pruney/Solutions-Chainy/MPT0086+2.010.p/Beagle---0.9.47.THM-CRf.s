%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:14 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   40 (  62 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   34 (  59 expanded)
%              Number of equality atoms :   26 (  46 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_60,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_60])).

tff(c_132,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_147,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_132])).

tff(c_151,plain,(
    ! [A_24] : k4_xboole_0(A_24,A_24) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_147])).

tff(c_10,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_156,plain,(
    ! [A_24] : k4_xboole_0(A_24,k1_xboole_0) = k3_xboole_0(A_24,A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_10])).

tff(c_168,plain,(
    ! [A_24] : k3_xboole_0(A_24,A_24) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_156])).

tff(c_201,plain,(
    ! [A_26,B_27,C_28] : k4_xboole_0(k3_xboole_0(A_26,B_27),C_28) = k3_xboole_0(A_26,k4_xboole_0(B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_225,plain,(
    ! [A_24,C_28] : k3_xboole_0(A_24,k4_xboole_0(A_24,C_28)) = k4_xboole_0(A_24,C_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_201])).

tff(c_141,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,k4_xboole_0(A_6,B_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_132])).

tff(c_1555,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = k4_xboole_0(A_6,B_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_141])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_150,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_147])).

tff(c_296,plain,(
    ! [A_30,B_31] : k3_xboole_0(A_30,k4_xboole_0(B_31,k3_xboole_0(A_30,B_31))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_150])).

tff(c_334,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k4_xboole_0(B_2,k3_xboole_0(B_2,A_1))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_296])).

tff(c_1557,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k4_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1555,c_334])).

tff(c_65,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(A_18,B_19)
      | k3_xboole_0(A_18,B_19) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_71,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_65,c_16])).

tff(c_74,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_71])).

tff(c_1687,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1557,c_74])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.46  
% 3.10/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.46  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.10/1.46  
% 3.10/1.46  %Foreground sorts:
% 3.10/1.46  
% 3.10/1.46  
% 3.10/1.46  %Background operators:
% 3.10/1.46  
% 3.10/1.46  
% 3.10/1.46  %Foreground operators:
% 3.10/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.10/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.10/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.10/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.10/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.10/1.46  
% 3.15/1.47  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.15/1.47  tff(f_39, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.15/1.47  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.15/1.47  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.15/1.47  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.15/1.47  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.15/1.47  tff(f_42, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.15/1.47  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.15/1.47  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.15/1.47  tff(c_60, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.15/1.47  tff(c_64, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_60])).
% 3.15/1.47  tff(c_132, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.15/1.47  tff(c_147, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_132])).
% 3.15/1.47  tff(c_151, plain, (![A_24]: (k4_xboole_0(A_24, A_24)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_147])).
% 3.15/1.47  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.15/1.47  tff(c_156, plain, (![A_24]: (k4_xboole_0(A_24, k1_xboole_0)=k3_xboole_0(A_24, A_24))), inference(superposition, [status(thm), theory('equality')], [c_151, c_10])).
% 3.15/1.47  tff(c_168, plain, (![A_24]: (k3_xboole_0(A_24, A_24)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_156])).
% 3.15/1.47  tff(c_201, plain, (![A_26, B_27, C_28]: (k4_xboole_0(k3_xboole_0(A_26, B_27), C_28)=k3_xboole_0(A_26, k4_xboole_0(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.47  tff(c_225, plain, (![A_24, C_28]: (k3_xboole_0(A_24, k4_xboole_0(A_24, C_28))=k4_xboole_0(A_24, C_28))), inference(superposition, [status(thm), theory('equality')], [c_168, c_201])).
% 3.15/1.47  tff(c_141, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k3_xboole_0(A_6, B_7))=k3_xboole_0(A_6, k4_xboole_0(A_6, B_7)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_132])).
% 3.15/1.47  tff(c_1555, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k3_xboole_0(A_6, B_7))=k4_xboole_0(A_6, B_7))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_141])).
% 3.15/1.47  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.47  tff(c_150, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_147])).
% 3.15/1.47  tff(c_296, plain, (![A_30, B_31]: (k3_xboole_0(A_30, k4_xboole_0(B_31, k3_xboole_0(A_30, B_31)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_201, c_150])).
% 3.15/1.47  tff(c_334, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k4_xboole_0(B_2, k3_xboole_0(B_2, A_1)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_296])).
% 3.15/1.47  tff(c_1557, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k4_xboole_0(B_2, A_1))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1555, c_334])).
% 3.15/1.47  tff(c_65, plain, (![A_18, B_19]: (r1_xboole_0(A_18, B_19) | k3_xboole_0(A_18, B_19)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.15/1.47  tff(c_16, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.15/1.47  tff(c_71, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_65, c_16])).
% 3.15/1.47  tff(c_74, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_71])).
% 3.15/1.47  tff(c_1687, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1557, c_74])).
% 3.15/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.47  
% 3.15/1.47  Inference rules
% 3.15/1.47  ----------------------
% 3.15/1.47  #Ref     : 0
% 3.15/1.47  #Sup     : 412
% 3.15/1.47  #Fact    : 0
% 3.15/1.47  #Define  : 0
% 3.15/1.47  #Split   : 0
% 3.15/1.47  #Chain   : 0
% 3.15/1.47  #Close   : 0
% 3.15/1.47  
% 3.15/1.47  Ordering : KBO
% 3.15/1.47  
% 3.15/1.47  Simplification rules
% 3.15/1.47  ----------------------
% 3.15/1.47  #Subsume      : 2
% 3.15/1.47  #Demod        : 487
% 3.15/1.47  #Tautology    : 316
% 3.15/1.47  #SimpNegUnit  : 0
% 3.15/1.47  #BackRed      : 3
% 3.15/1.47  
% 3.15/1.47  #Partial instantiations: 0
% 3.15/1.47  #Strategies tried      : 1
% 3.15/1.47  
% 3.15/1.47  Timing (in seconds)
% 3.15/1.47  ----------------------
% 3.15/1.47  Preprocessing        : 0.27
% 3.15/1.47  Parsing              : 0.15
% 3.15/1.47  CNF conversion       : 0.01
% 3.15/1.47  Main loop            : 0.43
% 3.15/1.47  Inferencing          : 0.13
% 3.15/1.47  Reduction            : 0.21
% 3.15/1.47  Demodulation         : 0.18
% 3.15/1.47  BG Simplification    : 0.02
% 3.15/1.47  Subsumption          : 0.06
% 3.15/1.47  Abstraction          : 0.02
% 3.15/1.47  MUC search           : 0.00
% 3.15/1.47  Cooper               : 0.00
% 3.15/1.47  Total                : 0.73
% 3.15/1.47  Index Insertion      : 0.00
% 3.15/1.47  Index Deletion       : 0.00
% 3.15/1.47  Index Matching       : 0.00
% 3.15/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
