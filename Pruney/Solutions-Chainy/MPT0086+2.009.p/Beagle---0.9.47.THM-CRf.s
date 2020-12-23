%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:14 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   38 (  56 expanded)
%              Number of leaves         :   16 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   31 (  49 expanded)
%              Number of equality atoms :   26 (  44 expanded)
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

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_127,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_142,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_127])).

tff(c_146,plain,(
    ! [A_23] : k4_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_142])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_151,plain,(
    ! [A_23] : k4_xboole_0(A_23,k1_xboole_0) = k3_xboole_0(A_23,A_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_12])).

tff(c_163,plain,(
    ! [A_23] : k3_xboole_0(A_23,A_23) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_151])).

tff(c_196,plain,(
    ! [A_25,B_26,C_27] : k4_xboole_0(k3_xboole_0(A_25,B_26),C_27) = k3_xboole_0(A_25,k4_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_220,plain,(
    ! [A_23,C_27] : k3_xboole_0(A_23,k4_xboole_0(A_23,C_27)) = k4_xboole_0(A_23,C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_196])).

tff(c_136,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,k4_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_127])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_145,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_142])).

tff(c_352,plain,(
    ! [A_31,B_32] : k3_xboole_0(A_31,k4_xboole_0(B_32,k3_xboole_0(A_31,B_32))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_196])).

tff(c_387,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k4_xboole_0(B_2,k3_xboole_0(B_2,A_1))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_352])).

tff(c_469,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k3_xboole_0(B_2,k4_xboole_0(B_2,A_1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_387])).

tff(c_527,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k4_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_469])).

tff(c_117,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(A_19,B_20)
      | k3_xboole_0(A_19,B_20) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_123,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_117,c_16])).

tff(c_126,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_123])).

tff(c_587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:06:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.23  
% 2.00/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.23  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.00/1.23  
% 2.00/1.23  %Foreground sorts:
% 2.00/1.23  
% 2.00/1.23  
% 2.00/1.23  %Background operators:
% 2.00/1.23  
% 2.00/1.23  
% 2.00/1.23  %Foreground operators:
% 2.00/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.00/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.00/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.23  
% 2.13/1.24  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.13/1.24  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.13/1.24  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.13/1.24  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.13/1.24  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.13/1.24  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.13/1.24  tff(f_42, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.13/1.24  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.24  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.24  tff(c_127, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.24  tff(c_142, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_127])).
% 2.13/1.24  tff(c_146, plain, (![A_23]: (k4_xboole_0(A_23, A_23)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_142])).
% 2.13/1.24  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.24  tff(c_151, plain, (![A_23]: (k4_xboole_0(A_23, k1_xboole_0)=k3_xboole_0(A_23, A_23))), inference(superposition, [status(thm), theory('equality')], [c_146, c_12])).
% 2.13/1.24  tff(c_163, plain, (![A_23]: (k3_xboole_0(A_23, A_23)=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_151])).
% 2.13/1.24  tff(c_196, plain, (![A_25, B_26, C_27]: (k4_xboole_0(k3_xboole_0(A_25, B_26), C_27)=k3_xboole_0(A_25, k4_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.13/1.24  tff(c_220, plain, (![A_23, C_27]: (k3_xboole_0(A_23, k4_xboole_0(A_23, C_27))=k4_xboole_0(A_23, C_27))), inference(superposition, [status(thm), theory('equality')], [c_163, c_196])).
% 2.13/1.24  tff(c_136, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k3_xboole_0(A_7, k4_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_127])).
% 2.13/1.24  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.13/1.24  tff(c_145, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_142])).
% 2.13/1.24  tff(c_352, plain, (![A_31, B_32]: (k3_xboole_0(A_31, k4_xboole_0(B_32, k3_xboole_0(A_31, B_32)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_145, c_196])).
% 2.13/1.24  tff(c_387, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k4_xboole_0(B_2, k3_xboole_0(B_2, A_1)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_352])).
% 2.13/1.24  tff(c_469, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k3_xboole_0(B_2, k4_xboole_0(B_2, A_1)))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_136, c_387])).
% 2.13/1.24  tff(c_527, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k4_xboole_0(B_2, A_1))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_220, c_469])).
% 2.13/1.24  tff(c_117, plain, (![A_19, B_20]: (r1_xboole_0(A_19, B_20) | k3_xboole_0(A_19, B_20)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.24  tff(c_16, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.13/1.24  tff(c_123, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_117, c_16])).
% 2.13/1.24  tff(c_126, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_123])).
% 2.13/1.24  tff(c_587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_527, c_126])).
% 2.13/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.24  
% 2.13/1.24  Inference rules
% 2.13/1.24  ----------------------
% 2.13/1.24  #Ref     : 0
% 2.13/1.24  #Sup     : 135
% 2.13/1.24  #Fact    : 0
% 2.13/1.24  #Define  : 0
% 2.13/1.24  #Split   : 0
% 2.13/1.24  #Chain   : 0
% 2.13/1.24  #Close   : 0
% 2.13/1.24  
% 2.13/1.25  Ordering : KBO
% 2.13/1.25  
% 2.13/1.25  Simplification rules
% 2.13/1.25  ----------------------
% 2.13/1.25  #Subsume      : 0
% 2.13/1.25  #Demod        : 105
% 2.13/1.25  #Tautology    : 102
% 2.13/1.25  #SimpNegUnit  : 0
% 2.13/1.25  #BackRed      : 4
% 2.13/1.25  
% 2.13/1.25  #Partial instantiations: 0
% 2.13/1.25  #Strategies tried      : 1
% 2.13/1.25  
% 2.13/1.25  Timing (in seconds)
% 2.13/1.25  ----------------------
% 2.13/1.25  Preprocessing        : 0.25
% 2.13/1.25  Parsing              : 0.13
% 2.13/1.25  CNF conversion       : 0.01
% 2.13/1.25  Main loop            : 0.23
% 2.13/1.25  Inferencing          : 0.08
% 2.13/1.25  Reduction            : 0.10
% 2.13/1.25  Demodulation         : 0.08
% 2.13/1.25  BG Simplification    : 0.01
% 2.13/1.25  Subsumption          : 0.03
% 2.13/1.25  Abstraction          : 0.02
% 2.13/1.25  MUC search           : 0.00
% 2.13/1.25  Cooper               : 0.00
% 2.13/1.25  Total                : 0.51
% 2.13/1.25  Index Insertion      : 0.00
% 2.13/1.25  Index Deletion       : 0.00
% 2.13/1.25  Index Matching       : 0.00
% 2.13/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
