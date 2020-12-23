%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:16 EST 2020

% Result     : Theorem 4.46s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :   39 (  63 expanded)
%              Number of leaves         :   17 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   32 (  59 expanded)
%              Number of equality atoms :   24 (  46 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_6,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_27,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_27])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_61,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_79,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_61])).

tff(c_130,plain,(
    ! [A_26] : k4_xboole_0(A_26,A_26) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_79])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] : k4_xboole_0(k4_xboole_0(A_6,B_7),C_8) = k4_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_139,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k2_xboole_0(B_7,k4_xboole_0(A_6,B_7))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_10])).

tff(c_161,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k2_xboole_0(B_7,A_6)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_139])).

tff(c_83,plain,(
    ! [A_23,B_24,C_25] : k4_xboole_0(k4_xboole_0(A_23,B_24),C_25) = k4_xboole_0(A_23,k2_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_103,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k2_xboole_0(B_24,k1_xboole_0)) = k4_xboole_0(A_23,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_8])).

tff(c_145,plain,(
    ! [A_26] : k2_xboole_0(A_26,k1_xboole_0) = k2_xboole_0(A_26,A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_6])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5589,plain,(
    ! [A_117,B_118,C_119] : k4_xboole_0(k4_xboole_0(A_117,B_118),k4_xboole_0(A_117,k2_xboole_0(B_118,C_119))) = k3_xboole_0(k4_xboole_0(A_117,B_118),C_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_12])).

tff(c_5841,plain,(
    ! [A_117,A_26] : k4_xboole_0(k4_xboole_0(A_117,A_26),k4_xboole_0(A_117,k2_xboole_0(A_26,k1_xboole_0))) = k3_xboole_0(k4_xboole_0(A_117,A_26),A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_5589])).

tff(c_5951,plain,(
    ! [A_117,A_26] : k3_xboole_0(k4_xboole_0(A_117,A_26),A_26) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_6,c_10,c_103,c_5841])).

tff(c_39,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k3_xboole_0(A_17,B_18) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_47,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_39,c_16])).

tff(c_5964,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5951,c_47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.46/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.91  
% 4.68/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.91  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 4.68/1.91  
% 4.68/1.91  %Foreground sorts:
% 4.68/1.91  
% 4.68/1.91  
% 4.68/1.91  %Background operators:
% 4.68/1.91  
% 4.68/1.91  
% 4.68/1.91  %Foreground operators:
% 4.68/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.68/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.68/1.91  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.68/1.91  tff('#skF_2', type, '#skF_2': $i).
% 4.68/1.91  tff('#skF_1', type, '#skF_1': $i).
% 4.68/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.68/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.68/1.91  
% 4.68/1.92  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.68/1.92  tff(f_39, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.68/1.92  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.68/1.92  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.68/1.92  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.68/1.92  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.68/1.92  tff(f_42, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.68/1.92  tff(c_6, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.68/1.92  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.68/1.92  tff(c_27, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.68/1.92  tff(c_31, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_27])).
% 4.68/1.92  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.68/1.92  tff(c_61, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.68/1.92  tff(c_79, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_61])).
% 4.68/1.92  tff(c_130, plain, (![A_26]: (k4_xboole_0(A_26, A_26)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_31, c_79])).
% 4.68/1.92  tff(c_10, plain, (![A_6, B_7, C_8]: (k4_xboole_0(k4_xboole_0(A_6, B_7), C_8)=k4_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.68/1.92  tff(c_139, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k2_xboole_0(B_7, k4_xboole_0(A_6, B_7)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_130, c_10])).
% 4.68/1.92  tff(c_161, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k2_xboole_0(B_7, A_6))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_139])).
% 4.68/1.92  tff(c_83, plain, (![A_23, B_24, C_25]: (k4_xboole_0(k4_xboole_0(A_23, B_24), C_25)=k4_xboole_0(A_23, k2_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.68/1.92  tff(c_103, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k2_xboole_0(B_24, k1_xboole_0))=k4_xboole_0(A_23, B_24))), inference(superposition, [status(thm), theory('equality')], [c_83, c_8])).
% 4.68/1.92  tff(c_145, plain, (![A_26]: (k2_xboole_0(A_26, k1_xboole_0)=k2_xboole_0(A_26, A_26))), inference(superposition, [status(thm), theory('equality')], [c_130, c_6])).
% 4.68/1.92  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.68/1.92  tff(c_5589, plain, (![A_117, B_118, C_119]: (k4_xboole_0(k4_xboole_0(A_117, B_118), k4_xboole_0(A_117, k2_xboole_0(B_118, C_119)))=k3_xboole_0(k4_xboole_0(A_117, B_118), C_119))), inference(superposition, [status(thm), theory('equality')], [c_83, c_12])).
% 4.68/1.92  tff(c_5841, plain, (![A_117, A_26]: (k4_xboole_0(k4_xboole_0(A_117, A_26), k4_xboole_0(A_117, k2_xboole_0(A_26, k1_xboole_0)))=k3_xboole_0(k4_xboole_0(A_117, A_26), A_26))), inference(superposition, [status(thm), theory('equality')], [c_145, c_5589])).
% 4.68/1.92  tff(c_5951, plain, (![A_117, A_26]: (k3_xboole_0(k4_xboole_0(A_117, A_26), A_26)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_161, c_6, c_10, c_103, c_5841])).
% 4.68/1.92  tff(c_39, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k3_xboole_0(A_17, B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.68/1.92  tff(c_16, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.68/1.92  tff(c_47, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_39, c_16])).
% 4.68/1.92  tff(c_5964, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5951, c_47])).
% 4.68/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.68/1.92  
% 4.68/1.92  Inference rules
% 4.68/1.92  ----------------------
% 4.68/1.92  #Ref     : 0
% 4.68/1.92  #Sup     : 1433
% 4.68/1.92  #Fact    : 0
% 4.68/1.92  #Define  : 0
% 4.68/1.92  #Split   : 0
% 4.68/1.92  #Chain   : 0
% 4.68/1.92  #Close   : 0
% 4.68/1.92  
% 4.68/1.92  Ordering : KBO
% 4.68/1.92  
% 4.68/1.92  Simplification rules
% 4.68/1.92  ----------------------
% 4.68/1.92  #Subsume      : 9
% 4.68/1.92  #Demod        : 1300
% 4.68/1.92  #Tautology    : 924
% 4.68/1.92  #SimpNegUnit  : 0
% 4.68/1.92  #BackRed      : 1
% 4.68/1.92  
% 4.68/1.92  #Partial instantiations: 0
% 4.68/1.92  #Strategies tried      : 1
% 4.68/1.92  
% 4.68/1.92  Timing (in seconds)
% 4.68/1.92  ----------------------
% 4.68/1.92  Preprocessing        : 0.24
% 4.68/1.92  Parsing              : 0.13
% 4.68/1.92  CNF conversion       : 0.01
% 4.68/1.92  Main loop            : 0.85
% 4.68/1.92  Inferencing          : 0.28
% 4.68/1.92  Reduction            : 0.37
% 4.68/1.92  Demodulation         : 0.31
% 4.68/1.92  BG Simplification    : 0.03
% 4.68/1.92  Subsumption          : 0.13
% 4.68/1.92  Abstraction          : 0.05
% 4.68/1.92  MUC search           : 0.00
% 4.68/1.92  Cooper               : 0.00
% 4.68/1.92  Total                : 1.12
% 4.68/1.92  Index Insertion      : 0.00
% 4.68/1.92  Index Deletion       : 0.00
% 4.68/1.92  Index Matching       : 0.00
% 4.68/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
