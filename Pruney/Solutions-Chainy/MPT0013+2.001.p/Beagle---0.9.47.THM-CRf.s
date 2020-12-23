%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:29 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   25 (  33 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   18 (  26 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k2_xboole_0(A,C),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_21,plain,(
    ! [B_11,A_12] : k2_xboole_0(B_11,A_12) = k2_xboole_0(A_12,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [A_12] : k2_xboole_0(k1_xboole_0,A_12) = A_12 ),
    inference(superposition,[status(thm),theory(equality)],[c_21,c_4])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_xboole_0(k2_xboole_0(A_4,B_5),C_6) = k2_xboole_0(A_4,k2_xboole_0(B_5,C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] : k2_xboole_0(k2_xboole_0(A_7,C_9),k2_xboole_0(B_8,C_9)) = k2_xboole_0(k2_xboole_0(A_7,B_8),C_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_522,plain,(
    ! [A_25,C_26,B_27] : k2_xboole_0(k2_xboole_0(A_25,C_26),k2_xboole_0(B_27,C_26)) = k2_xboole_0(A_25,k2_xboole_0(B_27,C_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_622,plain,(
    ! [B_27,A_12] : k2_xboole_0(k1_xboole_0,k2_xboole_0(B_27,A_12)) = k2_xboole_0(A_12,k2_xboole_0(B_27,A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_522])).

tff(c_672,plain,(
    ! [A_28,B_29] : k2_xboole_0(A_28,k2_xboole_0(B_29,A_28)) = k2_xboole_0(B_29,A_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_622])).

tff(c_778,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_672])).

tff(c_10,plain,(
    k2_xboole_0('#skF_1',k2_xboole_0('#skF_1','#skF_2')) != k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1242,plain,(
    k2_xboole_0('#skF_2','#skF_1') != k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_778,c_10])).

tff(c_1245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.50  
% 3.12/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.50  %$ k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.12/1.50  
% 3.12/1.50  %Foreground sorts:
% 3.12/1.50  
% 3.12/1.50  
% 3.12/1.50  %Background operators:
% 3.12/1.50  
% 3.12/1.50  
% 3.12/1.50  %Foreground operators:
% 3.12/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.12/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.12/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.12/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.12/1.50  
% 3.12/1.51  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.12/1.51  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.12/1.51  tff(f_31, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.12/1.51  tff(f_33, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_xboole_1)).
% 3.12/1.51  tff(f_36, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 3.12/1.51  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.12/1.51  tff(c_21, plain, (![B_11, A_12]: (k2_xboole_0(B_11, A_12)=k2_xboole_0(A_12, B_11))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.12/1.51  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.12/1.51  tff(c_37, plain, (![A_12]: (k2_xboole_0(k1_xboole_0, A_12)=A_12)), inference(superposition, [status(thm), theory('equality')], [c_21, c_4])).
% 3.12/1.51  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_xboole_0(k2_xboole_0(A_4, B_5), C_6)=k2_xboole_0(A_4, k2_xboole_0(B_5, C_6)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.12/1.51  tff(c_8, plain, (![A_7, C_9, B_8]: (k2_xboole_0(k2_xboole_0(A_7, C_9), k2_xboole_0(B_8, C_9))=k2_xboole_0(k2_xboole_0(A_7, B_8), C_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.12/1.51  tff(c_522, plain, (![A_25, C_26, B_27]: (k2_xboole_0(k2_xboole_0(A_25, C_26), k2_xboole_0(B_27, C_26))=k2_xboole_0(A_25, k2_xboole_0(B_27, C_26)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 3.12/1.51  tff(c_622, plain, (![B_27, A_12]: (k2_xboole_0(k1_xboole_0, k2_xboole_0(B_27, A_12))=k2_xboole_0(A_12, k2_xboole_0(B_27, A_12)))), inference(superposition, [status(thm), theory('equality')], [c_37, c_522])).
% 3.12/1.51  tff(c_672, plain, (![A_28, B_29]: (k2_xboole_0(A_28, k2_xboole_0(B_29, A_28))=k2_xboole_0(B_29, A_28))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_622])).
% 3.12/1.51  tff(c_778, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_672])).
% 3.12/1.51  tff(c_10, plain, (k2_xboole_0('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))!=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.12/1.51  tff(c_1242, plain, (k2_xboole_0('#skF_2', '#skF_1')!=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_778, c_10])).
% 3.12/1.51  tff(c_1245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1242])).
% 3.12/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/1.51  
% 3.12/1.51  Inference rules
% 3.12/1.51  ----------------------
% 3.12/1.51  #Ref     : 0
% 3.12/1.51  #Sup     : 308
% 3.12/1.51  #Fact    : 0
% 3.12/1.51  #Define  : 0
% 3.12/1.51  #Split   : 0
% 3.12/1.51  #Chain   : 0
% 3.12/1.51  #Close   : 0
% 3.12/1.51  
% 3.12/1.51  Ordering : KBO
% 3.12/1.51  
% 3.12/1.51  Simplification rules
% 3.12/1.51  ----------------------
% 3.12/1.51  #Subsume      : 21
% 3.12/1.51  #Demod        : 258
% 3.12/1.51  #Tautology    : 123
% 3.12/1.51  #SimpNegUnit  : 0
% 3.12/1.51  #BackRed      : 1
% 3.12/1.51  
% 3.12/1.51  #Partial instantiations: 0
% 3.12/1.51  #Strategies tried      : 1
% 3.12/1.51  
% 3.12/1.51  Timing (in seconds)
% 3.12/1.51  ----------------------
% 3.12/1.51  Preprocessing        : 0.23
% 3.12/1.51  Parsing              : 0.13
% 3.12/1.51  CNF conversion       : 0.01
% 3.12/1.51  Main loop            : 0.47
% 3.12/1.51  Inferencing          : 0.13
% 3.12/1.51  Reduction            : 0.25
% 3.12/1.51  Demodulation         : 0.23
% 3.12/1.51  BG Simplification    : 0.02
% 3.12/1.51  Subsumption          : 0.04
% 3.12/1.51  Abstraction          : 0.03
% 3.12/1.51  MUC search           : 0.00
% 3.12/1.51  Cooper               : 0.00
% 3.12/1.51  Total                : 0.72
% 3.12/1.51  Index Insertion      : 0.00
% 3.12/1.51  Index Deletion       : 0.00
% 3.12/1.51  Index Matching       : 0.00
% 3.12/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
