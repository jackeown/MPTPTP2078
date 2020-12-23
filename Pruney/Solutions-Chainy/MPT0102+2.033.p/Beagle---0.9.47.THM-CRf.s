%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:45 EST 2020

% Result     : Theorem 4.56s
% Output     : CNFRefutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :   42 (  51 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :   31 (  40 expanded)
%              Number of equality atoms :   30 (  39 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_36,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_32,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_30,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_34,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_38,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_43,negated_conjecture,(
    ~ ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(c_12,plain,(
    ! [A_7,B_8,C_9] : k5_xboole_0(k5_xboole_0(A_7,B_8),C_9) = k5_xboole_0(A_7,k5_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_11,B_12] : k5_xboole_0(k5_xboole_0(A_11,B_12),k3_xboole_0(A_11,B_12)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_56,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_71,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_56])).

tff(c_75,plain,(
    ! [A_19] : k4_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_71])).

tff(c_10,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_80,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = k3_xboole_0(A_19,A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_10])).

tff(c_92,plain,(
    ! [A_19] : k3_xboole_0(A_19,A_19) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_80])).

tff(c_4,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_14,plain,(
    ! [A_10] : k5_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_115,plain,(
    ! [A_21,B_22] : k5_xboole_0(k5_xboole_0(A_21,B_22),k3_xboole_0(A_21,B_22)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_136,plain,(
    ! [A_10] : k5_xboole_0(k1_xboole_0,k3_xboole_0(A_10,A_10)) = k2_xboole_0(A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_115])).

tff(c_140,plain,(
    ! [A_10] : k5_xboole_0(k1_xboole_0,A_10) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_4,c_136])).

tff(c_225,plain,(
    ! [A_26,B_27,C_28] : k5_xboole_0(k5_xboole_0(A_26,B_27),C_28) = k5_xboole_0(A_26,k5_xboole_0(B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_285,plain,(
    ! [A_10,C_28] : k5_xboole_0(A_10,k5_xboole_0(A_10,C_28)) = k5_xboole_0(k1_xboole_0,C_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_225])).

tff(c_421,plain,(
    ! [A_32,C_33] : k5_xboole_0(A_32,k5_xboole_0(A_32,C_33)) = C_33 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_285])).

tff(c_1867,plain,(
    ! [A_59,B_60] : k5_xboole_0(k5_xboole_0(A_59,B_60),k2_xboole_0(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_421])).

tff(c_1976,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k5_xboole_0(B_8,k2_xboole_0(A_7,B_8))) = k3_xboole_0(A_7,B_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1867])).

tff(c_18,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_19,plain,(
    k5_xboole_0('#skF_1',k5_xboole_0('#skF_2',k2_xboole_0('#skF_1','#skF_2'))) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18])).

tff(c_4958,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1976,c_19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:25:52 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.56/1.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.97  
% 4.56/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.98  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1
% 4.56/1.98  
% 4.56/1.98  %Foreground sorts:
% 4.56/1.98  
% 4.56/1.98  
% 4.56/1.98  %Background operators:
% 4.56/1.98  
% 4.56/1.98  
% 4.56/1.98  %Foreground operators:
% 4.56/1.98  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 4.56/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.56/1.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.56/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.56/1.98  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.56/1.98  tff('#skF_2', type, '#skF_2': $i).
% 4.56/1.98  tff('#skF_1', type, '#skF_1': $i).
% 4.56/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.56/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.56/1.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.56/1.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.56/1.98  
% 4.56/1.99  tff(f_36, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.56/1.99  tff(f_40, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.56/1.99  tff(f_32, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.56/1.99  tff(f_30, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.56/1.99  tff(f_34, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.56/1.99  tff(f_28, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.56/1.99  tff(f_38, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.56/1.99  tff(f_43, negated_conjecture, ~(![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 4.56/1.99  tff(c_12, plain, (![A_7, B_8, C_9]: (k5_xboole_0(k5_xboole_0(A_7, B_8), C_9)=k5_xboole_0(A_7, k5_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.56/1.99  tff(c_16, plain, (![A_11, B_12]: (k5_xboole_0(k5_xboole_0(A_11, B_12), k3_xboole_0(A_11, B_12))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.56/1.99  tff(c_8, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.56/1.99  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.56/1.99  tff(c_56, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.56/1.99  tff(c_71, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_56])).
% 4.56/1.99  tff(c_75, plain, (![A_19]: (k4_xboole_0(A_19, A_19)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_71])).
% 4.56/1.99  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.56/1.99  tff(c_80, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=k3_xboole_0(A_19, A_19))), inference(superposition, [status(thm), theory('equality')], [c_75, c_10])).
% 4.56/1.99  tff(c_92, plain, (![A_19]: (k3_xboole_0(A_19, A_19)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_80])).
% 4.56/1.99  tff(c_4, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 4.56/1.99  tff(c_14, plain, (![A_10]: (k5_xboole_0(A_10, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.56/1.99  tff(c_115, plain, (![A_21, B_22]: (k5_xboole_0(k5_xboole_0(A_21, B_22), k3_xboole_0(A_21, B_22))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.56/1.99  tff(c_136, plain, (![A_10]: (k5_xboole_0(k1_xboole_0, k3_xboole_0(A_10, A_10))=k2_xboole_0(A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_115])).
% 4.56/1.99  tff(c_140, plain, (![A_10]: (k5_xboole_0(k1_xboole_0, A_10)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_4, c_136])).
% 4.56/1.99  tff(c_225, plain, (![A_26, B_27, C_28]: (k5_xboole_0(k5_xboole_0(A_26, B_27), C_28)=k5_xboole_0(A_26, k5_xboole_0(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.56/1.99  tff(c_285, plain, (![A_10, C_28]: (k5_xboole_0(A_10, k5_xboole_0(A_10, C_28))=k5_xboole_0(k1_xboole_0, C_28))), inference(superposition, [status(thm), theory('equality')], [c_14, c_225])).
% 4.56/1.99  tff(c_421, plain, (![A_32, C_33]: (k5_xboole_0(A_32, k5_xboole_0(A_32, C_33))=C_33)), inference(demodulation, [status(thm), theory('equality')], [c_140, c_285])).
% 4.56/1.99  tff(c_1867, plain, (![A_59, B_60]: (k5_xboole_0(k5_xboole_0(A_59, B_60), k2_xboole_0(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(superposition, [status(thm), theory('equality')], [c_16, c_421])).
% 4.56/1.99  tff(c_1976, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k5_xboole_0(B_8, k2_xboole_0(A_7, B_8)))=k3_xboole_0(A_7, B_8))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1867])).
% 4.56/1.99  tff(c_18, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.56/1.99  tff(c_19, plain, (k5_xboole_0('#skF_1', k5_xboole_0('#skF_2', k2_xboole_0('#skF_1', '#skF_2')))!=k3_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18])).
% 4.56/1.99  tff(c_4958, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1976, c_19])).
% 4.56/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.99  
% 4.56/1.99  Inference rules
% 4.56/1.99  ----------------------
% 4.56/1.99  #Ref     : 0
% 4.56/1.99  #Sup     : 1268
% 4.56/1.99  #Fact    : 0
% 4.56/1.99  #Define  : 0
% 4.56/1.99  #Split   : 0
% 4.56/1.99  #Chain   : 0
% 4.56/1.99  #Close   : 0
% 4.56/1.99  
% 4.56/1.99  Ordering : KBO
% 4.56/1.99  
% 4.56/1.99  Simplification rules
% 4.56/1.99  ----------------------
% 4.56/1.99  #Subsume      : 28
% 4.56/1.99  #Demod        : 1573
% 4.56/1.99  #Tautology    : 590
% 4.56/1.99  #SimpNegUnit  : 0
% 4.56/1.99  #BackRed      : 4
% 4.56/1.99  
% 4.56/1.99  #Partial instantiations: 0
% 4.56/1.99  #Strategies tried      : 1
% 4.56/1.99  
% 4.56/1.99  Timing (in seconds)
% 4.56/1.99  ----------------------
% 4.56/1.99  Preprocessing        : 0.27
% 4.56/1.99  Parsing              : 0.14
% 4.56/1.99  CNF conversion       : 0.01
% 4.56/1.99  Main loop            : 0.95
% 4.56/1.99  Inferencing          : 0.28
% 4.56/1.99  Reduction            : 0.48
% 4.56/1.99  Demodulation         : 0.42
% 4.56/1.99  BG Simplification    : 0.04
% 4.56/1.99  Subsumption          : 0.10
% 4.56/1.99  Abstraction          : 0.06
% 4.56/1.99  MUC search           : 0.00
% 4.56/1.99  Cooper               : 0.00
% 4.56/1.99  Total                : 1.25
% 4.56/1.99  Index Insertion      : 0.00
% 4.56/1.99  Index Deletion       : 0.00
% 4.56/1.99  Index Matching       : 0.00
% 4.56/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
