%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:45 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   39 (  53 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  43 expanded)
%              Number of equality atoms :   28 (  42 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_115,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k2_xboole_0(A_22,B_23)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_125,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_115])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k4_xboole_0(k4_xboole_0(A_8,B_9),C_10) = k4_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_274,plain,(
    ! [A_33,B_34] : k2_xboole_0(k4_xboole_0(A_33,B_34),k4_xboole_0(B_34,A_33)) = k5_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1901,plain,(
    ! [B_77,A_78] : k2_xboole_0(k4_xboole_0(B_77,A_78),k4_xboole_0(A_78,B_77)) = k5_xboole_0(A_78,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_274])).

tff(c_2018,plain,(
    ! [A_13,B_14] : k2_xboole_0(k4_xboole_0(k4_xboole_0(A_13,B_14),A_13),k3_xboole_0(A_13,B_14)) = k5_xboole_0(A_13,k4_xboole_0(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1901])).

tff(c_2087,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_125,c_2,c_10,c_2018])).

tff(c_29,plain,(
    ! [B_19,A_20] : k2_xboole_0(B_19,A_20) = k2_xboole_0(A_20,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_45,plain,(
    ! [A_20] : k2_xboole_0(k1_xboole_0,A_20) = A_20 ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_6])).

tff(c_8,plain,(
    ! [A_6,B_7] : k4_xboole_0(k2_xboole_0(A_6,B_7),B_7) = k4_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_307,plain,(
    ! [B_7,A_6] : k2_xboole_0(k4_xboole_0(B_7,k2_xboole_0(A_6,B_7)),k4_xboole_0(A_6,B_7)) = k5_xboole_0(B_7,k2_xboole_0(A_6,B_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_274])).

tff(c_341,plain,(
    ! [B_7,A_6] : k5_xboole_0(B_7,k2_xboole_0(A_6,B_7)) = k4_xboole_0(A_6,B_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_125,c_307])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17] : k5_xboole_0(k5_xboole_0(A_15,B_16),C_17) = k5_xboole_0(A_15,k5_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),k2_xboole_0('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19,plain,(
    k5_xboole_0('#skF_1',k5_xboole_0('#skF_2',k2_xboole_0('#skF_1','#skF_2'))) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_756,plain,(
    k5_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) != k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_19])).

tff(c_2611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2087,c_756])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.56  
% 3.42/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.57  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.42/1.57  
% 3.42/1.57  %Foreground sorts:
% 3.42/1.57  
% 3.42/1.57  
% 3.42/1.57  %Background operators:
% 3.42/1.57  
% 3.42/1.57  
% 3.42/1.57  %Foreground operators:
% 3.42/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.42/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.42/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.42/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.42/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.42/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.42/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.42/1.57  
% 3.42/1.58  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.42/1.58  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.42/1.58  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.42/1.58  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.42/1.58  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.42/1.58  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 3.42/1.58  tff(f_33, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.42/1.58  tff(f_41, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.42/1.58  tff(f_44, negated_conjecture, ~(![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.42/1.58  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.42/1.58  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.42/1.58  tff(c_115, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k2_xboole_0(A_22, B_23))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.42/1.58  tff(c_125, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_115])).
% 3.42/1.58  tff(c_10, plain, (![A_8, B_9, C_10]: (k4_xboole_0(k4_xboole_0(A_8, B_9), C_10)=k4_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.42/1.58  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.42/1.58  tff(c_274, plain, (![A_33, B_34]: (k2_xboole_0(k4_xboole_0(A_33, B_34), k4_xboole_0(B_34, A_33))=k5_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.42/1.58  tff(c_1901, plain, (![B_77, A_78]: (k2_xboole_0(k4_xboole_0(B_77, A_78), k4_xboole_0(A_78, B_77))=k5_xboole_0(A_78, B_77))), inference(superposition, [status(thm), theory('equality')], [c_2, c_274])).
% 3.42/1.58  tff(c_2018, plain, (![A_13, B_14]: (k2_xboole_0(k4_xboole_0(k4_xboole_0(A_13, B_14), A_13), k3_xboole_0(A_13, B_14))=k5_xboole_0(A_13, k4_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1901])).
% 3.42/1.58  tff(c_2087, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_125, c_2, c_10, c_2018])).
% 3.42/1.58  tff(c_29, plain, (![B_19, A_20]: (k2_xboole_0(B_19, A_20)=k2_xboole_0(A_20, B_19))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.42/1.58  tff(c_45, plain, (![A_20]: (k2_xboole_0(k1_xboole_0, A_20)=A_20)), inference(superposition, [status(thm), theory('equality')], [c_29, c_6])).
% 3.42/1.58  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(k2_xboole_0(A_6, B_7), B_7)=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.42/1.58  tff(c_307, plain, (![B_7, A_6]: (k2_xboole_0(k4_xboole_0(B_7, k2_xboole_0(A_6, B_7)), k4_xboole_0(A_6, B_7))=k5_xboole_0(B_7, k2_xboole_0(A_6, B_7)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_274])).
% 3.42/1.58  tff(c_341, plain, (![B_7, A_6]: (k5_xboole_0(B_7, k2_xboole_0(A_6, B_7))=k4_xboole_0(A_6, B_7))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_125, c_307])).
% 3.42/1.58  tff(c_16, plain, (![A_15, B_16, C_17]: (k5_xboole_0(k5_xboole_0(A_15, B_16), C_17)=k5_xboole_0(A_15, k5_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.42/1.58  tff(c_18, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), k2_xboole_0('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.42/1.58  tff(c_19, plain, (k5_xboole_0('#skF_1', k5_xboole_0('#skF_2', k2_xboole_0('#skF_1', '#skF_2')))!=k3_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 3.42/1.58  tff(c_756, plain, (k5_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))!=k3_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_341, c_19])).
% 3.42/1.58  tff(c_2611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2087, c_756])).
% 3.42/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.58  
% 3.42/1.58  Inference rules
% 3.42/1.58  ----------------------
% 3.42/1.58  #Ref     : 0
% 3.42/1.58  #Sup     : 637
% 3.42/1.58  #Fact    : 0
% 3.42/1.58  #Define  : 0
% 3.42/1.58  #Split   : 0
% 3.42/1.58  #Chain   : 0
% 3.42/1.58  #Close   : 0
% 3.42/1.58  
% 3.42/1.58  Ordering : KBO
% 3.42/1.58  
% 3.42/1.58  Simplification rules
% 3.42/1.58  ----------------------
% 3.42/1.58  #Subsume      : 18
% 3.42/1.58  #Demod        : 622
% 3.42/1.58  #Tautology    : 415
% 3.42/1.58  #SimpNegUnit  : 0
% 3.42/1.58  #BackRed      : 2
% 3.42/1.58  
% 3.42/1.58  #Partial instantiations: 0
% 3.42/1.58  #Strategies tried      : 1
% 3.42/1.58  
% 3.42/1.58  Timing (in seconds)
% 3.42/1.58  ----------------------
% 3.64/1.58  Preprocessing        : 0.25
% 3.64/1.58  Parsing              : 0.14
% 3.64/1.58  CNF conversion       : 0.02
% 3.64/1.58  Main loop            : 0.55
% 3.64/1.58  Inferencing          : 0.17
% 3.64/1.58  Reduction            : 0.25
% 3.64/1.58  Demodulation         : 0.21
% 3.64/1.58  BG Simplification    : 0.02
% 3.64/1.58  Subsumption          : 0.07
% 3.64/1.58  Abstraction          : 0.03
% 3.64/1.58  MUC search           : 0.00
% 3.64/1.58  Cooper               : 0.00
% 3.64/1.58  Total                : 0.82
% 3.64/1.58  Index Insertion      : 0.00
% 3.64/1.58  Index Deletion       : 0.00
% 3.64/1.58  Index Matching       : 0.00
% 3.64/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
