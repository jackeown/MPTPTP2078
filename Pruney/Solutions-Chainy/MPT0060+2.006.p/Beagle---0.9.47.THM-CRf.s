%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:06 EST 2020

% Result     : Theorem 8.41s
% Output     : CNFRefutation 8.41s
% Verified   : 
% Statistics : Number of formulae       :   34 (  47 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   25 (  38 expanded)
%              Number of equality atoms :   24 (  37 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k4_xboole_0(k4_xboole_0(A_5,B_6),C_7) = k4_xboole_0(A_5,k2_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_113,plain,(
    ! [A_22,B_23,C_24] : k4_xboole_0(k4_xboole_0(A_22,B_23),C_24) = k4_xboole_0(A_22,k2_xboole_0(B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_142,plain,(
    ! [A_8,B_9,C_24] : k4_xboole_0(A_8,k2_xboole_0(k3_xboole_0(A_8,B_9),C_24)) = k4_xboole_0(k4_xboole_0(A_8,B_9),C_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_113])).

tff(c_296,plain,(
    ! [A_33,B_34,C_35] : k4_xboole_0(A_33,k2_xboole_0(k3_xboole_0(A_33,B_34),C_35)) = k4_xboole_0(A_33,k2_xboole_0(B_34,C_35)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_142])).

tff(c_350,plain,(
    ! [A_33,A_1,B_34] : k4_xboole_0(A_33,k2_xboole_0(A_1,k3_xboole_0(A_33,B_34))) = k4_xboole_0(A_33,k2_xboole_0(B_34,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_296])).

tff(c_10,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_194,plain,(
    ! [C_27,A_28,B_29] : k2_xboole_0(C_27,k4_xboole_0(A_28,k2_xboole_0(B_29,C_27))) = k2_xboole_0(C_27,k4_xboole_0(A_28,B_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_4])).

tff(c_216,plain,(
    ! [B_2,A_28,A_1] : k2_xboole_0(B_2,k4_xboole_0(A_28,k2_xboole_0(B_2,A_1))) = k2_xboole_0(B_2,k4_xboole_0(A_28,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_194])).

tff(c_133,plain,(
    ! [A_22,B_23,B_11] : k4_xboole_0(A_22,k2_xboole_0(B_23,k4_xboole_0(k4_xboole_0(A_22,B_23),B_11))) = k3_xboole_0(k4_xboole_0(A_22,B_23),B_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_10])).

tff(c_157,plain,(
    ! [A_22,B_23,B_11] : k4_xboole_0(A_22,k2_xboole_0(B_23,k4_xboole_0(A_22,k2_xboole_0(B_23,B_11)))) = k3_xboole_0(k4_xboole_0(A_22,B_23),B_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_133])).

tff(c_2874,plain,(
    ! [A_85,B_86,B_87] : k4_xboole_0(A_85,k2_xboole_0(B_86,k4_xboole_0(A_85,B_87))) = k3_xboole_0(k4_xboole_0(A_85,B_86),B_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_157])).

tff(c_3038,plain,(
    ! [A_10,B_86,B_11] : k4_xboole_0(A_10,k2_xboole_0(B_86,k3_xboole_0(A_10,B_11))) = k3_xboole_0(k4_xboole_0(A_10,B_86),k4_xboole_0(A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2874])).

tff(c_3078,plain,(
    ! [A_10,B_86,B_11] : k3_xboole_0(k4_xboole_0(A_10,B_86),k4_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,k2_xboole_0(B_11,B_86)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_3038])).

tff(c_12,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_3')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13,plain,(
    k3_xboole_0(k4_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_3')) != k4_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_8759,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3078,c_13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:50:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.41/3.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.41/3.16  
% 8.41/3.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.41/3.16  %$ k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 8.41/3.16  
% 8.41/3.16  %Foreground sorts:
% 8.41/3.16  
% 8.41/3.16  
% 8.41/3.16  %Background operators:
% 8.41/3.16  
% 8.41/3.16  
% 8.41/3.16  %Foreground operators:
% 8.41/3.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.41/3.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.41/3.16  tff('#skF_2', type, '#skF_2': $i).
% 8.41/3.16  tff('#skF_3', type, '#skF_3': $i).
% 8.41/3.16  tff('#skF_1', type, '#skF_1': $i).
% 8.41/3.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.41/3.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.41/3.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.41/3.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.41/3.16  
% 8.41/3.17  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.41/3.17  tff(f_31, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 8.41/3.17  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.41/3.17  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.41/3.17  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.41/3.17  tff(f_38, negated_conjecture, ~(![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_xboole_1)).
% 8.41/3.17  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.41/3.17  tff(c_6, plain, (![A_5, B_6, C_7]: (k4_xboole_0(k4_xboole_0(A_5, B_6), C_7)=k4_xboole_0(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.41/3.17  tff(c_8, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.41/3.17  tff(c_113, plain, (![A_22, B_23, C_24]: (k4_xboole_0(k4_xboole_0(A_22, B_23), C_24)=k4_xboole_0(A_22, k2_xboole_0(B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.41/3.17  tff(c_142, plain, (![A_8, B_9, C_24]: (k4_xboole_0(A_8, k2_xboole_0(k3_xboole_0(A_8, B_9), C_24))=k4_xboole_0(k4_xboole_0(A_8, B_9), C_24))), inference(superposition, [status(thm), theory('equality')], [c_8, c_113])).
% 8.41/3.17  tff(c_296, plain, (![A_33, B_34, C_35]: (k4_xboole_0(A_33, k2_xboole_0(k3_xboole_0(A_33, B_34), C_35))=k4_xboole_0(A_33, k2_xboole_0(B_34, C_35)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_142])).
% 8.41/3.17  tff(c_350, plain, (![A_33, A_1, B_34]: (k4_xboole_0(A_33, k2_xboole_0(A_1, k3_xboole_0(A_33, B_34)))=k4_xboole_0(A_33, k2_xboole_0(B_34, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_296])).
% 8.41/3.17  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.41/3.17  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.41/3.17  tff(c_194, plain, (![C_27, A_28, B_29]: (k2_xboole_0(C_27, k4_xboole_0(A_28, k2_xboole_0(B_29, C_27)))=k2_xboole_0(C_27, k4_xboole_0(A_28, B_29)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_4])).
% 8.41/3.17  tff(c_216, plain, (![B_2, A_28, A_1]: (k2_xboole_0(B_2, k4_xboole_0(A_28, k2_xboole_0(B_2, A_1)))=k2_xboole_0(B_2, k4_xboole_0(A_28, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_194])).
% 8.41/3.17  tff(c_133, plain, (![A_22, B_23, B_11]: (k4_xboole_0(A_22, k2_xboole_0(B_23, k4_xboole_0(k4_xboole_0(A_22, B_23), B_11)))=k3_xboole_0(k4_xboole_0(A_22, B_23), B_11))), inference(superposition, [status(thm), theory('equality')], [c_113, c_10])).
% 8.41/3.17  tff(c_157, plain, (![A_22, B_23, B_11]: (k4_xboole_0(A_22, k2_xboole_0(B_23, k4_xboole_0(A_22, k2_xboole_0(B_23, B_11))))=k3_xboole_0(k4_xboole_0(A_22, B_23), B_11))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_133])).
% 8.41/3.17  tff(c_2874, plain, (![A_85, B_86, B_87]: (k4_xboole_0(A_85, k2_xboole_0(B_86, k4_xboole_0(A_85, B_87)))=k3_xboole_0(k4_xboole_0(A_85, B_86), B_87))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_157])).
% 8.41/3.17  tff(c_3038, plain, (![A_10, B_86, B_11]: (k4_xboole_0(A_10, k2_xboole_0(B_86, k3_xboole_0(A_10, B_11)))=k3_xboole_0(k4_xboole_0(A_10, B_86), k4_xboole_0(A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2874])).
% 8.41/3.17  tff(c_3078, plain, (![A_10, B_86, B_11]: (k3_xboole_0(k4_xboole_0(A_10, B_86), k4_xboole_0(A_10, B_11))=k4_xboole_0(A_10, k2_xboole_0(B_11, B_86)))), inference(demodulation, [status(thm), theory('equality')], [c_350, c_3038])).
% 8.41/3.17  tff(c_12, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.41/3.17  tff(c_13, plain, (k3_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 8.41/3.17  tff(c_8759, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3078, c_13])).
% 8.41/3.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.41/3.17  
% 8.41/3.17  Inference rules
% 8.41/3.17  ----------------------
% 8.41/3.17  #Ref     : 0
% 8.41/3.17  #Sup     : 2264
% 8.41/3.17  #Fact    : 0
% 8.41/3.17  #Define  : 0
% 8.41/3.17  #Split   : 0
% 8.41/3.17  #Chain   : 0
% 8.41/3.17  #Close   : 0
% 8.41/3.17  
% 8.41/3.17  Ordering : KBO
% 8.41/3.17  
% 8.41/3.17  Simplification rules
% 8.41/3.17  ----------------------
% 8.41/3.17  #Subsume      : 101
% 8.41/3.17  #Demod        : 1957
% 8.41/3.17  #Tautology    : 417
% 8.41/3.17  #SimpNegUnit  : 0
% 8.41/3.17  #BackRed      : 5
% 8.41/3.17  
% 8.41/3.17  #Partial instantiations: 0
% 8.41/3.17  #Strategies tried      : 1
% 8.41/3.17  
% 8.41/3.17  Timing (in seconds)
% 8.41/3.17  ----------------------
% 8.41/3.17  Preprocessing        : 0.25
% 8.41/3.17  Parsing              : 0.13
% 8.41/3.17  CNF conversion       : 0.01
% 8.41/3.17  Main loop            : 2.18
% 8.41/3.17  Inferencing          : 0.49
% 8.41/3.17  Reduction            : 1.28
% 8.41/3.17  Demodulation         : 1.15
% 8.41/3.18  BG Simplification    : 0.09
% 8.41/3.18  Subsumption          : 0.24
% 8.41/3.18  Abstraction          : 0.14
% 8.41/3.18  MUC search           : 0.00
% 8.41/3.18  Cooper               : 0.00
% 8.41/3.18  Total                : 2.45
% 8.41/3.18  Index Insertion      : 0.00
% 8.41/3.18  Index Deletion       : 0.00
% 8.41/3.18  Index Matching       : 0.00
% 8.41/3.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
