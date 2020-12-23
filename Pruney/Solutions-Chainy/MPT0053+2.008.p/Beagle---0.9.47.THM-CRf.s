%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:51 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   29 (  34 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :   21 (  26 expanded)
%              Number of equality atoms :   20 (  25 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(c_10,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [A_14,B_15] : k4_xboole_0(k2_xboole_0(A_14,B_15),B_15) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = k2_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_4])).

tff(c_133,plain,(
    ! [A_19] : k2_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_79])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_161,plain,(
    ! [A_20] : k2_xboole_0(k1_xboole_0,A_20) = A_20 ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_2])).

tff(c_6,plain,(
    ! [A_4,B_5] : k4_xboole_0(k2_xboole_0(A_4,B_5),B_5) = k4_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_171,plain,(
    ! [A_20] : k4_xboole_0(k1_xboole_0,A_20) = k4_xboole_0(A_20,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_6])).

tff(c_205,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_171])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k4_xboole_0(k4_xboole_0(A_6,B_7),C_8) = k4_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_210,plain,(
    ! [A_21,C_8] : k4_xboole_0(A_21,k2_xboole_0(A_21,C_8)) = k4_xboole_0(k1_xboole_0,C_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_8])).

tff(c_236,plain,(
    ! [A_21,C_8] : k4_xboole_0(A_21,k2_xboole_0(A_21,C_8)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_210])).

tff(c_12,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.13  
% 1.77/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.13  %$ k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.77/1.13  
% 1.77/1.13  %Foreground sorts:
% 1.77/1.13  
% 1.77/1.13  
% 1.77/1.13  %Background operators:
% 1.77/1.13  
% 1.77/1.13  
% 1.77/1.13  %Foreground operators:
% 1.77/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.77/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.77/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.77/1.13  
% 1.77/1.14  tff(f_35, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.77/1.14  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.77/1.14  tff(f_31, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.77/1.14  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.77/1.14  tff(f_33, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 1.77/1.14  tff(f_38, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.77/1.14  tff(c_10, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.77/1.14  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.77/1.14  tff(c_72, plain, (![A_14, B_15]: (k4_xboole_0(k2_xboole_0(A_14, B_15), B_15)=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.77/1.14  tff(c_79, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=k2_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_72, c_4])).
% 1.77/1.14  tff(c_133, plain, (![A_19]: (k2_xboole_0(A_19, k1_xboole_0)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_79])).
% 1.77/1.14  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.77/1.14  tff(c_161, plain, (![A_20]: (k2_xboole_0(k1_xboole_0, A_20)=A_20)), inference(superposition, [status(thm), theory('equality')], [c_133, c_2])).
% 1.77/1.14  tff(c_6, plain, (![A_4, B_5]: (k4_xboole_0(k2_xboole_0(A_4, B_5), B_5)=k4_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.77/1.14  tff(c_171, plain, (![A_20]: (k4_xboole_0(k1_xboole_0, A_20)=k4_xboole_0(A_20, A_20))), inference(superposition, [status(thm), theory('equality')], [c_161, c_6])).
% 1.77/1.14  tff(c_205, plain, (![A_21]: (k4_xboole_0(A_21, A_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_171])).
% 1.77/1.14  tff(c_8, plain, (![A_6, B_7, C_8]: (k4_xboole_0(k4_xboole_0(A_6, B_7), C_8)=k4_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.77/1.14  tff(c_210, plain, (![A_21, C_8]: (k4_xboole_0(A_21, k2_xboole_0(A_21, C_8))=k4_xboole_0(k1_xboole_0, C_8))), inference(superposition, [status(thm), theory('equality')], [c_205, c_8])).
% 1.77/1.14  tff(c_236, plain, (![A_21, C_8]: (k4_xboole_0(A_21, k2_xboole_0(A_21, C_8))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_210])).
% 1.77/1.14  tff(c_12, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.77/1.14  tff(c_244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_236, c_12])).
% 1.77/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.14  
% 1.77/1.14  Inference rules
% 1.77/1.14  ----------------------
% 1.77/1.14  #Ref     : 0
% 1.77/1.14  #Sup     : 54
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
% 1.77/1.14  #Demod        : 22
% 1.77/1.14  #Tautology    : 40
% 1.77/1.14  #SimpNegUnit  : 0
% 1.77/1.14  #BackRed      : 1
% 1.77/1.14  
% 1.77/1.14  #Partial instantiations: 0
% 1.77/1.14  #Strategies tried      : 1
% 1.77/1.14  
% 1.77/1.14  Timing (in seconds)
% 1.77/1.14  ----------------------
% 1.77/1.14  Preprocessing        : 0.24
% 1.77/1.14  Parsing              : 0.14
% 1.77/1.14  CNF conversion       : 0.01
% 1.77/1.14  Main loop            : 0.14
% 1.77/1.14  Inferencing          : 0.05
% 1.77/1.14  Reduction            : 0.06
% 1.77/1.14  Demodulation         : 0.05
% 1.77/1.14  BG Simplification    : 0.01
% 1.77/1.14  Subsumption          : 0.02
% 1.77/1.14  Abstraction          : 0.01
% 1.77/1.14  MUC search           : 0.00
% 1.77/1.14  Cooper               : 0.00
% 1.77/1.14  Total                : 0.41
% 1.77/1.14  Index Insertion      : 0.00
% 1.77/1.14  Index Deletion       : 0.00
% 1.77/1.14  Index Matching       : 0.00
% 1.77/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
