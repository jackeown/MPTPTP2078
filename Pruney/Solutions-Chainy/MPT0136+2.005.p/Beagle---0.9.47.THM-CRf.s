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
% DateTime   : Thu Dec  3 09:45:44 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   37 (  49 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   22 (  34 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_tarski(A,B),k2_enumset1(C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_enumset1)).

tff(c_4,plain,(
    ! [B_5,D_7,A_4,E_8,C_6,F_9] : k2_xboole_0(k1_enumset1(A_4,B_5,C_6),k1_enumset1(D_7,E_8,F_9)) = k4_enumset1(A_4,B_5,C_6,D_7,E_8,F_9) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_10,B_11] : k2_xboole_0(k1_tarski(A_10),k1_tarski(B_11)) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_31,plain,(
    ! [A_24,B_25,C_26] : k2_xboole_0(k2_xboole_0(A_24,B_25),C_26) = k2_xboole_0(A_24,k2_xboole_0(B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_49,plain,(
    ! [A_10,B_11,C_26] : k2_xboole_0(k1_tarski(A_10),k2_xboole_0(k1_tarski(B_11),C_26)) = k2_xboole_0(k2_tarski(A_10,B_11),C_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_31])).

tff(c_10,plain,(
    ! [A_15,B_16,C_17,D_18] : k2_xboole_0(k1_tarski(A_15),k1_enumset1(B_16,C_17,D_18)) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    ! [A_31,B_32,C_33] : k2_xboole_0(k1_tarski(A_31),k2_xboole_0(k1_tarski(B_32),C_33)) = k2_xboole_0(k2_tarski(A_31,B_32),C_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_31])).

tff(c_224,plain,(
    ! [B_67,A_66,C_64,D_65,A_68] : k2_xboole_0(k2_tarski(A_66,A_68),k1_enumset1(B_67,C_64,D_65)) = k2_xboole_0(k1_tarski(A_66),k2_enumset1(A_68,B_67,C_64,D_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_66])).

tff(c_8,plain,(
    ! [A_12,B_13,C_14] : k2_xboole_0(k2_tarski(A_12,B_13),k1_tarski(C_14)) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_87,plain,(
    ! [A_31,A_10,B_11] : k2_xboole_0(k2_tarski(A_31,A_10),k1_tarski(B_11)) = k2_xboole_0(k1_tarski(A_31),k2_tarski(A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_66])).

tff(c_92,plain,(
    ! [A_34,A_35,B_36] : k2_xboole_0(k1_tarski(A_34),k2_tarski(A_35,B_36)) = k1_enumset1(A_34,A_35,B_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_87])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_101,plain,(
    ! [A_34,A_35,B_36,C_3] : k2_xboole_0(k1_tarski(A_34),k2_xboole_0(k2_tarski(A_35,B_36),C_3)) = k2_xboole_0(k1_enumset1(A_34,A_35,B_36),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2])).

tff(c_230,plain,(
    ! [B_67,A_66,A_34,C_64,D_65,A_68] : k2_xboole_0(k1_tarski(A_34),k2_xboole_0(k1_tarski(A_66),k2_enumset1(A_68,B_67,C_64,D_65))) = k2_xboole_0(k1_enumset1(A_34,A_66,A_68),k1_enumset1(B_67,C_64,D_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_101])).

tff(c_238,plain,(
    ! [B_67,A_66,A_34,C_64,D_65,A_68] : k2_xboole_0(k2_tarski(A_34,A_66),k2_enumset1(A_68,B_67,C_64,D_65)) = k4_enumset1(A_34,A_66,A_68,B_67,C_64,D_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_49,c_230])).

tff(c_12,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_enumset1('#skF_3','#skF_4','#skF_5','#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.62  
% 2.48/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.63  %$ k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.48/1.63  
% 2.48/1.63  %Foreground sorts:
% 2.48/1.63  
% 2.48/1.63  
% 2.48/1.63  %Background operators:
% 2.48/1.63  
% 2.48/1.63  
% 2.48/1.63  %Foreground operators:
% 2.48/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.48/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.63  tff('#skF_5', type, '#skF_5': $i).
% 2.48/1.63  tff('#skF_6', type, '#skF_6': $i).
% 2.48/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.48/1.63  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.63  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.63  tff('#skF_1', type, '#skF_1': $i).
% 2.48/1.63  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.48/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.63  tff('#skF_4', type, '#skF_4': $i).
% 2.48/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.48/1.63  
% 2.48/1.64  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 2.48/1.64  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.48/1.64  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.48/1.64  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.48/1.64  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 2.48/1.64  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_tarski(A, B), k2_enumset1(C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_enumset1)).
% 2.48/1.64  tff(c_4, plain, (![B_5, D_7, A_4, E_8, C_6, F_9]: (k2_xboole_0(k1_enumset1(A_4, B_5, C_6), k1_enumset1(D_7, E_8, F_9))=k4_enumset1(A_4, B_5, C_6, D_7, E_8, F_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.48/1.64  tff(c_6, plain, (![A_10, B_11]: (k2_xboole_0(k1_tarski(A_10), k1_tarski(B_11))=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.64  tff(c_31, plain, (![A_24, B_25, C_26]: (k2_xboole_0(k2_xboole_0(A_24, B_25), C_26)=k2_xboole_0(A_24, k2_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.48/1.64  tff(c_49, plain, (![A_10, B_11, C_26]: (k2_xboole_0(k1_tarski(A_10), k2_xboole_0(k1_tarski(B_11), C_26))=k2_xboole_0(k2_tarski(A_10, B_11), C_26))), inference(superposition, [status(thm), theory('equality')], [c_6, c_31])).
% 2.48/1.64  tff(c_10, plain, (![A_15, B_16, C_17, D_18]: (k2_xboole_0(k1_tarski(A_15), k1_enumset1(B_16, C_17, D_18))=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.48/1.64  tff(c_66, plain, (![A_31, B_32, C_33]: (k2_xboole_0(k1_tarski(A_31), k2_xboole_0(k1_tarski(B_32), C_33))=k2_xboole_0(k2_tarski(A_31, B_32), C_33))), inference(superposition, [status(thm), theory('equality')], [c_6, c_31])).
% 2.48/1.64  tff(c_224, plain, (![B_67, A_66, C_64, D_65, A_68]: (k2_xboole_0(k2_tarski(A_66, A_68), k1_enumset1(B_67, C_64, D_65))=k2_xboole_0(k1_tarski(A_66), k2_enumset1(A_68, B_67, C_64, D_65)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_66])).
% 2.48/1.64  tff(c_8, plain, (![A_12, B_13, C_14]: (k2_xboole_0(k2_tarski(A_12, B_13), k1_tarski(C_14))=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.48/1.64  tff(c_87, plain, (![A_31, A_10, B_11]: (k2_xboole_0(k2_tarski(A_31, A_10), k1_tarski(B_11))=k2_xboole_0(k1_tarski(A_31), k2_tarski(A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_66])).
% 2.48/1.64  tff(c_92, plain, (![A_34, A_35, B_36]: (k2_xboole_0(k1_tarski(A_34), k2_tarski(A_35, B_36))=k1_enumset1(A_34, A_35, B_36))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_87])).
% 2.48/1.64  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.48/1.64  tff(c_101, plain, (![A_34, A_35, B_36, C_3]: (k2_xboole_0(k1_tarski(A_34), k2_xboole_0(k2_tarski(A_35, B_36), C_3))=k2_xboole_0(k1_enumset1(A_34, A_35, B_36), C_3))), inference(superposition, [status(thm), theory('equality')], [c_92, c_2])).
% 2.48/1.64  tff(c_230, plain, (![B_67, A_66, A_34, C_64, D_65, A_68]: (k2_xboole_0(k1_tarski(A_34), k2_xboole_0(k1_tarski(A_66), k2_enumset1(A_68, B_67, C_64, D_65)))=k2_xboole_0(k1_enumset1(A_34, A_66, A_68), k1_enumset1(B_67, C_64, D_65)))), inference(superposition, [status(thm), theory('equality')], [c_224, c_101])).
% 2.48/1.64  tff(c_238, plain, (![B_67, A_66, A_34, C_64, D_65, A_68]: (k2_xboole_0(k2_tarski(A_34, A_66), k2_enumset1(A_68, B_67, C_64, D_65))=k4_enumset1(A_34, A_66, A_68, B_67, C_64, D_65))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_49, c_230])).
% 2.48/1.64  tff(c_12, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.48/1.64  tff(c_370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_238, c_12])).
% 2.48/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.64  
% 2.48/1.64  Inference rules
% 2.48/1.64  ----------------------
% 2.48/1.64  #Ref     : 0
% 2.48/1.64  #Sup     : 93
% 2.48/1.64  #Fact    : 0
% 2.48/1.64  #Define  : 0
% 2.48/1.64  #Split   : 0
% 2.48/1.64  #Chain   : 0
% 2.48/1.64  #Close   : 0
% 2.48/1.64  
% 2.48/1.64  Ordering : KBO
% 2.48/1.64  
% 2.48/1.64  Simplification rules
% 2.48/1.64  ----------------------
% 2.48/1.64  #Subsume      : 0
% 2.48/1.64  #Demod        : 48
% 2.48/1.64  #Tautology    : 46
% 2.48/1.64  #SimpNegUnit  : 0
% 2.48/1.64  #BackRed      : 1
% 2.48/1.64  
% 2.48/1.64  #Partial instantiations: 0
% 2.48/1.64  #Strategies tried      : 1
% 2.48/1.64  
% 2.48/1.64  Timing (in seconds)
% 2.48/1.64  ----------------------
% 2.48/1.64  Preprocessing        : 0.41
% 2.48/1.64  Parsing              : 0.22
% 2.48/1.64  CNF conversion       : 0.03
% 2.48/1.64  Main loop            : 0.32
% 2.48/1.64  Inferencing          : 0.14
% 2.48/1.64  Reduction            : 0.10
% 2.48/1.64  Demodulation         : 0.08
% 2.48/1.64  BG Simplification    : 0.03
% 2.48/1.64  Subsumption          : 0.04
% 2.48/1.64  Abstraction          : 0.02
% 2.48/1.64  MUC search           : 0.00
% 2.48/1.64  Cooper               : 0.00
% 2.48/1.64  Total                : 0.76
% 2.48/1.64  Index Insertion      : 0.00
% 2.48/1.64  Index Deletion       : 0.00
% 2.48/1.64  Index Matching       : 0.00
% 2.48/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
