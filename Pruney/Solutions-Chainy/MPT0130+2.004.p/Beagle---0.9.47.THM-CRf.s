%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:39 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(c_42,plain,(
    ! [A_25,B_26,C_27,D_28] : k2_xboole_0(k1_tarski(A_25),k1_enumset1(B_26,C_27,D_28)) = k2_enumset1(A_25,B_26,C_27,D_28) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_40,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k2_tarski(A_22,B_23),k1_tarski(C_24)) = k1_enumset1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_38,plain,(
    ! [A_19,B_20,C_21] : k2_xboole_0(k1_tarski(A_19),k2_tarski(B_20,C_21)) = k1_enumset1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_136,plain,(
    ! [A_52,B_53,C_54] : k2_xboole_0(k2_xboole_0(A_52,B_53),C_54) = k2_xboole_0(A_52,k2_xboole_0(B_53,C_54)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1407,plain,(
    ! [A_142,B_143,C_144,C_145] : k2_xboole_0(k1_tarski(A_142),k2_xboole_0(k2_tarski(B_143,C_144),C_145)) = k2_xboole_0(k1_enumset1(A_142,B_143,C_144),C_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_136])).

tff(c_1478,plain,(
    ! [A_142,A_22,B_23,C_24] : k2_xboole_0(k1_enumset1(A_142,A_22,B_23),k1_tarski(C_24)) = k2_xboole_0(k1_tarski(A_142),k1_enumset1(A_22,B_23,C_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1407])).

tff(c_1507,plain,(
    ! [A_142,A_22,B_23,C_24] : k2_xboole_0(k1_enumset1(A_142,A_22,B_23),k1_tarski(C_24)) = k2_enumset1(A_142,A_22,B_23,C_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1478])).

tff(c_46,plain,(
    k2_xboole_0(k1_enumset1('#skF_5','#skF_6','#skF_7'),k1_tarski('#skF_8')) != k2_enumset1('#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1507,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:27:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.62  
% 3.25/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.62  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1
% 3.25/1.62  
% 3.25/1.62  %Foreground sorts:
% 3.25/1.62  
% 3.25/1.62  
% 3.25/1.62  %Background operators:
% 3.25/1.62  
% 3.25/1.62  
% 3.25/1.62  %Foreground operators:
% 3.25/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.25/1.62  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.25/1.62  tff('#skF_7', type, '#skF_7': $i).
% 3.25/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.25/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.25/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.25/1.62  tff('#skF_6', type, '#skF_6': $i).
% 3.25/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.25/1.62  tff('#skF_8', type, '#skF_8': $i).
% 3.25/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.25/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.25/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.25/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.25/1.62  
% 3.25/1.63  tff(f_53, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 3.25/1.63  tff(f_51, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 3.25/1.63  tff(f_49, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 3.25/1.63  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.25/1.63  tff(f_58, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 3.25/1.63  tff(c_42, plain, (![A_25, B_26, C_27, D_28]: (k2_xboole_0(k1_tarski(A_25), k1_enumset1(B_26, C_27, D_28))=k2_enumset1(A_25, B_26, C_27, D_28))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.25/1.63  tff(c_40, plain, (![A_22, B_23, C_24]: (k2_xboole_0(k2_tarski(A_22, B_23), k1_tarski(C_24))=k1_enumset1(A_22, B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.25/1.63  tff(c_38, plain, (![A_19, B_20, C_21]: (k2_xboole_0(k1_tarski(A_19), k2_tarski(B_20, C_21))=k1_enumset1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.25/1.63  tff(c_136, plain, (![A_52, B_53, C_54]: (k2_xboole_0(k2_xboole_0(A_52, B_53), C_54)=k2_xboole_0(A_52, k2_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.25/1.63  tff(c_1407, plain, (![A_142, B_143, C_144, C_145]: (k2_xboole_0(k1_tarski(A_142), k2_xboole_0(k2_tarski(B_143, C_144), C_145))=k2_xboole_0(k1_enumset1(A_142, B_143, C_144), C_145))), inference(superposition, [status(thm), theory('equality')], [c_38, c_136])).
% 3.25/1.63  tff(c_1478, plain, (![A_142, A_22, B_23, C_24]: (k2_xboole_0(k1_enumset1(A_142, A_22, B_23), k1_tarski(C_24))=k2_xboole_0(k1_tarski(A_142), k1_enumset1(A_22, B_23, C_24)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1407])).
% 3.25/1.63  tff(c_1507, plain, (![A_142, A_22, B_23, C_24]: (k2_xboole_0(k1_enumset1(A_142, A_22, B_23), k1_tarski(C_24))=k2_enumset1(A_142, A_22, B_23, C_24))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1478])).
% 3.25/1.63  tff(c_46, plain, (k2_xboole_0(k1_enumset1('#skF_5', '#skF_6', '#skF_7'), k1_tarski('#skF_8'))!=k2_enumset1('#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.25/1.63  tff(c_1582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1507, c_46])).
% 3.25/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.63  
% 3.25/1.63  Inference rules
% 3.25/1.63  ----------------------
% 3.25/1.63  #Ref     : 0
% 3.25/1.63  #Sup     : 352
% 3.25/1.63  #Fact    : 0
% 3.25/1.63  #Define  : 0
% 3.25/1.63  #Split   : 0
% 3.25/1.63  #Chain   : 0
% 3.25/1.63  #Close   : 0
% 3.25/1.63  
% 3.25/1.63  Ordering : KBO
% 3.25/1.63  
% 3.25/1.63  Simplification rules
% 3.25/1.63  ----------------------
% 3.25/1.63  #Subsume      : 1
% 3.25/1.63  #Demod        : 434
% 3.25/1.63  #Tautology    : 260
% 3.25/1.63  #SimpNegUnit  : 0
% 3.25/1.63  #BackRed      : 1
% 3.25/1.63  
% 3.25/1.63  #Partial instantiations: 0
% 3.25/1.63  #Strategies tried      : 1
% 3.25/1.63  
% 3.25/1.63  Timing (in seconds)
% 3.25/1.63  ----------------------
% 3.25/1.63  Preprocessing        : 0.31
% 3.25/1.63  Parsing              : 0.17
% 3.25/1.63  CNF conversion       : 0.02
% 3.25/1.63  Main loop            : 0.48
% 3.25/1.63  Inferencing          : 0.19
% 3.25/1.63  Reduction            : 0.19
% 3.25/1.63  Demodulation         : 0.15
% 3.25/1.63  BG Simplification    : 0.02
% 3.25/1.63  Subsumption          : 0.06
% 3.25/1.63  Abstraction          : 0.03
% 3.25/1.63  MUC search           : 0.00
% 3.25/1.63  Cooper               : 0.00
% 3.25/1.63  Total                : 0.82
% 3.25/1.63  Index Insertion      : 0.00
% 3.25/1.63  Index Deletion       : 0.00
% 3.25/1.63  Index Matching       : 0.00
% 3.25/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
