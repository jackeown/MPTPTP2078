%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:45 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   28 (  29 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   13 (  14 expanded)
%              Number of equality atoms :   12 (  13 expanded)
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

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_tarski(A,B),k2_enumset1(C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

tff(c_12,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23] : k2_xboole_0(k2_tarski(A_19,B_20),k2_enumset1(C_21,D_22,E_23,F_24)) = k4_enumset1(A_19,B_20,C_21,D_22,E_23,F_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : k2_xboole_0(k2_tarski(A_4,B_5),k2_tarski(C_6,D_7)) = k2_enumset1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    ! [A_33,B_34,C_35,D_36] : k2_xboole_0(k2_tarski(A_33,B_34),k2_tarski(C_35,D_36)) = k2_enumset1(A_33,B_34,C_35,D_36) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_217,plain,(
    ! [D_73,C_75,B_74,C_72,A_71] : k2_xboole_0(k2_tarski(A_71,B_74),k2_xboole_0(k2_tarski(C_72,D_73),C_75)) = k2_xboole_0(k2_enumset1(A_71,B_74,C_72,D_73),C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2])).

tff(c_244,plain,(
    ! [B_5,D_7,A_4,B_74,C_6,A_71] : k2_xboole_0(k2_enumset1(A_71,B_74,A_4,B_5),k2_tarski(C_6,D_7)) = k2_xboole_0(k2_tarski(A_71,B_74),k2_enumset1(A_4,B_5,C_6,D_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_217])).

tff(c_251,plain,(
    ! [B_5,D_7,A_4,B_74,C_6,A_71] : k2_xboole_0(k2_enumset1(A_71,B_74,A_4,B_5),k2_tarski(C_6,D_7)) = k4_enumset1(A_71,B_74,A_4,B_5,C_6,D_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_244])).

tff(c_14,plain,(
    k2_xboole_0(k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:55:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.22  
% 2.09/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.22  %$ k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.09/1.22  
% 2.09/1.22  %Foreground sorts:
% 2.09/1.22  
% 2.09/1.22  
% 2.09/1.22  %Background operators:
% 2.09/1.22  
% 2.09/1.22  
% 2.09/1.22  %Foreground operators:
% 2.09/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.22  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.22  tff('#skF_6', type, '#skF_6': $i).
% 2.09/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.22  
% 2.09/1.23  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_tarski(A, B), k2_enumset1(C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_enumset1)).
% 2.09/1.23  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 2.09/1.23  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.09/1.23  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_enumset1)).
% 2.09/1.23  tff(c_12, plain, (![A_19, C_21, D_22, B_20, F_24, E_23]: (k2_xboole_0(k2_tarski(A_19, B_20), k2_enumset1(C_21, D_22, E_23, F_24))=k4_enumset1(A_19, B_20, C_21, D_22, E_23, F_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.23  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k2_xboole_0(k2_tarski(A_4, B_5), k2_tarski(C_6, D_7))=k2_enumset1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.09/1.23  tff(c_56, plain, (![A_33, B_34, C_35, D_36]: (k2_xboole_0(k2_tarski(A_33, B_34), k2_tarski(C_35, D_36))=k2_enumset1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.09/1.23  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.09/1.23  tff(c_217, plain, (![D_73, C_75, B_74, C_72, A_71]: (k2_xboole_0(k2_tarski(A_71, B_74), k2_xboole_0(k2_tarski(C_72, D_73), C_75))=k2_xboole_0(k2_enumset1(A_71, B_74, C_72, D_73), C_75))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2])).
% 2.09/1.23  tff(c_244, plain, (![B_5, D_7, A_4, B_74, C_6, A_71]: (k2_xboole_0(k2_enumset1(A_71, B_74, A_4, B_5), k2_tarski(C_6, D_7))=k2_xboole_0(k2_tarski(A_71, B_74), k2_enumset1(A_4, B_5, C_6, D_7)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_217])).
% 2.09/1.23  tff(c_251, plain, (![B_5, D_7, A_4, B_74, C_6, A_71]: (k2_xboole_0(k2_enumset1(A_71, B_74, A_4, B_5), k2_tarski(C_6, D_7))=k4_enumset1(A_71, B_74, A_4, B_5, C_6, D_7))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_244])).
% 2.09/1.23  tff(c_14, plain, (k2_xboole_0(k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.09/1.23  tff(c_292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_251, c_14])).
% 2.09/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.23  
% 2.09/1.23  Inference rules
% 2.09/1.23  ----------------------
% 2.09/1.23  #Ref     : 0
% 2.09/1.23  #Sup     : 71
% 2.09/1.23  #Fact    : 0
% 2.09/1.23  #Define  : 0
% 2.09/1.23  #Split   : 0
% 2.09/1.23  #Chain   : 0
% 2.09/1.23  #Close   : 0
% 2.09/1.23  
% 2.09/1.23  Ordering : KBO
% 2.09/1.23  
% 2.09/1.23  Simplification rules
% 2.09/1.23  ----------------------
% 2.09/1.23  #Subsume      : 0
% 2.09/1.23  #Demod        : 35
% 2.09/1.23  #Tautology    : 40
% 2.09/1.23  #SimpNegUnit  : 0
% 2.09/1.23  #BackRed      : 1
% 2.09/1.23  
% 2.09/1.23  #Partial instantiations: 0
% 2.09/1.23  #Strategies tried      : 1
% 2.09/1.23  
% 2.09/1.23  Timing (in seconds)
% 2.09/1.23  ----------------------
% 2.22/1.23  Preprocessing        : 0.27
% 2.22/1.23  Parsing              : 0.15
% 2.22/1.23  CNF conversion       : 0.02
% 2.22/1.23  Main loop            : 0.23
% 2.22/1.23  Inferencing          : 0.10
% 2.22/1.23  Reduction            : 0.07
% 2.22/1.23  Demodulation         : 0.06
% 2.22/1.23  BG Simplification    : 0.02
% 2.22/1.23  Subsumption          : 0.03
% 2.22/1.23  Abstraction          : 0.02
% 2.22/1.23  MUC search           : 0.00
% 2.22/1.23  Cooper               : 0.00
% 2.22/1.23  Total                : 0.52
% 2.22/1.23  Index Insertion      : 0.00
% 2.22/1.23  Index Deletion       : 0.00
% 2.22/1.23  Index Matching       : 0.00
% 2.22/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
