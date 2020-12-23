%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:10 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   26 (  28 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   15 (  17 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k2_xboole_0(k1_tarski(A_6),k2_tarski(B_7,C_8)) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_54,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k2_xboole_0(A_23,B_24),C_25) = k2_xboole_0(A_23,k2_xboole_0(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_85,plain,(
    ! [A_26,C_27] : k2_xboole_0(A_26,k2_xboole_0(A_26,C_27)) = k2_xboole_0(A_26,C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_54])).

tff(c_114,plain,(
    ! [A_6,B_7,C_8] : k2_xboole_0(k1_tarski(A_6),k1_enumset1(A_6,B_7,C_8)) = k2_xboole_0(k1_tarski(A_6),k2_tarski(B_7,C_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_85])).

tff(c_669,plain,(
    ! [A_54,B_55,C_56] : k2_xboole_0(k1_tarski(A_54),k1_enumset1(A_54,B_55,C_56)) = k1_enumset1(A_54,B_55,C_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_114])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11,D_12] : k2_xboole_0(k1_tarski(A_9),k1_enumset1(B_10,C_11,D_12)) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_678,plain,(
    ! [A_54,B_55,C_56] : k2_enumset1(A_54,A_54,B_55,C_56) = k1_enumset1(A_54,B_55,C_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_669,c_8])).

tff(c_14,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n009.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:00:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.39  
% 2.57/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.39  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.57/1.39  
% 2.57/1.39  %Foreground sorts:
% 2.57/1.39  
% 2.57/1.39  
% 2.57/1.39  %Background operators:
% 2.57/1.39  
% 2.57/1.39  
% 2.57/1.39  %Foreground operators:
% 2.57/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.57/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.57/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.57/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.57/1.39  
% 2.57/1.40  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.57/1.40  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.57/1.40  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.57/1.40  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.57/1.40  tff(f_40, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.57/1.40  tff(c_6, plain, (![A_6, B_7, C_8]: (k2_xboole_0(k1_tarski(A_6), k2_tarski(B_7, C_8))=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.40  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.57/1.40  tff(c_54, plain, (![A_23, B_24, C_25]: (k2_xboole_0(k2_xboole_0(A_23, B_24), C_25)=k2_xboole_0(A_23, k2_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.57/1.40  tff(c_85, plain, (![A_26, C_27]: (k2_xboole_0(A_26, k2_xboole_0(A_26, C_27))=k2_xboole_0(A_26, C_27))), inference(superposition, [status(thm), theory('equality')], [c_2, c_54])).
% 2.57/1.40  tff(c_114, plain, (![A_6, B_7, C_8]: (k2_xboole_0(k1_tarski(A_6), k1_enumset1(A_6, B_7, C_8))=k2_xboole_0(k1_tarski(A_6), k2_tarski(B_7, C_8)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_85])).
% 2.57/1.40  tff(c_669, plain, (![A_54, B_55, C_56]: (k2_xboole_0(k1_tarski(A_54), k1_enumset1(A_54, B_55, C_56))=k1_enumset1(A_54, B_55, C_56))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_114])).
% 2.57/1.40  tff(c_8, plain, (![A_9, B_10, C_11, D_12]: (k2_xboole_0(k1_tarski(A_9), k1_enumset1(B_10, C_11, D_12))=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.57/1.40  tff(c_678, plain, (![A_54, B_55, C_56]: (k2_enumset1(A_54, A_54, B_55, C_56)=k1_enumset1(A_54, B_55, C_56))), inference(superposition, [status(thm), theory('equality')], [c_669, c_8])).
% 2.57/1.40  tff(c_14, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.57/1.40  tff(c_772, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_678, c_14])).
% 2.57/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.40  
% 2.57/1.40  Inference rules
% 2.57/1.40  ----------------------
% 2.57/1.40  #Ref     : 0
% 2.57/1.40  #Sup     : 178
% 2.57/1.40  #Fact    : 0
% 2.57/1.40  #Define  : 0
% 2.57/1.40  #Split   : 0
% 2.57/1.40  #Chain   : 0
% 2.57/1.40  #Close   : 0
% 2.57/1.40  
% 2.57/1.40  Ordering : KBO
% 2.57/1.40  
% 2.57/1.40  Simplification rules
% 2.57/1.40  ----------------------
% 2.57/1.40  #Subsume      : 9
% 2.57/1.40  #Demod        : 168
% 2.57/1.40  #Tautology    : 113
% 2.57/1.40  #SimpNegUnit  : 0
% 2.57/1.40  #BackRed      : 1
% 2.57/1.40  
% 2.57/1.40  #Partial instantiations: 0
% 2.57/1.40  #Strategies tried      : 1
% 2.57/1.40  
% 2.57/1.40  Timing (in seconds)
% 2.57/1.40  ----------------------
% 2.57/1.41  Preprocessing        : 0.30
% 2.57/1.41  Parsing              : 0.15
% 2.57/1.41  CNF conversion       : 0.02
% 2.57/1.41  Main loop            : 0.31
% 2.57/1.41  Inferencing          : 0.12
% 2.57/1.41  Reduction            : 0.13
% 2.57/1.41  Demodulation         : 0.10
% 2.57/1.41  BG Simplification    : 0.02
% 2.57/1.41  Subsumption          : 0.04
% 2.57/1.41  Abstraction          : 0.03
% 2.57/1.41  MUC search           : 0.00
% 2.57/1.41  Cooper               : 0.00
% 2.57/1.41  Total                : 0.63
% 2.57/1.41  Index Insertion      : 0.00
% 2.57/1.41  Index Deletion       : 0.00
% 2.57/1.41  Index Matching       : 0.00
% 2.57/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
