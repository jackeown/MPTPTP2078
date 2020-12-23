%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:00 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   27 (  46 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   17 (  36 expanded)
%              Number of equality atoms :   16 (  35 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(C,B,A,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    ! [A_17,B_18,C_19,D_20] : k2_xboole_0(k2_tarski(A_17,B_18),k2_tarski(C_19,D_20)) = k2_enumset1(A_17,B_18,C_19,D_20) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_122,plain,(
    ! [A_25,B_26,B_27,A_28] : k2_xboole_0(k2_tarski(A_25,B_26),k2_tarski(B_27,A_28)) = k2_enumset1(A_25,B_26,A_28,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_72])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] : k2_xboole_0(k2_tarski(A_3,B_4),k2_tarski(C_5,D_6)) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_131,plain,(
    ! [A_25,B_26,B_27,A_28] : k2_enumset1(A_25,B_26,B_27,A_28) = k2_enumset1(A_25,B_26,A_28,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_4])).

tff(c_6,plain,(
    ! [A_7,C_9,D_10,B_8] : k2_enumset1(A_7,C_9,D_10,B_8) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [B_21,A_22,C_23,D_24] : k2_xboole_0(k2_tarski(B_21,A_22),k2_tarski(C_23,D_24)) = k2_enumset1(A_22,B_21,C_23,D_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_72])).

tff(c_99,plain,(
    ! [B_21,A_22,C_23,D_24] : k2_enumset1(B_21,A_22,C_23,D_24) = k2_enumset1(A_22,B_21,C_23,D_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_4])).

tff(c_8,plain,(
    k2_enumset1('#skF_3','#skF_2','#skF_1','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_2','#skF_1') != k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_8])).

tff(c_157,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_2','#skF_1') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_99,c_9])).

tff(c_158,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_157])).

tff(c_403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:27:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.40  
% 2.27/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.40  %$ k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.27/1.40  
% 2.27/1.40  %Foreground sorts:
% 2.27/1.40  
% 2.27/1.40  
% 2.27/1.40  %Background operators:
% 2.27/1.40  
% 2.27/1.40  
% 2.27/1.40  %Foreground operators:
% 2.27/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.27/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.27/1.40  
% 2.27/1.41  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.27/1.41  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 2.27/1.41  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 2.27/1.41  tff(f_34, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(C, B, A, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_enumset1)).
% 2.27/1.41  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.27/1.41  tff(c_72, plain, (![A_17, B_18, C_19, D_20]: (k2_xboole_0(k2_tarski(A_17, B_18), k2_tarski(C_19, D_20))=k2_enumset1(A_17, B_18, C_19, D_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.27/1.41  tff(c_122, plain, (![A_25, B_26, B_27, A_28]: (k2_xboole_0(k2_tarski(A_25, B_26), k2_tarski(B_27, A_28))=k2_enumset1(A_25, B_26, A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_2, c_72])).
% 2.27/1.41  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (k2_xboole_0(k2_tarski(A_3, B_4), k2_tarski(C_5, D_6))=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.27/1.41  tff(c_131, plain, (![A_25, B_26, B_27, A_28]: (k2_enumset1(A_25, B_26, B_27, A_28)=k2_enumset1(A_25, B_26, A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_122, c_4])).
% 2.27/1.41  tff(c_6, plain, (![A_7, C_9, D_10, B_8]: (k2_enumset1(A_7, C_9, D_10, B_8)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.41  tff(c_93, plain, (![B_21, A_22, C_23, D_24]: (k2_xboole_0(k2_tarski(B_21, A_22), k2_tarski(C_23, D_24))=k2_enumset1(A_22, B_21, C_23, D_24))), inference(superposition, [status(thm), theory('equality')], [c_2, c_72])).
% 2.27/1.41  tff(c_99, plain, (![B_21, A_22, C_23, D_24]: (k2_enumset1(B_21, A_22, C_23, D_24)=k2_enumset1(A_22, B_21, C_23, D_24))), inference(superposition, [status(thm), theory('equality')], [c_93, c_4])).
% 2.27/1.41  tff(c_8, plain, (k2_enumset1('#skF_3', '#skF_2', '#skF_1', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.27/1.41  tff(c_9, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_2', '#skF_1')!=k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_8])).
% 2.27/1.41  tff(c_157, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_2', '#skF_1')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_99, c_9])).
% 2.27/1.41  tff(c_158, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_157])).
% 2.27/1.41  tff(c_403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_158])).
% 2.27/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.41  
% 2.27/1.41  Inference rules
% 2.27/1.41  ----------------------
% 2.27/1.41  #Ref     : 0
% 2.27/1.41  #Sup     : 112
% 2.27/1.41  #Fact    : 0
% 2.27/1.41  #Define  : 0
% 2.27/1.41  #Split   : 0
% 2.27/1.41  #Chain   : 0
% 2.27/1.41  #Close   : 0
% 2.27/1.41  
% 2.27/1.41  Ordering : KBO
% 2.27/1.41  
% 2.27/1.41  Simplification rules
% 2.27/1.41  ----------------------
% 2.27/1.41  #Subsume      : 20
% 2.27/1.41  #Demod        : 10
% 2.27/1.41  #Tautology    : 46
% 2.27/1.41  #SimpNegUnit  : 0
% 2.27/1.41  #BackRed      : 1
% 2.27/1.41  
% 2.27/1.41  #Partial instantiations: 0
% 2.27/1.41  #Strategies tried      : 1
% 2.27/1.41  
% 2.27/1.41  Timing (in seconds)
% 2.27/1.41  ----------------------
% 2.27/1.41  Preprocessing        : 0.29
% 2.27/1.41  Parsing              : 0.15
% 2.27/1.41  CNF conversion       : 0.02
% 2.27/1.41  Main loop            : 0.25
% 2.27/1.41  Inferencing          : 0.09
% 2.27/1.41  Reduction            : 0.10
% 2.27/1.41  Demodulation         : 0.09
% 2.27/1.41  BG Simplification    : 0.02
% 2.27/1.41  Subsumption          : 0.03
% 2.27/1.41  Abstraction          : 0.01
% 2.27/1.41  MUC search           : 0.00
% 2.27/1.41  Cooper               : 0.00
% 2.27/1.41  Total                : 0.56
% 2.27/1.41  Index Insertion      : 0.00
% 2.27/1.41  Index Deletion       : 0.00
% 2.27/1.41  Index Matching       : 0.00
% 2.27/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
