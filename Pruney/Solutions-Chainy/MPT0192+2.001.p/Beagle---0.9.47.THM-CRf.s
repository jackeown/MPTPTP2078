%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:56 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   28 (  58 expanded)
%              Number of leaves         :   14 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   18 (  48 expanded)
%              Number of equality atoms :   17 (  47 expanded)
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

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,A,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,C,D,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_enumset1)).

tff(c_4,plain,(
    ! [B_4,C_5,A_3,D_6] : k2_enumset1(B_4,C_5,A_3,D_6) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    ! [A_17,B_18,C_19,D_20] : k2_xboole_0(k2_tarski(A_17,B_18),k2_tarski(C_19,D_20)) = k2_enumset1(A_17,B_18,C_19,D_20) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [B_2,A_1,C_19,D_20] : k2_xboole_0(k2_tarski(B_2,A_1),k2_tarski(C_19,D_20)) = k2_enumset1(A_1,B_2,C_19,D_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_72])).

tff(c_122,plain,(
    ! [A_25,B_26,B_27,A_28] : k2_xboole_0(k2_tarski(A_25,B_26),k2_tarski(B_27,A_28)) = k2_enumset1(A_25,B_26,A_28,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_72])).

tff(c_297,plain,(
    ! [B_37,A_38,D_39,C_40] : k2_enumset1(B_37,A_38,D_39,C_40) = k2_enumset1(A_38,B_37,C_40,D_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_122])).

tff(c_387,plain,(
    ! [B_4,C_5,A_3,D_6] : k2_enumset1(B_4,C_5,A_3,D_6) = k2_enumset1(B_4,A_3,D_6,C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_297])).

tff(c_6,plain,(
    ! [A_7,B_8,C_9,D_10] : k2_xboole_0(k2_tarski(A_7,B_8),k2_tarski(C_9,D_10)) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_131,plain,(
    ! [A_25,B_26,B_27,A_28] : k2_enumset1(A_25,B_26,B_27,A_28) = k2_enumset1(A_25,B_26,A_28,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_6])).

tff(c_8,plain,(
    k2_enumset1('#skF_2','#skF_3','#skF_4','#skF_1') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_2','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_214,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') != k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_131,c_9])).

tff(c_215,plain,(
    k2_enumset1('#skF_4','#skF_2','#skF_1','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_4,c_214])).

tff(c_404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:37:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.23  
% 2.23/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.24  %$ k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.23/1.24  
% 2.23/1.24  %Foreground sorts:
% 2.23/1.24  
% 2.23/1.24  
% 2.23/1.24  %Background operators:
% 2.23/1.24  
% 2.23/1.24  
% 2.23/1.24  %Foreground operators:
% 2.23/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.24  
% 2.23/1.25  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, A, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l123_enumset1)).
% 2.23/1.25  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.23/1.25  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 2.23/1.25  tff(f_34, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, C, D, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_enumset1)).
% 2.23/1.25  tff(c_4, plain, (![B_4, C_5, A_3, D_6]: (k2_enumset1(B_4, C_5, A_3, D_6)=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.25  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.23/1.25  tff(c_72, plain, (![A_17, B_18, C_19, D_20]: (k2_xboole_0(k2_tarski(A_17, B_18), k2_tarski(C_19, D_20))=k2_enumset1(A_17, B_18, C_19, D_20))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.25  tff(c_81, plain, (![B_2, A_1, C_19, D_20]: (k2_xboole_0(k2_tarski(B_2, A_1), k2_tarski(C_19, D_20))=k2_enumset1(A_1, B_2, C_19, D_20))), inference(superposition, [status(thm), theory('equality')], [c_2, c_72])).
% 2.23/1.25  tff(c_122, plain, (![A_25, B_26, B_27, A_28]: (k2_xboole_0(k2_tarski(A_25, B_26), k2_tarski(B_27, A_28))=k2_enumset1(A_25, B_26, A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_2, c_72])).
% 2.23/1.25  tff(c_297, plain, (![B_37, A_38, D_39, C_40]: (k2_enumset1(B_37, A_38, D_39, C_40)=k2_enumset1(A_38, B_37, C_40, D_39))), inference(superposition, [status(thm), theory('equality')], [c_81, c_122])).
% 2.23/1.25  tff(c_387, plain, (![B_4, C_5, A_3, D_6]: (k2_enumset1(B_4, C_5, A_3, D_6)=k2_enumset1(B_4, A_3, D_6, C_5))), inference(superposition, [status(thm), theory('equality')], [c_4, c_297])).
% 2.23/1.25  tff(c_6, plain, (![A_7, B_8, C_9, D_10]: (k2_xboole_0(k2_tarski(A_7, B_8), k2_tarski(C_9, D_10))=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.25  tff(c_131, plain, (![A_25, B_26, B_27, A_28]: (k2_enumset1(A_25, B_26, B_27, A_28)=k2_enumset1(A_25, B_26, A_28, B_27))), inference(superposition, [status(thm), theory('equality')], [c_122, c_6])).
% 2.23/1.25  tff(c_8, plain, (k2_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_1')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.23/1.25  tff(c_9, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_2', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8])).
% 2.23/1.25  tff(c_214, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')!=k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_131, c_9])).
% 2.23/1.25  tff(c_215, plain, (k2_enumset1('#skF_4', '#skF_2', '#skF_1', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_4, c_214])).
% 2.23/1.25  tff(c_404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_387, c_215])).
% 2.23/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.25  
% 2.23/1.25  Inference rules
% 2.23/1.25  ----------------------
% 2.23/1.25  #Ref     : 0
% 2.23/1.25  #Sup     : 112
% 2.23/1.25  #Fact    : 0
% 2.23/1.25  #Define  : 0
% 2.23/1.25  #Split   : 0
% 2.23/1.25  #Chain   : 0
% 2.23/1.25  #Close   : 0
% 2.23/1.25  
% 2.23/1.25  Ordering : KBO
% 2.23/1.25  
% 2.23/1.25  Simplification rules
% 2.23/1.25  ----------------------
% 2.23/1.25  #Subsume      : 23
% 2.23/1.25  #Demod        : 10
% 2.23/1.25  #Tautology    : 46
% 2.23/1.25  #SimpNegUnit  : 0
% 2.23/1.25  #BackRed      : 2
% 2.23/1.25  
% 2.23/1.25  #Partial instantiations: 0
% 2.23/1.25  #Strategies tried      : 1
% 2.23/1.25  
% 2.23/1.25  Timing (in seconds)
% 2.23/1.25  ----------------------
% 2.23/1.25  Preprocessing        : 0.24
% 2.23/1.25  Parsing              : 0.12
% 2.23/1.25  CNF conversion       : 0.01
% 2.23/1.25  Main loop            : 0.24
% 2.23/1.25  Inferencing          : 0.08
% 2.23/1.25  Reduction            : 0.10
% 2.23/1.25  Demodulation         : 0.09
% 2.23/1.25  BG Simplification    : 0.01
% 2.23/1.25  Subsumption          : 0.03
% 2.23/1.25  Abstraction          : 0.01
% 2.23/1.25  MUC search           : 0.00
% 2.23/1.25  Cooper               : 0.00
% 2.23/1.25  Total                : 0.50
% 2.23/1.25  Index Insertion      : 0.00
% 2.23/1.25  Index Deletion       : 0.00
% 2.23/1.25  Index Matching       : 0.00
% 2.23/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
