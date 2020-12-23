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
% DateTime   : Thu Dec  3 09:46:41 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   25 (  31 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   14 (  20 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_73,plain,(
    ! [A_27,B_28,C_29,D_30] : k2_xboole_0(k2_tarski(A_27,B_28),k2_tarski(C_29,D_30)) = k2_enumset1(A_27,B_28,C_29,D_30) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_156,plain,(
    ! [A_39,B_40,B_41,A_42] : k2_xboole_0(k2_tarski(A_39,B_40),k2_tarski(B_41,A_42)) = k2_enumset1(A_39,B_40,A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_73])).

tff(c_82,plain,(
    ! [B_2,A_1,C_29,D_30] : k2_xboole_0(k2_tarski(B_2,A_1),k2_tarski(C_29,D_30)) = k2_enumset1(A_1,B_2,C_29,D_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_73])).

tff(c_191,plain,(
    ! [B_43,A_44,B_45,A_46] : k2_enumset1(B_43,A_44,B_45,A_46) = k2_enumset1(A_44,B_43,A_46,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_82])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11] : k2_enumset1(A_9,A_9,B_10,C_11) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_262,plain,(
    ! [B_47,B_48,A_49] : k2_enumset1(B_47,B_47,B_48,A_49) = k1_enumset1(B_47,A_49,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_8])).

tff(c_274,plain,(
    ! [B_47,B_48,A_49] : k1_enumset1(B_47,B_48,A_49) = k1_enumset1(B_47,A_49,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_8])).

tff(c_12,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.21  
% 1.86/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.21  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.86/1.21  
% 1.86/1.21  %Foreground sorts:
% 1.86/1.21  
% 1.86/1.21  
% 1.86/1.21  %Background operators:
% 1.86/1.21  
% 1.86/1.21  
% 1.86/1.21  %Foreground operators:
% 1.86/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.86/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.86/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.86/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.86/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.86/1.21  
% 1.86/1.22  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.86/1.22  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 1.86/1.22  tff(f_33, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.86/1.22  tff(f_38, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_enumset1)).
% 1.86/1.22  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.86/1.22  tff(c_73, plain, (![A_27, B_28, C_29, D_30]: (k2_xboole_0(k2_tarski(A_27, B_28), k2_tarski(C_29, D_30))=k2_enumset1(A_27, B_28, C_29, D_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.86/1.22  tff(c_156, plain, (![A_39, B_40, B_41, A_42]: (k2_xboole_0(k2_tarski(A_39, B_40), k2_tarski(B_41, A_42))=k2_enumset1(A_39, B_40, A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_2, c_73])).
% 1.86/1.22  tff(c_82, plain, (![B_2, A_1, C_29, D_30]: (k2_xboole_0(k2_tarski(B_2, A_1), k2_tarski(C_29, D_30))=k2_enumset1(A_1, B_2, C_29, D_30))), inference(superposition, [status(thm), theory('equality')], [c_2, c_73])).
% 1.86/1.22  tff(c_191, plain, (![B_43, A_44, B_45, A_46]: (k2_enumset1(B_43, A_44, B_45, A_46)=k2_enumset1(A_44, B_43, A_46, B_45))), inference(superposition, [status(thm), theory('equality')], [c_156, c_82])).
% 1.86/1.22  tff(c_8, plain, (![A_9, B_10, C_11]: (k2_enumset1(A_9, A_9, B_10, C_11)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.86/1.22  tff(c_262, plain, (![B_47, B_48, A_49]: (k2_enumset1(B_47, B_47, B_48, A_49)=k1_enumset1(B_47, A_49, B_48))), inference(superposition, [status(thm), theory('equality')], [c_191, c_8])).
% 1.86/1.22  tff(c_274, plain, (![B_47, B_48, A_49]: (k1_enumset1(B_47, B_48, A_49)=k1_enumset1(B_47, A_49, B_48))), inference(superposition, [status(thm), theory('equality')], [c_262, c_8])).
% 1.86/1.22  tff(c_12, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.86/1.22  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_274, c_12])).
% 1.86/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.22  
% 1.86/1.22  Inference rules
% 1.86/1.22  ----------------------
% 1.86/1.22  #Ref     : 0
% 1.86/1.22  #Sup     : 74
% 1.86/1.22  #Fact    : 0
% 1.86/1.22  #Define  : 0
% 1.86/1.22  #Split   : 0
% 1.86/1.22  #Chain   : 0
% 1.86/1.22  #Close   : 0
% 1.86/1.22  
% 1.86/1.22  Ordering : KBO
% 1.86/1.22  
% 1.86/1.22  Simplification rules
% 1.86/1.22  ----------------------
% 1.86/1.22  #Subsume      : 1
% 1.86/1.22  #Demod        : 9
% 1.86/1.22  #Tautology    : 46
% 1.86/1.22  #SimpNegUnit  : 0
% 1.86/1.22  #BackRed      : 1
% 1.86/1.22  
% 1.86/1.22  #Partial instantiations: 0
% 1.86/1.22  #Strategies tried      : 1
% 1.86/1.22  
% 1.86/1.22  Timing (in seconds)
% 1.86/1.22  ----------------------
% 1.86/1.22  Preprocessing        : 0.26
% 1.86/1.22  Parsing              : 0.14
% 1.86/1.22  CNF conversion       : 0.01
% 1.86/1.22  Main loop            : 0.17
% 1.86/1.22  Inferencing          : 0.07
% 1.86/1.22  Reduction            : 0.06
% 1.86/1.22  Demodulation         : 0.05
% 1.86/1.22  BG Simplification    : 0.01
% 1.86/1.22  Subsumption          : 0.02
% 1.86/1.22  Abstraction          : 0.01
% 1.86/1.22  MUC search           : 0.00
% 1.86/1.22  Cooper               : 0.00
% 1.86/1.22  Total                : 0.46
% 1.86/1.22  Index Insertion      : 0.00
% 1.86/1.22  Index Deletion       : 0.00
% 1.86/1.22  Index Matching       : 0.00
% 1.86/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
