%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:45 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   32 (  47 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   20 (  35 expanded)
%              Number of equality atoms :   19 (  34 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

tff(c_8,plain,(
    ! [A_7,B_8] : k1_enumset1(A_7,A_7,B_8) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_24,B_25,C_26] : k2_xboole_0(k2_tarski(A_24,B_25),k1_tarski(C_26)) = k1_enumset1(A_24,B_25,C_26) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_96,plain,(
    ! [A_6,C_26] : k2_xboole_0(k1_tarski(A_6),k1_tarski(C_26)) = k1_enumset1(A_6,A_6,C_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_75])).

tff(c_100,plain,(
    ! [A_27,C_28] : k2_xboole_0(k1_tarski(A_27),k1_tarski(C_28)) = k2_tarski(A_27,C_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_96])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_121,plain,(
    ! [C_29,A_30] : k2_xboole_0(k1_tarski(C_29),k1_tarski(A_30)) = k2_tarski(A_30,C_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_2])).

tff(c_99,plain,(
    ! [A_6,C_26] : k2_xboole_0(k1_tarski(A_6),k1_tarski(C_26)) = k2_tarski(A_6,C_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_96])).

tff(c_127,plain,(
    ! [C_29,A_30] : k2_tarski(C_29,A_30) = k2_tarski(A_30,C_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_99])).

tff(c_203,plain,(
    ! [C_37,A_38,B_39] : k2_xboole_0(k1_tarski(C_37),k2_tarski(A_38,B_39)) = k1_enumset1(A_38,B_39,C_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_75])).

tff(c_241,plain,(
    ! [C_40,C_41,A_42] : k2_xboole_0(k1_tarski(C_40),k2_tarski(C_41,A_42)) = k1_enumset1(A_42,C_41,C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_203])).

tff(c_93,plain,(
    ! [C_26,A_24,B_25] : k2_xboole_0(k1_tarski(C_26),k2_tarski(A_24,B_25)) = k1_enumset1(A_24,B_25,C_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_75])).

tff(c_247,plain,(
    ! [C_41,A_42,C_40] : k1_enumset1(C_41,A_42,C_40) = k1_enumset1(A_42,C_41,C_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_93])).

tff(c_14,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.19  
% 1.78/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.19  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.78/1.19  
% 1.78/1.19  %Foreground sorts:
% 1.78/1.19  
% 1.78/1.19  
% 1.78/1.19  %Background operators:
% 1.78/1.19  
% 1.78/1.19  
% 1.78/1.19  %Foreground operators:
% 1.78/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.78/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.78/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.78/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.78/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.78/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.78/1.19  
% 1.97/1.20  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.97/1.20  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.97/1.20  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 1.97/1.20  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.97/1.20  tff(f_40, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_enumset1)).
% 1.97/1.20  tff(c_8, plain, (![A_7, B_8]: (k1_enumset1(A_7, A_7, B_8)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.97/1.20  tff(c_6, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.20  tff(c_75, plain, (![A_24, B_25, C_26]: (k2_xboole_0(k2_tarski(A_24, B_25), k1_tarski(C_26))=k1_enumset1(A_24, B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.97/1.20  tff(c_96, plain, (![A_6, C_26]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(C_26))=k1_enumset1(A_6, A_6, C_26))), inference(superposition, [status(thm), theory('equality')], [c_6, c_75])).
% 1.97/1.20  tff(c_100, plain, (![A_27, C_28]: (k2_xboole_0(k1_tarski(A_27), k1_tarski(C_28))=k2_tarski(A_27, C_28))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_96])).
% 1.97/1.20  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.97/1.20  tff(c_121, plain, (![C_29, A_30]: (k2_xboole_0(k1_tarski(C_29), k1_tarski(A_30))=k2_tarski(A_30, C_29))), inference(superposition, [status(thm), theory('equality')], [c_100, c_2])).
% 1.97/1.20  tff(c_99, plain, (![A_6, C_26]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(C_26))=k2_tarski(A_6, C_26))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_96])).
% 1.97/1.20  tff(c_127, plain, (![C_29, A_30]: (k2_tarski(C_29, A_30)=k2_tarski(A_30, C_29))), inference(superposition, [status(thm), theory('equality')], [c_121, c_99])).
% 1.97/1.20  tff(c_203, plain, (![C_37, A_38, B_39]: (k2_xboole_0(k1_tarski(C_37), k2_tarski(A_38, B_39))=k1_enumset1(A_38, B_39, C_37))), inference(superposition, [status(thm), theory('equality')], [c_2, c_75])).
% 1.97/1.20  tff(c_241, plain, (![C_40, C_41, A_42]: (k2_xboole_0(k1_tarski(C_40), k2_tarski(C_41, A_42))=k1_enumset1(A_42, C_41, C_40))), inference(superposition, [status(thm), theory('equality')], [c_127, c_203])).
% 1.97/1.20  tff(c_93, plain, (![C_26, A_24, B_25]: (k2_xboole_0(k1_tarski(C_26), k2_tarski(A_24, B_25))=k1_enumset1(A_24, B_25, C_26))), inference(superposition, [status(thm), theory('equality')], [c_2, c_75])).
% 1.97/1.20  tff(c_247, plain, (![C_41, A_42, C_40]: (k1_enumset1(C_41, A_42, C_40)=k1_enumset1(A_42, C_41, C_40))), inference(superposition, [status(thm), theory('equality')], [c_241, c_93])).
% 1.97/1.20  tff(c_14, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.97/1.20  tff(c_325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_247, c_14])).
% 1.97/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.20  
% 1.97/1.20  Inference rules
% 1.97/1.20  ----------------------
% 1.97/1.20  #Ref     : 0
% 1.97/1.20  #Sup     : 78
% 1.97/1.20  #Fact    : 0
% 1.97/1.20  #Define  : 0
% 1.97/1.20  #Split   : 0
% 1.97/1.20  #Chain   : 0
% 1.97/1.20  #Close   : 0
% 1.97/1.20  
% 1.97/1.20  Ordering : KBO
% 1.97/1.20  
% 1.97/1.20  Simplification rules
% 1.97/1.20  ----------------------
% 1.97/1.20  #Subsume      : 3
% 1.97/1.20  #Demod        : 30
% 1.97/1.20  #Tautology    : 59
% 1.97/1.20  #SimpNegUnit  : 0
% 1.97/1.20  #BackRed      : 1
% 1.97/1.20  
% 1.97/1.20  #Partial instantiations: 0
% 1.97/1.20  #Strategies tried      : 1
% 1.97/1.20  
% 1.97/1.20  Timing (in seconds)
% 1.97/1.20  ----------------------
% 1.97/1.20  Preprocessing        : 0.27
% 1.97/1.20  Parsing              : 0.14
% 1.97/1.20  CNF conversion       : 0.01
% 1.97/1.20  Main loop            : 0.17
% 1.97/1.20  Inferencing          : 0.07
% 1.97/1.20  Reduction            : 0.06
% 1.97/1.20  Demodulation         : 0.05
% 1.97/1.20  BG Simplification    : 0.01
% 1.97/1.20  Subsumption          : 0.02
% 1.97/1.20  Abstraction          : 0.01
% 1.97/1.20  MUC search           : 0.00
% 1.97/1.20  Cooper               : 0.00
% 1.97/1.20  Total                : 0.46
% 1.97/1.20  Index Insertion      : 0.00
% 1.97/1.20  Index Deletion       : 0.00
% 1.97/1.20  Index Matching       : 0.00
% 1.97/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
