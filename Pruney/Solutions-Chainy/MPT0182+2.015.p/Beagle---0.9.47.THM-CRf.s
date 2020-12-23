%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:44 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   32 (  41 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   20 (  29 expanded)
%              Number of equality atoms :   19 (  28 expanded)
%              Maximal formula depth    :    7 (   4 average)
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

tff(f_39,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

tff(c_14,plain,(
    ! [A_17,C_19,B_18] : k1_enumset1(A_17,C_19,B_18) = k1_enumset1(A_17,B_18,C_19) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] : k2_enumset1(A_10,A_10,B_11,C_12) = k1_enumset1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_174,plain,(
    ! [A_37,B_38,C_39,D_40] : k2_xboole_0(k1_enumset1(A_37,B_38,C_39),k1_tarski(D_40)) = k2_enumset1(A_37,B_38,C_39,D_40) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_192,plain,(
    ! [A_8,B_9,D_40] : k2_xboole_0(k2_tarski(A_8,B_9),k1_tarski(D_40)) = k2_enumset1(A_8,A_8,B_9,D_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_174])).

tff(c_196,plain,(
    ! [A_41,B_42,D_43] : k2_xboole_0(k2_tarski(A_41,B_42),k1_tarski(D_43)) = k1_enumset1(A_41,B_42,D_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_192])).

tff(c_224,plain,(
    ! [A_46,B_47,D_48] : k2_xboole_0(k2_tarski(A_46,B_47),k1_tarski(D_48)) = k1_enumset1(B_47,A_46,D_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_196])).

tff(c_195,plain,(
    ! [A_8,B_9,D_40] : k2_xboole_0(k2_tarski(A_8,B_9),k1_tarski(D_40)) = k1_enumset1(A_8,B_9,D_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_192])).

tff(c_230,plain,(
    ! [B_47,A_46,D_48] : k1_enumset1(B_47,A_46,D_48) = k1_enumset1(A_46,B_47,D_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_195])).

tff(c_16,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_17,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_282,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_17])).

tff(c_285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n023.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 10:17:05 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.31  
% 1.80/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.31  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.80/1.31  
% 1.80/1.31  %Foreground sorts:
% 1.80/1.31  
% 1.80/1.31  
% 1.80/1.31  %Background operators:
% 1.80/1.31  
% 1.80/1.31  
% 1.80/1.31  %Foreground operators:
% 1.80/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.80/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.80/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.80/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.80/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.80/1.31  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.31  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.31  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.80/1.31  
% 1.80/1.32  tff(f_39, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 1.80/1.32  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.80/1.32  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 1.80/1.32  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.80/1.32  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 1.80/1.32  tff(f_42, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_enumset1)).
% 1.80/1.32  tff(c_14, plain, (![A_17, C_19, B_18]: (k1_enumset1(A_17, C_19, B_18)=k1_enumset1(A_17, B_18, C_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.80/1.32  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.80/1.32  tff(c_10, plain, (![A_10, B_11, C_12]: (k2_enumset1(A_10, A_10, B_11, C_12)=k1_enumset1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.80/1.32  tff(c_8, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.80/1.32  tff(c_174, plain, (![A_37, B_38, C_39, D_40]: (k2_xboole_0(k1_enumset1(A_37, B_38, C_39), k1_tarski(D_40))=k2_enumset1(A_37, B_38, C_39, D_40))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.80/1.32  tff(c_192, plain, (![A_8, B_9, D_40]: (k2_xboole_0(k2_tarski(A_8, B_9), k1_tarski(D_40))=k2_enumset1(A_8, A_8, B_9, D_40))), inference(superposition, [status(thm), theory('equality')], [c_8, c_174])).
% 1.80/1.32  tff(c_196, plain, (![A_41, B_42, D_43]: (k2_xboole_0(k2_tarski(A_41, B_42), k1_tarski(D_43))=k1_enumset1(A_41, B_42, D_43))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_192])).
% 1.80/1.32  tff(c_224, plain, (![A_46, B_47, D_48]: (k2_xboole_0(k2_tarski(A_46, B_47), k1_tarski(D_48))=k1_enumset1(B_47, A_46, D_48))), inference(superposition, [status(thm), theory('equality')], [c_2, c_196])).
% 1.80/1.32  tff(c_195, plain, (![A_8, B_9, D_40]: (k2_xboole_0(k2_tarski(A_8, B_9), k1_tarski(D_40))=k1_enumset1(A_8, B_9, D_40))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_192])).
% 1.80/1.32  tff(c_230, plain, (![B_47, A_46, D_48]: (k1_enumset1(B_47, A_46, D_48)=k1_enumset1(A_46, B_47, D_48))), inference(superposition, [status(thm), theory('equality')], [c_224, c_195])).
% 1.80/1.32  tff(c_16, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.80/1.32  tff(c_17, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 1.80/1.32  tff(c_282, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_230, c_17])).
% 1.80/1.32  tff(c_285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_282])).
% 1.80/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.32  
% 1.80/1.32  Inference rules
% 1.80/1.32  ----------------------
% 1.80/1.32  #Ref     : 0
% 1.80/1.32  #Sup     : 64
% 1.80/1.32  #Fact    : 0
% 1.80/1.32  #Define  : 0
% 1.80/1.32  #Split   : 0
% 1.80/1.32  #Chain   : 0
% 1.80/1.32  #Close   : 0
% 1.80/1.32  
% 1.80/1.32  Ordering : KBO
% 1.80/1.32  
% 1.80/1.32  Simplification rules
% 1.80/1.32  ----------------------
% 1.80/1.32  #Subsume      : 0
% 1.80/1.32  #Demod        : 25
% 1.80/1.32  #Tautology    : 51
% 1.80/1.32  #SimpNegUnit  : 0
% 1.80/1.32  #BackRed      : 1
% 1.80/1.32  
% 1.80/1.32  #Partial instantiations: 0
% 1.80/1.32  #Strategies tried      : 1
% 1.80/1.32  
% 1.80/1.32  Timing (in seconds)
% 1.80/1.32  ----------------------
% 1.80/1.32  Preprocessing        : 0.29
% 1.80/1.32  Parsing              : 0.14
% 1.80/1.32  CNF conversion       : 0.02
% 1.80/1.32  Main loop            : 0.16
% 1.80/1.32  Inferencing          : 0.06
% 1.80/1.32  Reduction            : 0.06
% 1.80/1.32  Demodulation         : 0.05
% 1.80/1.32  BG Simplification    : 0.01
% 1.80/1.32  Subsumption          : 0.02
% 1.80/1.32  Abstraction          : 0.01
% 1.80/1.32  MUC search           : 0.00
% 1.80/1.32  Cooper               : 0.00
% 1.80/1.32  Total                : 0.47
% 1.80/1.32  Index Insertion      : 0.00
% 1.80/1.32  Index Deletion       : 0.00
% 1.80/1.32  Index Matching       : 0.00
% 1.80/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
