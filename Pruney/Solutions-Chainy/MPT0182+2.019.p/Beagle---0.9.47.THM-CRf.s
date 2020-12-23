%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:44 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  20 expanded)
%              Number of equality atoms :   19 (  19 expanded)
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

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

tff(c_12,plain,(
    ! [A_13,B_14,C_15] : k2_enumset1(A_13,A_13,B_14,C_15) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,B_12] : k1_enumset1(A_11,A_11,B_12) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_303,plain,(
    ! [A_47,B_48,C_49,D_50] : k2_xboole_0(k1_enumset1(A_47,B_48,C_49),k1_tarski(D_50)) = k2_enumset1(A_47,B_48,C_49,D_50) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_333,plain,(
    ! [A_11,B_12,D_50] : k2_xboole_0(k2_tarski(A_11,B_12),k1_tarski(D_50)) = k2_enumset1(A_11,A_11,B_12,D_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_303])).

tff(c_507,plain,(
    ! [A_58,B_59,D_60] : k2_xboole_0(k2_tarski(A_58,B_59),k1_tarski(D_60)) = k1_enumset1(A_58,B_59,D_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_333])).

tff(c_167,plain,(
    ! [A_36,B_37,C_38] : k2_xboole_0(k1_tarski(A_36),k2_tarski(B_37,C_38)) = k1_enumset1(A_36,B_37,C_38) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_176,plain,(
    ! [B_37,C_38,A_36] : k2_xboole_0(k2_tarski(B_37,C_38),k1_tarski(A_36)) = k1_enumset1(A_36,B_37,C_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_2])).

tff(c_513,plain,(
    ! [D_60,A_58,B_59] : k1_enumset1(D_60,A_58,B_59) = k1_enumset1(A_58,B_59,D_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_507,c_176])).

tff(c_16,plain,(
    ! [A_20,C_22,B_21] : k1_enumset1(A_20,C_22,B_21) = k1_enumset1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_19,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_541,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:49:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.23  
% 2.21/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.23  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.21/1.23  
% 2.21/1.23  %Foreground sorts:
% 2.21/1.23  
% 2.21/1.23  
% 2.21/1.23  %Background operators:
% 2.21/1.23  
% 2.21/1.23  
% 2.21/1.23  %Foreground operators:
% 2.21/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.21/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.21/1.23  
% 2.21/1.24  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.21/1.24  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.21/1.24  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.21/1.24  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.21/1.24  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.21/1.24  tff(f_41, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_enumset1)).
% 2.21/1.24  tff(f_44, negated_conjecture, ~(![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_enumset1)).
% 2.21/1.24  tff(c_12, plain, (![A_13, B_14, C_15]: (k2_enumset1(A_13, A_13, B_14, C_15)=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.21/1.24  tff(c_10, plain, (![A_11, B_12]: (k1_enumset1(A_11, A_11, B_12)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.21/1.24  tff(c_303, plain, (![A_47, B_48, C_49, D_50]: (k2_xboole_0(k1_enumset1(A_47, B_48, C_49), k1_tarski(D_50))=k2_enumset1(A_47, B_48, C_49, D_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.21/1.24  tff(c_333, plain, (![A_11, B_12, D_50]: (k2_xboole_0(k2_tarski(A_11, B_12), k1_tarski(D_50))=k2_enumset1(A_11, A_11, B_12, D_50))), inference(superposition, [status(thm), theory('equality')], [c_10, c_303])).
% 2.21/1.24  tff(c_507, plain, (![A_58, B_59, D_60]: (k2_xboole_0(k2_tarski(A_58, B_59), k1_tarski(D_60))=k1_enumset1(A_58, B_59, D_60))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_333])).
% 2.21/1.24  tff(c_167, plain, (![A_36, B_37, C_38]: (k2_xboole_0(k1_tarski(A_36), k2_tarski(B_37, C_38))=k1_enumset1(A_36, B_37, C_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.24  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.24  tff(c_176, plain, (![B_37, C_38, A_36]: (k2_xboole_0(k2_tarski(B_37, C_38), k1_tarski(A_36))=k1_enumset1(A_36, B_37, C_38))), inference(superposition, [status(thm), theory('equality')], [c_167, c_2])).
% 2.21/1.24  tff(c_513, plain, (![D_60, A_58, B_59]: (k1_enumset1(D_60, A_58, B_59)=k1_enumset1(A_58, B_59, D_60))), inference(superposition, [status(thm), theory('equality')], [c_507, c_176])).
% 2.21/1.24  tff(c_16, plain, (![A_20, C_22, B_21]: (k1_enumset1(A_20, C_22, B_21)=k1_enumset1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.21/1.24  tff(c_18, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.21/1.24  tff(c_19, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 2.21/1.24  tff(c_541, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_513, c_19])).
% 2.21/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.24  
% 2.21/1.24  Inference rules
% 2.21/1.24  ----------------------
% 2.21/1.24  #Ref     : 0
% 2.21/1.24  #Sup     : 134
% 2.21/1.24  #Fact    : 0
% 2.21/1.24  #Define  : 0
% 2.21/1.24  #Split   : 0
% 2.21/1.24  #Chain   : 0
% 2.21/1.24  #Close   : 0
% 2.21/1.24  
% 2.21/1.24  Ordering : KBO
% 2.21/1.24  
% 2.21/1.24  Simplification rules
% 2.21/1.24  ----------------------
% 2.21/1.24  #Subsume      : 31
% 2.21/1.24  #Demod        : 47
% 2.21/1.24  #Tautology    : 75
% 2.21/1.24  #SimpNegUnit  : 0
% 2.21/1.24  #BackRed      : 1
% 2.21/1.24  
% 2.21/1.24  #Partial instantiations: 0
% 2.21/1.24  #Strategies tried      : 1
% 2.21/1.24  
% 2.21/1.24  Timing (in seconds)
% 2.21/1.24  ----------------------
% 2.21/1.25  Preprocessing        : 0.27
% 2.21/1.25  Parsing              : 0.14
% 2.21/1.25  CNF conversion       : 0.02
% 2.21/1.25  Main loop            : 0.24
% 2.21/1.25  Inferencing          : 0.09
% 2.21/1.25  Reduction            : 0.09
% 2.21/1.25  Demodulation         : 0.08
% 2.21/1.25  BG Simplification    : 0.01
% 2.21/1.25  Subsumption          : 0.03
% 2.21/1.25  Abstraction          : 0.01
% 2.21/1.25  MUC search           : 0.00
% 2.21/1.25  Cooper               : 0.00
% 2.21/1.25  Total                : 0.53
% 2.21/1.25  Index Insertion      : 0.00
% 2.21/1.25  Index Deletion       : 0.00
% 2.21/1.25  Index Matching       : 0.00
% 2.21/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
