%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:55 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   21 (  22 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :   10 (  11 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_4,plain,(
    ! [B_6,A_5,C_7] : k1_enumset1(B_6,A_5,C_7) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    ! [A_11,B_12,C_13,D_14] : k2_xboole_0(k1_enumset1(A_11,B_12,C_13),k1_tarski(D_14)) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_55,plain,(
    ! [B_15,A_16,C_17,D_18] : k2_xboole_0(k1_enumset1(B_15,A_16,C_17),k1_tarski(D_18)) = k2_enumset1(A_16,B_15,C_17,D_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_40])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_xboole_0(k1_enumset1(A_1,B_2,C_3),k1_tarski(D_4)) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_61,plain,(
    ! [B_15,A_16,C_17,D_18] : k2_enumset1(B_15,A_16,C_17,D_18) = k2_enumset1(A_16,B_15,C_17,D_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_2])).

tff(c_6,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.14  
% 1.60/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.15  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.60/1.15  
% 1.60/1.15  %Foreground sorts:
% 1.60/1.15  
% 1.60/1.15  
% 1.60/1.15  %Background operators:
% 1.60/1.15  
% 1.60/1.15  
% 1.60/1.15  %Foreground operators:
% 1.60/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.60/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.60/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.60/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.60/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.60/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.60/1.15  
% 1.60/1.15  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_enumset1)).
% 1.60/1.15  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 1.60/1.15  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_enumset1)).
% 1.60/1.15  tff(c_4, plain, (![B_6, A_5, C_7]: (k1_enumset1(B_6, A_5, C_7)=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.60/1.15  tff(c_40, plain, (![A_11, B_12, C_13, D_14]: (k2_xboole_0(k1_enumset1(A_11, B_12, C_13), k1_tarski(D_14))=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.60/1.15  tff(c_55, plain, (![B_15, A_16, C_17, D_18]: (k2_xboole_0(k1_enumset1(B_15, A_16, C_17), k1_tarski(D_18))=k2_enumset1(A_16, B_15, C_17, D_18))), inference(superposition, [status(thm), theory('equality')], [c_4, c_40])).
% 1.60/1.15  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k2_xboole_0(k1_enumset1(A_1, B_2, C_3), k1_tarski(D_4))=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.60/1.15  tff(c_61, plain, (![B_15, A_16, C_17, D_18]: (k2_enumset1(B_15, A_16, C_17, D_18)=k2_enumset1(A_16, B_15, C_17, D_18))), inference(superposition, [status(thm), theory('equality')], [c_55, c_2])).
% 1.60/1.15  tff(c_6, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.60/1.15  tff(c_80, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_6])).
% 1.60/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.15  
% 1.60/1.15  Inference rules
% 1.60/1.15  ----------------------
% 1.60/1.15  #Ref     : 0
% 1.60/1.15  #Sup     : 18
% 1.60/1.15  #Fact    : 0
% 1.60/1.15  #Define  : 0
% 1.60/1.15  #Split   : 0
% 1.60/1.15  #Chain   : 0
% 1.60/1.15  #Close   : 0
% 1.60/1.15  
% 1.60/1.15  Ordering : KBO
% 1.60/1.15  
% 1.60/1.15  Simplification rules
% 1.60/1.15  ----------------------
% 1.60/1.15  #Subsume      : 0
% 1.60/1.15  #Demod        : 3
% 1.60/1.15  #Tautology    : 14
% 1.60/1.15  #SimpNegUnit  : 0
% 1.60/1.15  #BackRed      : 1
% 1.60/1.15  
% 1.60/1.15  #Partial instantiations: 0
% 1.60/1.15  #Strategies tried      : 1
% 1.60/1.15  
% 1.60/1.15  Timing (in seconds)
% 1.60/1.15  ----------------------
% 1.60/1.15  Preprocessing        : 0.27
% 1.60/1.16  Parsing              : 0.14
% 1.60/1.16  CNF conversion       : 0.02
% 1.60/1.16  Main loop            : 0.08
% 1.60/1.16  Inferencing          : 0.04
% 1.60/1.16  Reduction            : 0.03
% 1.60/1.16  Demodulation         : 0.02
% 1.60/1.16  BG Simplification    : 0.01
% 1.60/1.16  Subsumption          : 0.01
% 1.60/1.16  Abstraction          : 0.01
% 1.60/1.16  MUC search           : 0.00
% 1.60/1.16  Cooper               : 0.00
% 1.60/1.16  Total                : 0.37
% 1.60/1.16  Index Insertion      : 0.00
% 1.60/1.16  Index Deletion       : 0.00
% 1.60/1.16  Index Matching       : 0.00
% 1.60/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
