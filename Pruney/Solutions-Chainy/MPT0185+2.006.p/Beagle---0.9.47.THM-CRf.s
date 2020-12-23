%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:46 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
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
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_32,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(c_4,plain,(
    ! [A_5,C_7,B_6] : k1_enumset1(A_5,C_7,B_6) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    ! [A_11,B_12,C_13,D_14] : k2_xboole_0(k1_tarski(A_11),k1_enumset1(B_12,C_13,D_14)) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_55,plain,(
    ! [A_15,A_16,C_17,B_18] : k2_xboole_0(k1_tarski(A_15),k1_enumset1(A_16,C_17,B_18)) = k2_enumset1(A_15,A_16,B_18,C_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_40])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] : k2_xboole_0(k1_tarski(A_1),k1_enumset1(B_2,C_3,D_4)) = k2_enumset1(A_1,B_2,C_3,D_4) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_61,plain,(
    ! [A_15,A_16,C_17,B_18] : k2_enumset1(A_15,A_16,C_17,B_18) = k2_enumset1(A_15,A_16,B_18,C_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_2])).

tff(c_6,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:18:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.32  
% 1.88/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.33  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.88/1.33  
% 1.88/1.33  %Foreground sorts:
% 1.88/1.33  
% 1.88/1.33  
% 1.88/1.33  %Background operators:
% 1.88/1.33  
% 1.88/1.33  
% 1.88/1.33  %Foreground operators:
% 1.88/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.88/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.88/1.33  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.33  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.33  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.33  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.88/1.33  
% 1.88/1.34  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 1.88/1.34  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 1.88/1.34  tff(f_32, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 1.88/1.34  tff(c_4, plain, (![A_5, C_7, B_6]: (k1_enumset1(A_5, C_7, B_6)=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.88/1.34  tff(c_40, plain, (![A_11, B_12, C_13, D_14]: (k2_xboole_0(k1_tarski(A_11), k1_enumset1(B_12, C_13, D_14))=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.88/1.34  tff(c_55, plain, (![A_15, A_16, C_17, B_18]: (k2_xboole_0(k1_tarski(A_15), k1_enumset1(A_16, C_17, B_18))=k2_enumset1(A_15, A_16, B_18, C_17))), inference(superposition, [status(thm), theory('equality')], [c_4, c_40])).
% 1.88/1.34  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (k2_xboole_0(k1_tarski(A_1), k1_enumset1(B_2, C_3, D_4))=k2_enumset1(A_1, B_2, C_3, D_4))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.88/1.34  tff(c_61, plain, (![A_15, A_16, C_17, B_18]: (k2_enumset1(A_15, A_16, C_17, B_18)=k2_enumset1(A_15, A_16, B_18, C_17))), inference(superposition, [status(thm), theory('equality')], [c_55, c_2])).
% 1.88/1.34  tff(c_6, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.34  tff(c_80, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_6])).
% 1.88/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.34  
% 1.88/1.34  Inference rules
% 1.88/1.34  ----------------------
% 1.88/1.34  #Ref     : 0
% 1.88/1.34  #Sup     : 18
% 1.88/1.34  #Fact    : 0
% 1.88/1.34  #Define  : 0
% 1.88/1.34  #Split   : 0
% 1.88/1.34  #Chain   : 0
% 1.88/1.34  #Close   : 0
% 1.88/1.34  
% 1.88/1.34  Ordering : KBO
% 1.88/1.34  
% 1.88/1.34  Simplification rules
% 1.88/1.34  ----------------------
% 1.88/1.34  #Subsume      : 0
% 1.88/1.34  #Demod        : 3
% 1.88/1.34  #Tautology    : 14
% 1.88/1.34  #SimpNegUnit  : 0
% 1.88/1.34  #BackRed      : 1
% 1.88/1.34  
% 1.88/1.34  #Partial instantiations: 0
% 1.88/1.34  #Strategies tried      : 1
% 1.88/1.34  
% 1.88/1.34  Timing (in seconds)
% 1.88/1.34  ----------------------
% 1.88/1.34  Preprocessing        : 0.41
% 1.88/1.34  Parsing              : 0.21
% 1.88/1.34  CNF conversion       : 0.03
% 1.88/1.34  Main loop            : 0.14
% 1.88/1.34  Inferencing          : 0.06
% 1.88/1.34  Reduction            : 0.05
% 1.88/1.34  Demodulation         : 0.04
% 1.88/1.34  BG Simplification    : 0.01
% 1.88/1.34  Subsumption          : 0.01
% 1.88/1.34  Abstraction          : 0.01
% 1.88/1.34  MUC search           : 0.00
% 1.98/1.34  Cooper               : 0.00
% 1.98/1.35  Total                : 0.59
% 1.98/1.35  Index Insertion      : 0.00
% 1.98/1.35  Index Deletion       : 0.00
% 1.98/1.35  Index Matching       : 0.00
% 1.98/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
