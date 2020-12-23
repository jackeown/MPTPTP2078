%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:48 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   25 (  46 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   14 (  35 expanded)
%              Number of equality atoms :   13 (  34 expanded)
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
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,B,D,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_enumset1)).

tff(c_4,plain,(
    ! [A_4,B_5,D_7,C_6] : k2_enumset1(A_4,B_5,D_7,C_6) = k2_enumset1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1] : k1_enumset1(B_2,C_3,A_1) = k1_enumset1(A_1,B_2,C_3) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    ! [A_19,B_20,C_21,D_22] : k2_xboole_0(k1_tarski(A_19),k1_enumset1(B_20,C_21,D_22)) = k2_enumset1(A_19,B_20,C_21,D_22) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [A_23,B_24,C_25,A_26] : k2_xboole_0(k1_tarski(A_23),k1_enumset1(B_24,C_25,A_26)) = k2_enumset1(A_23,A_26,B_24,C_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_72])).

tff(c_6,plain,(
    ! [A_8,B_9,C_10,D_11] : k2_xboole_0(k1_tarski(A_8),k1_enumset1(B_9,C_10,D_11)) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_23,B_24,C_25,A_26] : k2_enumset1(A_23,B_24,C_25,A_26) = k2_enumset1(A_23,A_26,B_24,C_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_6])).

tff(c_8,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_4','#skF_3') != k2_enumset1('#skF_1','#skF_3','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_8])).

tff(c_138,plain,(
    k2_enumset1('#skF_1','#skF_4','#skF_2','#skF_3') != k2_enumset1('#skF_1','#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_93,c_93,c_9])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:37:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.13  
% 1.69/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.14  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.69/1.14  
% 1.69/1.14  %Foreground sorts:
% 1.69/1.14  
% 1.69/1.14  
% 1.69/1.14  %Background operators:
% 1.69/1.14  
% 1.69/1.14  
% 1.69/1.14  %Foreground operators:
% 1.69/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.69/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.69/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.69/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.69/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.69/1.14  
% 1.69/1.14  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, B, D, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_enumset1)).
% 1.69/1.14  tff(f_27, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 1.69/1.14  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 1.69/1.14  tff(f_34, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_enumset1)).
% 1.69/1.14  tff(c_4, plain, (![A_4, B_5, D_7, C_6]: (k2_enumset1(A_4, B_5, D_7, C_6)=k2_enumset1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.69/1.14  tff(c_2, plain, (![B_2, C_3, A_1]: (k1_enumset1(B_2, C_3, A_1)=k1_enumset1(A_1, B_2, C_3))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.69/1.14  tff(c_72, plain, (![A_19, B_20, C_21, D_22]: (k2_xboole_0(k1_tarski(A_19), k1_enumset1(B_20, C_21, D_22))=k2_enumset1(A_19, B_20, C_21, D_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.14  tff(c_87, plain, (![A_23, B_24, C_25, A_26]: (k2_xboole_0(k1_tarski(A_23), k1_enumset1(B_24, C_25, A_26))=k2_enumset1(A_23, A_26, B_24, C_25))), inference(superposition, [status(thm), theory('equality')], [c_2, c_72])).
% 1.69/1.14  tff(c_6, plain, (![A_8, B_9, C_10, D_11]: (k2_xboole_0(k1_tarski(A_8), k1_enumset1(B_9, C_10, D_11))=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.14  tff(c_93, plain, (![A_23, B_24, C_25, A_26]: (k2_enumset1(A_23, B_24, C_25, A_26)=k2_enumset1(A_23, A_26, B_24, C_25))), inference(superposition, [status(thm), theory('equality')], [c_87, c_6])).
% 1.69/1.14  tff(c_8, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.69/1.14  tff(c_9, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_4', '#skF_3')!=k2_enumset1('#skF_1', '#skF_3', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_8])).
% 1.69/1.14  tff(c_138, plain, (k2_enumset1('#skF_1', '#skF_4', '#skF_2', '#skF_3')!=k2_enumset1('#skF_1', '#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_93, c_93, c_9])).
% 1.69/1.14  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_138])).
% 1.69/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.14  
% 1.69/1.14  Inference rules
% 1.69/1.14  ----------------------
% 1.69/1.14  #Ref     : 0
% 1.69/1.14  #Sup     : 34
% 1.69/1.14  #Fact    : 0
% 1.69/1.14  #Define  : 0
% 1.69/1.14  #Split   : 0
% 1.69/1.14  #Chain   : 0
% 1.69/1.14  #Close   : 0
% 1.69/1.14  
% 1.69/1.14  Ordering : KBO
% 1.69/1.14  
% 1.69/1.14  Simplification rules
% 1.69/1.14  ----------------------
% 1.69/1.14  #Subsume      : 4
% 1.69/1.14  #Demod        : 9
% 1.69/1.14  #Tautology    : 21
% 1.69/1.14  #SimpNegUnit  : 0
% 1.69/1.14  #BackRed      : 1
% 1.69/1.14  
% 1.69/1.14  #Partial instantiations: 0
% 1.69/1.14  #Strategies tried      : 1
% 1.69/1.14  
% 1.69/1.14  Timing (in seconds)
% 1.69/1.14  ----------------------
% 1.69/1.15  Preprocessing        : 0.26
% 1.69/1.15  Parsing              : 0.14
% 1.69/1.15  CNF conversion       : 0.01
% 1.69/1.15  Main loop            : 0.13
% 1.69/1.15  Inferencing          : 0.05
% 1.69/1.15  Reduction            : 0.05
% 1.69/1.15  Demodulation         : 0.04
% 1.69/1.15  BG Simplification    : 0.01
% 1.69/1.15  Subsumption          : 0.02
% 1.69/1.15  Abstraction          : 0.01
% 1.69/1.15  MUC search           : 0.00
% 1.69/1.15  Cooper               : 0.00
% 1.69/1.15  Total                : 0.41
% 1.69/1.15  Index Insertion      : 0.00
% 1.69/1.15  Index Deletion       : 0.00
% 1.69/1.15  Index Matching       : 0.00
% 1.69/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
