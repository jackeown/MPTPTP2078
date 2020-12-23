%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:11 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   13 (  14 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_31,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_34,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).

tff(c_4,plain,(
    ! [A_5,B_6] : k2_enumset1(A_5,A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_9,B_10] : k2_enumset1(A_9,A_9,A_9,B_10) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_7] : k2_enumset1(A_7,A_7,A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_25,plain,(
    ! [B_10] : k2_tarski(B_10,B_10) = k1_tarski(B_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_6])).

tff(c_44,plain,(
    ! [A_12,B_13,C_14,D_15] : k2_xboole_0(k2_tarski(A_12,B_13),k2_tarski(C_14,D_15)) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_53,plain,(
    ! [B_10,C_14,D_15] : k2_xboole_0(k1_tarski(B_10),k2_tarski(C_14,D_15)) = k2_enumset1(B_10,B_10,C_14,D_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_44])).

tff(c_8,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_59,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_8])).

tff(c_62,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.09  
% 1.59/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.09  %$ k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.59/1.09  
% 1.59/1.09  %Foreground sorts:
% 1.59/1.09  
% 1.59/1.09  
% 1.59/1.09  %Background operators:
% 1.59/1.09  
% 1.59/1.09  
% 1.59/1.09  %Foreground operators:
% 1.59/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.59/1.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.59/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.59/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.59/1.09  
% 1.59/1.10  tff(f_29, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 1.59/1.10  tff(f_31, axiom, (![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_enumset1)).
% 1.59/1.10  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 1.59/1.10  tff(f_34, negated_conjecture, ~(![A, B]: (k2_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_zfmisc_1)).
% 1.59/1.10  tff(c_4, plain, (![A_5, B_6]: (k2_enumset1(A_5, A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.59/1.10  tff(c_18, plain, (![A_9, B_10]: (k2_enumset1(A_9, A_9, A_9, B_10)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.59/1.10  tff(c_6, plain, (![A_7]: (k2_enumset1(A_7, A_7, A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.59/1.10  tff(c_25, plain, (![B_10]: (k2_tarski(B_10, B_10)=k1_tarski(B_10))), inference(superposition, [status(thm), theory('equality')], [c_18, c_6])).
% 1.59/1.10  tff(c_44, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k2_tarski(A_12, B_13), k2_tarski(C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.59/1.10  tff(c_53, plain, (![B_10, C_14, D_15]: (k2_xboole_0(k1_tarski(B_10), k2_tarski(C_14, D_15))=k2_enumset1(B_10, B_10, C_14, D_15))), inference(superposition, [status(thm), theory('equality')], [c_25, c_44])).
% 1.59/1.10  tff(c_8, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.59/1.10  tff(c_59, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_8])).
% 1.59/1.10  tff(c_62, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_59])).
% 1.59/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.59/1.10  
% 1.59/1.10  Inference rules
% 1.59/1.10  ----------------------
% 1.59/1.10  #Ref     : 0
% 1.59/1.10  #Sup     : 12
% 1.59/1.10  #Fact    : 0
% 1.59/1.10  #Define  : 0
% 1.59/1.10  #Split   : 0
% 1.59/1.10  #Chain   : 0
% 1.59/1.10  #Close   : 0
% 1.59/1.10  
% 1.59/1.10  Ordering : KBO
% 1.59/1.10  
% 1.59/1.10  Simplification rules
% 1.59/1.10  ----------------------
% 1.59/1.10  #Subsume      : 0
% 1.59/1.10  #Demod        : 3
% 1.59/1.10  #Tautology    : 9
% 1.59/1.10  #SimpNegUnit  : 0
% 1.59/1.10  #BackRed      : 1
% 1.59/1.10  
% 1.59/1.10  #Partial instantiations: 0
% 1.59/1.10  #Strategies tried      : 1
% 1.59/1.10  
% 1.59/1.10  Timing (in seconds)
% 1.59/1.10  ----------------------
% 1.59/1.11  Preprocessing        : 0.26
% 1.59/1.11  Parsing              : 0.14
% 1.59/1.11  CNF conversion       : 0.01
% 1.59/1.11  Main loop            : 0.07
% 1.59/1.11  Inferencing          : 0.03
% 1.59/1.11  Reduction            : 0.02
% 1.59/1.11  Demodulation         : 0.02
% 1.59/1.11  BG Simplification    : 0.01
% 1.59/1.11  Subsumption          : 0.01
% 1.59/1.11  Abstraction          : 0.01
% 1.59/1.11  MUC search           : 0.00
% 1.59/1.11  Cooper               : 0.00
% 1.59/1.11  Total                : 0.35
% 1.59/1.11  Index Insertion      : 0.00
% 1.59/1.11  Index Deletion       : 0.00
% 1.59/1.11  Index Matching       : 0.00
% 1.59/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
