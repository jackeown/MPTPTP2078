%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:08 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   13 (  14 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_63,plain,(
    ! [A_18,B_19,C_20] : k2_xboole_0(k1_tarski(A_18),k2_tarski(B_19,C_20)) = k1_enumset1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(k1_tarski(A_5),k1_tarski(B_6)) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_37,plain,(
    ! [A_14,B_15] : k2_xboole_0(k1_tarski(A_14),k1_tarski(B_15)) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_43,plain,(
    ! [A_14,B_15] : k2_xboole_0(k1_tarski(A_14),k2_tarski(A_14,B_15)) = k2_xboole_0(k1_tarski(A_14),k1_tarski(B_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_2])).

tff(c_48,plain,(
    ! [A_14,B_15] : k2_xboole_0(k1_tarski(A_14),k2_tarski(A_14,B_15)) = k2_tarski(A_14,B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_43])).

tff(c_70,plain,(
    ! [B_19,C_20] : k1_enumset1(B_19,B_19,C_20) = k2_tarski(B_19,C_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_48])).

tff(c_10,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_85,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:25:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.57/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.15  
% 1.57/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.16  %$ k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.57/1.16  
% 1.57/1.16  %Foreground sorts:
% 1.57/1.16  
% 1.57/1.16  
% 1.57/1.16  %Background operators:
% 1.57/1.16  
% 1.57/1.16  
% 1.57/1.16  %Foreground operators:
% 1.57/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.57/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.57/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.57/1.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.57/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.57/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.57/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.57/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.57/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.57/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.57/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.57/1.16  
% 1.57/1.16  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 1.57/1.16  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 1.57/1.16  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 1.57/1.16  tff(f_36, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.57/1.16  tff(c_63, plain, (![A_18, B_19, C_20]: (k2_xboole_0(k1_tarski(A_18), k2_tarski(B_19, C_20))=k1_enumset1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.57/1.16  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(B_6))=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.57/1.16  tff(c_37, plain, (![A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), k1_tarski(B_15))=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.57/1.16  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.57/1.16  tff(c_43, plain, (![A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), k2_tarski(A_14, B_15))=k2_xboole_0(k1_tarski(A_14), k1_tarski(B_15)))), inference(superposition, [status(thm), theory('equality')], [c_37, c_2])).
% 1.57/1.16  tff(c_48, plain, (![A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), k2_tarski(A_14, B_15))=k2_tarski(A_14, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_43])).
% 1.57/1.16  tff(c_70, plain, (![B_19, C_20]: (k1_enumset1(B_19, B_19, C_20)=k2_tarski(B_19, C_20))), inference(superposition, [status(thm), theory('equality')], [c_63, c_48])).
% 1.57/1.16  tff(c_10, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.57/1.16  tff(c_85, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_10])).
% 1.57/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.16  
% 1.57/1.16  Inference rules
% 1.57/1.16  ----------------------
% 1.57/1.16  #Ref     : 0
% 1.57/1.16  #Sup     : 17
% 1.57/1.16  #Fact    : 0
% 1.57/1.16  #Define  : 0
% 1.57/1.16  #Split   : 0
% 1.57/1.16  #Chain   : 0
% 1.57/1.16  #Close   : 0
% 1.57/1.16  
% 1.57/1.16  Ordering : KBO
% 1.57/1.16  
% 1.57/1.16  Simplification rules
% 1.57/1.16  ----------------------
% 1.57/1.16  #Subsume      : 0
% 1.57/1.16  #Demod        : 9
% 1.57/1.16  #Tautology    : 13
% 1.57/1.16  #SimpNegUnit  : 0
% 1.57/1.16  #BackRed      : 1
% 1.57/1.16  
% 1.57/1.16  #Partial instantiations: 0
% 1.57/1.16  #Strategies tried      : 1
% 1.57/1.16  
% 1.57/1.16  Timing (in seconds)
% 1.57/1.16  ----------------------
% 1.57/1.17  Preprocessing        : 0.28
% 1.57/1.17  Parsing              : 0.14
% 1.57/1.17  CNF conversion       : 0.02
% 1.57/1.17  Main loop            : 0.08
% 1.57/1.17  Inferencing          : 0.03
% 1.57/1.17  Reduction            : 0.03
% 1.57/1.17  Demodulation         : 0.02
% 1.57/1.17  BG Simplification    : 0.01
% 1.57/1.17  Subsumption          : 0.01
% 1.57/1.17  Abstraction          : 0.01
% 1.57/1.17  MUC search           : 0.00
% 1.57/1.17  Cooper               : 0.00
% 1.57/1.17  Total                : 0.37
% 1.57/1.17  Index Insertion      : 0.00
% 1.57/1.17  Index Deletion       : 0.00
% 1.57/1.17  Index Matching       : 0.00
% 1.57/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
