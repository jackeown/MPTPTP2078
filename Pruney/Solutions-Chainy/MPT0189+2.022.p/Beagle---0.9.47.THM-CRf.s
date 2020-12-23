%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:53 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   32 (  41 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    4
%              Number of atoms          :   13 (  22 expanded)
%              Number of equality atoms :   12 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_8,plain,(
    ! [B_14,C_15,A_13] : k1_enumset1(B_14,C_15,A_13) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_304,plain,(
    ! [A_93,B_94,C_95,D_96] : k2_xboole_0(k1_enumset1(A_93,B_94,C_95),k1_tarski(D_96)) = k2_enumset1(A_93,B_94,C_95,D_96) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_383,plain,(
    ! [B_105,C_106,A_107,D_108] : k2_xboole_0(k1_enumset1(B_105,C_106,A_107),k1_tarski(D_108)) = k2_enumset1(A_107,B_105,C_106,D_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_304])).

tff(c_12,plain,(
    ! [A_20,B_21,C_22,D_23] : k2_xboole_0(k1_enumset1(A_20,B_21,C_22),k1_tarski(D_23)) = k2_enumset1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_389,plain,(
    ! [B_105,C_106,A_107,D_108] : k2_enumset1(B_105,C_106,A_107,D_108) = k2_enumset1(A_107,B_105,C_106,D_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_12])).

tff(c_10,plain,(
    ! [A_16,C_18,B_17,D_19] : k2_enumset1(A_16,C_18,B_17,D_19) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_33,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_32])).

tff(c_428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_389,c_33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:44:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.31  
% 2.15/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.31  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.15/1.31  
% 2.15/1.31  %Foreground sorts:
% 2.15/1.31  
% 2.15/1.31  
% 2.15/1.31  %Background operators:
% 2.15/1.31  
% 2.15/1.31  
% 2.15/1.31  %Foreground operators:
% 2.15/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.15/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.15/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.15/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.15/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.32  
% 2.15/1.32  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_enumset1)).
% 2.15/1.32  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.15/1.32  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 2.15/1.32  tff(f_58, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_enumset1)).
% 2.15/1.32  tff(c_8, plain, (![B_14, C_15, A_13]: (k1_enumset1(B_14, C_15, A_13)=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.15/1.32  tff(c_304, plain, (![A_93, B_94, C_95, D_96]: (k2_xboole_0(k1_enumset1(A_93, B_94, C_95), k1_tarski(D_96))=k2_enumset1(A_93, B_94, C_95, D_96))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.15/1.32  tff(c_383, plain, (![B_105, C_106, A_107, D_108]: (k2_xboole_0(k1_enumset1(B_105, C_106, A_107), k1_tarski(D_108))=k2_enumset1(A_107, B_105, C_106, D_108))), inference(superposition, [status(thm), theory('equality')], [c_8, c_304])).
% 2.15/1.32  tff(c_12, plain, (![A_20, B_21, C_22, D_23]: (k2_xboole_0(k1_enumset1(A_20, B_21, C_22), k1_tarski(D_23))=k2_enumset1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.15/1.32  tff(c_389, plain, (![B_105, C_106, A_107, D_108]: (k2_enumset1(B_105, C_106, A_107, D_108)=k2_enumset1(A_107, B_105, C_106, D_108))), inference(superposition, [status(thm), theory('equality')], [c_383, c_12])).
% 2.15/1.32  tff(c_10, plain, (![A_16, C_18, B_17, D_19]: (k2_enumset1(A_16, C_18, B_17, D_19)=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.15/1.32  tff(c_32, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.15/1.32  tff(c_33, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_32])).
% 2.15/1.32  tff(c_428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_389, c_389, c_33])).
% 2.15/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.32  
% 2.15/1.32  Inference rules
% 2.15/1.32  ----------------------
% 2.15/1.32  #Ref     : 0
% 2.15/1.32  #Sup     : 91
% 2.15/1.32  #Fact    : 0
% 2.15/1.32  #Define  : 0
% 2.15/1.32  #Split   : 0
% 2.15/1.32  #Chain   : 0
% 2.15/1.32  #Close   : 0
% 2.15/1.32  
% 2.15/1.32  Ordering : KBO
% 2.15/1.32  
% 2.15/1.32  Simplification rules
% 2.15/1.32  ----------------------
% 2.15/1.32  #Subsume      : 4
% 2.15/1.32  #Demod        : 56
% 2.15/1.32  #Tautology    : 76
% 2.15/1.32  #SimpNegUnit  : 0
% 2.15/1.32  #BackRed      : 1
% 2.15/1.32  
% 2.15/1.32  #Partial instantiations: 0
% 2.15/1.32  #Strategies tried      : 1
% 2.15/1.32  
% 2.15/1.32  Timing (in seconds)
% 2.15/1.32  ----------------------
% 2.15/1.33  Preprocessing        : 0.31
% 2.15/1.33  Parsing              : 0.16
% 2.15/1.33  CNF conversion       : 0.02
% 2.15/1.33  Main loop            : 0.25
% 2.15/1.33  Inferencing          : 0.09
% 2.15/1.33  Reduction            : 0.10
% 2.15/1.33  Demodulation         : 0.08
% 2.15/1.33  BG Simplification    : 0.02
% 2.15/1.33  Subsumption          : 0.03
% 2.15/1.33  Abstraction          : 0.02
% 2.15/1.33  MUC search           : 0.00
% 2.15/1.33  Cooper               : 0.00
% 2.15/1.33  Total                : 0.58
% 2.15/1.33  Index Insertion      : 0.00
% 2.15/1.33  Index Deletion       : 0.00
% 2.15/1.33  Index Matching       : 0.00
% 2.15/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
