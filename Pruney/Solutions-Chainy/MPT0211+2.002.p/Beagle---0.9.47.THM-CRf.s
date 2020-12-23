%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:15 EST 2020

% Result     : Theorem 6.71s
% Output     : CNFRefutation 6.88s
% Verified   : 
% Statistics : Number of formulae       :   38 (  41 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  25 expanded)
%              Number of equality atoms :   21 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_137,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_139,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_enumset1)).

tff(f_107,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_129,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_111,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_87,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_142,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_82,plain,(
    ! [A_128,C_130,B_129] : k1_enumset1(A_128,C_130,B_129) = k1_enumset1(A_128,B_129,C_130) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_84,plain,(
    ! [B_132,A_131,C_133] : k1_enumset1(B_132,A_131,C_133) = k1_enumset1(A_131,B_132,C_133) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_52,plain,(
    ! [A_66,B_67,C_68] : k2_xboole_0(k1_tarski(A_66),k2_tarski(B_67,C_68)) = k1_enumset1(A_66,B_67,C_68) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_364,plain,(
    ! [A_165,C_166,B_167] : k1_enumset1(A_165,C_166,B_167) = k1_enumset1(A_165,B_167,C_166) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_74,plain,(
    ! [A_118,B_119] : k1_enumset1(A_118,A_118,B_119) = k2_tarski(A_118,B_119) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_392,plain,(
    ! [B_167,C_166] : k1_enumset1(B_167,C_166,B_167) = k2_tarski(B_167,C_166) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_74])).

tff(c_1762,plain,(
    ! [A_244,B_245,C_246,D_247] : k2_xboole_0(k1_tarski(A_244),k1_enumset1(B_245,C_246,D_247)) = k2_enumset1(A_244,B_245,C_246,D_247) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1816,plain,(
    ! [A_244,B_167,C_166] : k2_xboole_0(k1_tarski(A_244),k2_tarski(B_167,C_166)) = k2_enumset1(A_244,B_167,C_166,B_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_1762])).

tff(c_1839,plain,(
    ! [A_244,B_167,C_166] : k2_enumset1(A_244,B_167,C_166,B_167) = k1_enumset1(A_244,B_167,C_166) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1816])).

tff(c_40,plain,(
    ! [A_45,B_46,C_47,D_48] : k2_xboole_0(k2_tarski(A_45,B_46),k2_tarski(C_47,D_48)) = k2_enumset1(A_45,B_46,C_47,D_48) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_86,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_87,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_86])).

tff(c_89,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_87])).

tff(c_6229,plain,(
    k1_enumset1('#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1839,c_89])).

tff(c_6232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_84,c_6229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:18:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.71/2.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.71/2.41  
% 6.71/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.88/2.41  %$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 6.88/2.41  
% 6.88/2.41  %Foreground sorts:
% 6.88/2.41  
% 6.88/2.41  
% 6.88/2.41  %Background operators:
% 6.88/2.41  
% 6.88/2.41  
% 6.88/2.41  %Foreground operators:
% 6.88/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.88/2.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.88/2.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.88/2.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.88/2.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.88/2.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.88/2.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.88/2.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.88/2.41  tff('#skF_2', type, '#skF_2': $i).
% 6.88/2.41  tff('#skF_3', type, '#skF_3': $i).
% 6.88/2.41  tff('#skF_1', type, '#skF_1': $i).
% 6.88/2.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.88/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.88/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.88/2.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.88/2.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.88/2.41  
% 6.88/2.42  tff(f_137, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_enumset1)).
% 6.88/2.42  tff(f_139, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_enumset1)).
% 6.88/2.42  tff(f_107, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 6.88/2.42  tff(f_129, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.88/2.42  tff(f_111, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 6.88/2.42  tff(f_87, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 6.88/2.42  tff(f_142, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 6.88/2.42  tff(c_82, plain, (![A_128, C_130, B_129]: (k1_enumset1(A_128, C_130, B_129)=k1_enumset1(A_128, B_129, C_130))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.88/2.42  tff(c_84, plain, (![B_132, A_131, C_133]: (k1_enumset1(B_132, A_131, C_133)=k1_enumset1(A_131, B_132, C_133))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.88/2.42  tff(c_52, plain, (![A_66, B_67, C_68]: (k2_xboole_0(k1_tarski(A_66), k2_tarski(B_67, C_68))=k1_enumset1(A_66, B_67, C_68))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.88/2.42  tff(c_364, plain, (![A_165, C_166, B_167]: (k1_enumset1(A_165, C_166, B_167)=k1_enumset1(A_165, B_167, C_166))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.88/2.42  tff(c_74, plain, (![A_118, B_119]: (k1_enumset1(A_118, A_118, B_119)=k2_tarski(A_118, B_119))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.88/2.42  tff(c_392, plain, (![B_167, C_166]: (k1_enumset1(B_167, C_166, B_167)=k2_tarski(B_167, C_166))), inference(superposition, [status(thm), theory('equality')], [c_364, c_74])).
% 6.88/2.42  tff(c_1762, plain, (![A_244, B_245, C_246, D_247]: (k2_xboole_0(k1_tarski(A_244), k1_enumset1(B_245, C_246, D_247))=k2_enumset1(A_244, B_245, C_246, D_247))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.88/2.42  tff(c_1816, plain, (![A_244, B_167, C_166]: (k2_xboole_0(k1_tarski(A_244), k2_tarski(B_167, C_166))=k2_enumset1(A_244, B_167, C_166, B_167))), inference(superposition, [status(thm), theory('equality')], [c_392, c_1762])).
% 6.88/2.42  tff(c_1839, plain, (![A_244, B_167, C_166]: (k2_enumset1(A_244, B_167, C_166, B_167)=k1_enumset1(A_244, B_167, C_166))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1816])).
% 6.88/2.42  tff(c_40, plain, (![A_45, B_46, C_47, D_48]: (k2_xboole_0(k2_tarski(A_45, B_46), k2_tarski(C_47, D_48))=k2_enumset1(A_45, B_46, C_47, D_48))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.88/2.42  tff(c_86, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.88/2.42  tff(c_87, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_86])).
% 6.88/2.42  tff(c_89, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_87])).
% 6.88/2.42  tff(c_6229, plain, (k1_enumset1('#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1839, c_89])).
% 6.88/2.42  tff(c_6232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_84, c_6229])).
% 6.88/2.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.88/2.42  
% 6.88/2.42  Inference rules
% 6.88/2.42  ----------------------
% 6.88/2.42  #Ref     : 1
% 6.88/2.42  #Sup     : 1622
% 6.88/2.42  #Fact    : 0
% 6.88/2.42  #Define  : 0
% 6.88/2.42  #Split   : 0
% 6.88/2.42  #Chain   : 0
% 6.88/2.42  #Close   : 0
% 6.88/2.42  
% 6.88/2.42  Ordering : KBO
% 6.88/2.42  
% 6.88/2.42  Simplification rules
% 6.88/2.42  ----------------------
% 6.88/2.42  #Subsume      : 93
% 6.88/2.42  #Demod        : 993
% 6.88/2.42  #Tautology    : 702
% 6.88/2.42  #SimpNegUnit  : 0
% 6.88/2.42  #BackRed      : 1
% 6.88/2.42  
% 6.88/2.42  #Partial instantiations: 0
% 6.88/2.42  #Strategies tried      : 1
% 6.88/2.42  
% 6.88/2.42  Timing (in seconds)
% 6.88/2.42  ----------------------
% 6.88/2.42  Preprocessing        : 0.39
% 6.88/2.42  Parsing              : 0.20
% 6.88/2.42  CNF conversion       : 0.03
% 6.88/2.42  Main loop            : 1.27
% 6.88/2.42  Inferencing          : 0.35
% 6.88/2.42  Reduction            : 0.58
% 6.88/2.42  Demodulation         : 0.49
% 6.88/2.42  BG Simplification    : 0.07
% 6.88/2.42  Subsumption          : 0.20
% 6.88/2.42  Abstraction          : 0.07
% 6.88/2.42  MUC search           : 0.00
% 6.88/2.42  Cooper               : 0.00
% 6.88/2.42  Total                : 1.69
% 6.88/2.42  Index Insertion      : 0.00
% 6.88/2.42  Index Deletion       : 0.00
% 6.88/2.42  Index Matching       : 0.00
% 6.88/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
