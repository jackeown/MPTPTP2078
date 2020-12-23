%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:07 EST 2020

% Result     : Theorem 6.10s
% Output     : CNFRefutation 6.31s
% Verified   : 
% Statistics : Number of formulae       :   38 (  45 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   22 (  29 expanded)
%              Number of equality atoms :   21 (  28 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_26,plain,(
    ! [A_26,B_27,C_28] : k2_xboole_0(k1_tarski(A_26),k2_tarski(B_27,C_28)) = k1_enumset1(A_26,B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_24,B_25] : k2_xboole_0(k1_tarski(A_24),k1_tarski(B_25)) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [A_38] : k2_tarski(A_38,A_38) = k1_tarski(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_540,plain,(
    ! [A_73,B_74,C_75] : k2_xboole_0(k1_tarski(A_73),k2_tarski(B_74,C_75)) = k1_enumset1(A_73,B_74,C_75) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_555,plain,(
    ! [A_73,A_38] : k2_xboole_0(k1_tarski(A_73),k1_tarski(A_38)) = k1_enumset1(A_73,A_38,A_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_540])).

tff(c_558,plain,(
    ! [A_73,A_38] : k1_enumset1(A_73,A_38,A_38) = k2_tarski(A_73,A_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_555])).

tff(c_658,plain,(
    ! [A_84,B_85,C_86,D_87] : k2_xboole_0(k1_tarski(A_84),k1_enumset1(B_85,C_86,D_87)) = k2_enumset1(A_84,B_85,C_86,D_87) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_673,plain,(
    ! [A_84,A_73,A_38] : k2_xboole_0(k1_tarski(A_84),k2_tarski(A_73,A_38)) = k2_enumset1(A_84,A_73,A_38,A_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_658])).

tff(c_8394,plain,(
    ! [A_276,A_277,A_278] : k2_enumset1(A_276,A_277,A_278,A_278) = k1_enumset1(A_276,A_277,A_278) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_673])).

tff(c_722,plain,(
    ! [A_93,B_94,C_95,D_96] : k2_xboole_0(k2_tarski(A_93,B_94),k2_tarski(C_95,D_96)) = k2_enumset1(A_93,B_94,C_95,D_96) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2185,plain,(
    ! [A_151,B_152,A_153] : k2_xboole_0(k2_tarski(A_151,B_152),k1_tarski(A_153)) = k2_enumset1(A_151,B_152,A_153,A_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_722])).

tff(c_2223,plain,(
    ! [A_38,A_153] : k2_xboole_0(k1_tarski(A_38),k1_tarski(A_153)) = k2_enumset1(A_38,A_38,A_153,A_153) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2185])).

tff(c_2232,plain,(
    ! [A_38,A_153] : k2_enumset1(A_38,A_38,A_153,A_153) = k2_tarski(A_38,A_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2223])).

tff(c_8409,plain,(
    ! [A_277,A_278] : k1_enumset1(A_277,A_277,A_278) = k2_tarski(A_277,A_278) ),
    inference(superposition,[status(thm),theory(equality)],[c_8394,c_2232])).

tff(c_34,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8409,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:49:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.10/2.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.10/2.28  
% 6.10/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.10/2.28  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 6.10/2.28  
% 6.10/2.28  %Foreground sorts:
% 6.10/2.28  
% 6.10/2.28  
% 6.10/2.28  %Background operators:
% 6.10/2.28  
% 6.10/2.28  
% 6.10/2.28  %Foreground operators:
% 6.10/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.10/2.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.10/2.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.10/2.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.10/2.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.10/2.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.10/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.10/2.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.10/2.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.10/2.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.10/2.28  tff('#skF_2', type, '#skF_2': $i).
% 6.10/2.28  tff('#skF_1', type, '#skF_1': $i).
% 6.10/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.10/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.10/2.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.10/2.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.10/2.28  
% 6.31/2.29  tff(f_53, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 6.31/2.29  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 6.31/2.29  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.31/2.29  tff(f_55, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 6.31/2.29  tff(f_49, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 6.31/2.29  tff(f_62, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.31/2.29  tff(c_26, plain, (![A_26, B_27, C_28]: (k2_xboole_0(k1_tarski(A_26), k2_tarski(B_27, C_28))=k1_enumset1(A_26, B_27, C_28))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.31/2.29  tff(c_24, plain, (![A_24, B_25]: (k2_xboole_0(k1_tarski(A_24), k1_tarski(B_25))=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.31/2.29  tff(c_32, plain, (![A_38]: (k2_tarski(A_38, A_38)=k1_tarski(A_38))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.31/2.29  tff(c_540, plain, (![A_73, B_74, C_75]: (k2_xboole_0(k1_tarski(A_73), k2_tarski(B_74, C_75))=k1_enumset1(A_73, B_74, C_75))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.31/2.29  tff(c_555, plain, (![A_73, A_38]: (k2_xboole_0(k1_tarski(A_73), k1_tarski(A_38))=k1_enumset1(A_73, A_38, A_38))), inference(superposition, [status(thm), theory('equality')], [c_32, c_540])).
% 6.31/2.29  tff(c_558, plain, (![A_73, A_38]: (k1_enumset1(A_73, A_38, A_38)=k2_tarski(A_73, A_38))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_555])).
% 6.31/2.29  tff(c_658, plain, (![A_84, B_85, C_86, D_87]: (k2_xboole_0(k1_tarski(A_84), k1_enumset1(B_85, C_86, D_87))=k2_enumset1(A_84, B_85, C_86, D_87))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.31/2.29  tff(c_673, plain, (![A_84, A_73, A_38]: (k2_xboole_0(k1_tarski(A_84), k2_tarski(A_73, A_38))=k2_enumset1(A_84, A_73, A_38, A_38))), inference(superposition, [status(thm), theory('equality')], [c_558, c_658])).
% 6.31/2.29  tff(c_8394, plain, (![A_276, A_277, A_278]: (k2_enumset1(A_276, A_277, A_278, A_278)=k1_enumset1(A_276, A_277, A_278))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_673])).
% 6.31/2.29  tff(c_722, plain, (![A_93, B_94, C_95, D_96]: (k2_xboole_0(k2_tarski(A_93, B_94), k2_tarski(C_95, D_96))=k2_enumset1(A_93, B_94, C_95, D_96))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.31/2.29  tff(c_2185, plain, (![A_151, B_152, A_153]: (k2_xboole_0(k2_tarski(A_151, B_152), k1_tarski(A_153))=k2_enumset1(A_151, B_152, A_153, A_153))), inference(superposition, [status(thm), theory('equality')], [c_32, c_722])).
% 6.31/2.29  tff(c_2223, plain, (![A_38, A_153]: (k2_xboole_0(k1_tarski(A_38), k1_tarski(A_153))=k2_enumset1(A_38, A_38, A_153, A_153))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2185])).
% 6.31/2.29  tff(c_2232, plain, (![A_38, A_153]: (k2_enumset1(A_38, A_38, A_153, A_153)=k2_tarski(A_38, A_153))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2223])).
% 6.31/2.29  tff(c_8409, plain, (![A_277, A_278]: (k1_enumset1(A_277, A_277, A_278)=k2_tarski(A_277, A_278))), inference(superposition, [status(thm), theory('equality')], [c_8394, c_2232])).
% 6.31/2.29  tff(c_34, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.31/2.29  tff(c_8448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8409, c_34])).
% 6.31/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.31/2.29  
% 6.31/2.29  Inference rules
% 6.31/2.29  ----------------------
% 6.31/2.29  #Ref     : 0
% 6.31/2.29  #Sup     : 2054
% 6.31/2.29  #Fact    : 0
% 6.31/2.29  #Define  : 0
% 6.31/2.29  #Split   : 0
% 6.31/2.29  #Chain   : 0
% 6.31/2.29  #Close   : 0
% 6.31/2.29  
% 6.31/2.29  Ordering : KBO
% 6.31/2.29  
% 6.31/2.29  Simplification rules
% 6.31/2.29  ----------------------
% 6.31/2.29  #Subsume      : 22
% 6.31/2.29  #Demod        : 2249
% 6.31/2.29  #Tautology    : 1469
% 6.31/2.29  #SimpNegUnit  : 0
% 6.31/2.29  #BackRed      : 16
% 6.31/2.29  
% 6.31/2.29  #Partial instantiations: 0
% 6.31/2.29  #Strategies tried      : 1
% 6.31/2.29  
% 6.31/2.29  Timing (in seconds)
% 6.31/2.29  ----------------------
% 6.31/2.29  Preprocessing        : 0.31
% 6.31/2.29  Parsing              : 0.16
% 6.31/2.29  CNF conversion       : 0.02
% 6.31/2.29  Main loop            : 1.23
% 6.31/2.30  Inferencing          : 0.38
% 6.31/2.30  Reduction            : 0.59
% 6.31/2.30  Demodulation         : 0.50
% 6.31/2.30  BG Simplification    : 0.04
% 6.31/2.30  Subsumption          : 0.16
% 6.31/2.30  Abstraction          : 0.07
% 6.31/2.30  MUC search           : 0.00
% 6.31/2.30  Cooper               : 0.00
% 6.31/2.30  Total                : 1.57
% 6.31/2.30  Index Insertion      : 0.00
% 6.31/2.30  Index Deletion       : 0.00
% 6.31/2.30  Index Matching       : 0.00
% 6.31/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
