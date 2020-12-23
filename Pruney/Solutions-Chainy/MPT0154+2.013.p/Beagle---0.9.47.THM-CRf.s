%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:05 EST 2020

% Result     : Theorem 7.94s
% Output     : CNFRefutation 7.94s
% Verified   : 
% Statistics : Number of formulae       :   41 (  48 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   22 (  29 expanded)
%              Number of equality atoms :   21 (  28 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_70,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_68,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_74,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_50,plain,(
    ! [A_34,B_35,C_36] : k2_xboole_0(k1_tarski(A_34),k2_tarski(B_35,C_36)) = k1_enumset1(A_34,B_35,C_36) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_48,plain,(
    ! [A_32,B_33] : k2_xboole_0(k1_tarski(A_32),k1_tarski(B_33)) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_54,plain,(
    ! [A_41] : k2_tarski(A_41,A_41) = k1_tarski(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_577,plain,(
    ! [A_94,B_95,C_96] : k2_xboole_0(k1_tarski(A_94),k2_tarski(B_95,C_96)) = k1_enumset1(A_94,B_95,C_96) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_586,plain,(
    ! [A_94,A_41] : k2_xboole_0(k1_tarski(A_94),k1_tarski(A_41)) = k1_enumset1(A_94,A_41,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_577])).

tff(c_589,plain,(
    ! [A_94,A_41] : k1_enumset1(A_94,A_41,A_41) = k2_tarski(A_94,A_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_586])).

tff(c_938,plain,(
    ! [A_111,B_112,C_113,D_114] : k2_xboole_0(k1_tarski(A_111),k1_enumset1(B_112,C_113,D_114)) = k2_enumset1(A_111,B_112,C_113,D_114) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_947,plain,(
    ! [A_111,A_94,A_41] : k2_xboole_0(k1_tarski(A_111),k2_tarski(A_94,A_41)) = k2_enumset1(A_111,A_94,A_41,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_938])).

tff(c_12011,plain,(
    ! [A_391,A_392,A_393] : k2_enumset1(A_391,A_392,A_393,A_393) = k1_enumset1(A_391,A_392,A_393) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_947])).

tff(c_878,plain,(
    ! [A_106,B_107,C_108,D_109] : k2_xboole_0(k2_tarski(A_106,B_107),k2_tarski(C_108,D_109)) = k2_enumset1(A_106,B_107,C_108,D_109) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3416,plain,(
    ! [A_205,B_206,A_207] : k2_xboole_0(k2_tarski(A_205,B_206),k1_tarski(A_207)) = k2_enumset1(A_205,B_206,A_207,A_207) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_878])).

tff(c_3457,plain,(
    ! [A_41,A_207] : k2_xboole_0(k1_tarski(A_41),k1_tarski(A_207)) = k2_enumset1(A_41,A_41,A_207,A_207) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_3416])).

tff(c_3466,plain,(
    ! [A_41,A_207] : k2_enumset1(A_41,A_41,A_207,A_207) = k2_tarski(A_41,A_207) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3457])).

tff(c_12018,plain,(
    ! [A_392,A_393] : k1_enumset1(A_392,A_392,A_393) = k2_tarski(A_392,A_393) ),
    inference(superposition,[status(thm),theory(equality)],[c_12011,c_3466])).

tff(c_56,plain,(
    k1_enumset1('#skF_4','#skF_4','#skF_5') != k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12058,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12018,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n005.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 17:56:02 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.94/2.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.94/2.74  
% 7.94/2.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.94/2.74  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 7.94/2.74  
% 7.94/2.74  %Foreground sorts:
% 7.94/2.74  
% 7.94/2.74  
% 7.94/2.74  %Background operators:
% 7.94/2.74  
% 7.94/2.74  
% 7.94/2.74  %Foreground operators:
% 7.94/2.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.94/2.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.94/2.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.94/2.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.94/2.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.94/2.74  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.94/2.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.94/2.74  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.94/2.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.94/2.74  tff('#skF_5', type, '#skF_5': $i).
% 7.94/2.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.94/2.74  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.94/2.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.94/2.74  tff('#skF_4', type, '#skF_4': $i).
% 7.94/2.74  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.94/2.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.94/2.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.94/2.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.94/2.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.94/2.74  
% 7.94/2.75  tff(f_70, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 7.94/2.75  tff(f_68, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 7.94/2.75  tff(f_74, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.94/2.75  tff(f_72, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 7.94/2.75  tff(f_66, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 7.94/2.75  tff(f_77, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.94/2.75  tff(c_50, plain, (![A_34, B_35, C_36]: (k2_xboole_0(k1_tarski(A_34), k2_tarski(B_35, C_36))=k1_enumset1(A_34, B_35, C_36))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.94/2.75  tff(c_48, plain, (![A_32, B_33]: (k2_xboole_0(k1_tarski(A_32), k1_tarski(B_33))=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.94/2.75  tff(c_54, plain, (![A_41]: (k2_tarski(A_41, A_41)=k1_tarski(A_41))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.94/2.75  tff(c_577, plain, (![A_94, B_95, C_96]: (k2_xboole_0(k1_tarski(A_94), k2_tarski(B_95, C_96))=k1_enumset1(A_94, B_95, C_96))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.94/2.75  tff(c_586, plain, (![A_94, A_41]: (k2_xboole_0(k1_tarski(A_94), k1_tarski(A_41))=k1_enumset1(A_94, A_41, A_41))), inference(superposition, [status(thm), theory('equality')], [c_54, c_577])).
% 7.94/2.75  tff(c_589, plain, (![A_94, A_41]: (k1_enumset1(A_94, A_41, A_41)=k2_tarski(A_94, A_41))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_586])).
% 7.94/2.75  tff(c_938, plain, (![A_111, B_112, C_113, D_114]: (k2_xboole_0(k1_tarski(A_111), k1_enumset1(B_112, C_113, D_114))=k2_enumset1(A_111, B_112, C_113, D_114))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.94/2.75  tff(c_947, plain, (![A_111, A_94, A_41]: (k2_xboole_0(k1_tarski(A_111), k2_tarski(A_94, A_41))=k2_enumset1(A_111, A_94, A_41, A_41))), inference(superposition, [status(thm), theory('equality')], [c_589, c_938])).
% 7.94/2.75  tff(c_12011, plain, (![A_391, A_392, A_393]: (k2_enumset1(A_391, A_392, A_393, A_393)=k1_enumset1(A_391, A_392, A_393))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_947])).
% 7.94/2.75  tff(c_878, plain, (![A_106, B_107, C_108, D_109]: (k2_xboole_0(k2_tarski(A_106, B_107), k2_tarski(C_108, D_109))=k2_enumset1(A_106, B_107, C_108, D_109))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.94/2.75  tff(c_3416, plain, (![A_205, B_206, A_207]: (k2_xboole_0(k2_tarski(A_205, B_206), k1_tarski(A_207))=k2_enumset1(A_205, B_206, A_207, A_207))), inference(superposition, [status(thm), theory('equality')], [c_54, c_878])).
% 7.94/2.75  tff(c_3457, plain, (![A_41, A_207]: (k2_xboole_0(k1_tarski(A_41), k1_tarski(A_207))=k2_enumset1(A_41, A_41, A_207, A_207))), inference(superposition, [status(thm), theory('equality')], [c_54, c_3416])).
% 7.94/2.75  tff(c_3466, plain, (![A_41, A_207]: (k2_enumset1(A_41, A_41, A_207, A_207)=k2_tarski(A_41, A_207))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3457])).
% 7.94/2.75  tff(c_12018, plain, (![A_392, A_393]: (k1_enumset1(A_392, A_392, A_393)=k2_tarski(A_392, A_393))), inference(superposition, [status(thm), theory('equality')], [c_12011, c_3466])).
% 7.94/2.75  tff(c_56, plain, (k1_enumset1('#skF_4', '#skF_4', '#skF_5')!=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.94/2.75  tff(c_12058, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12018, c_56])).
% 7.94/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.94/2.75  
% 7.94/2.75  Inference rules
% 7.94/2.75  ----------------------
% 7.94/2.75  #Ref     : 0
% 7.94/2.75  #Sup     : 2881
% 7.94/2.75  #Fact    : 0
% 7.94/2.75  #Define  : 0
% 7.94/2.75  #Split   : 0
% 7.94/2.75  #Chain   : 0
% 7.94/2.75  #Close   : 0
% 7.94/2.75  
% 7.94/2.75  Ordering : KBO
% 7.94/2.75  
% 7.94/2.75  Simplification rules
% 7.94/2.75  ----------------------
% 7.94/2.75  #Subsume      : 228
% 7.94/2.75  #Demod        : 3208
% 7.94/2.75  #Tautology    : 1840
% 7.94/2.75  #SimpNegUnit  : 0
% 7.94/2.75  #BackRed      : 17
% 7.94/2.75  
% 7.94/2.75  #Partial instantiations: 0
% 7.94/2.75  #Strategies tried      : 1
% 7.94/2.75  
% 7.94/2.75  Timing (in seconds)
% 7.94/2.75  ----------------------
% 7.94/2.75  Preprocessing        : 0.32
% 7.94/2.75  Parsing              : 0.16
% 7.94/2.75  CNF conversion       : 0.02
% 7.94/2.75  Main loop            : 1.69
% 7.94/2.75  Inferencing          : 0.47
% 7.94/2.75  Reduction            : 0.80
% 7.94/2.75  Demodulation         : 0.68
% 7.94/2.75  BG Simplification    : 0.05
% 7.94/2.75  Subsumption          : 0.28
% 7.94/2.75  Abstraction          : 0.08
% 7.94/2.75  MUC search           : 0.00
% 7.94/2.75  Cooper               : 0.00
% 7.94/2.75  Total                : 2.04
% 7.94/2.75  Index Insertion      : 0.00
% 7.94/2.75  Index Deletion       : 0.00
% 7.94/2.75  Index Matching       : 0.00
% 7.94/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
