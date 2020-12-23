%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:20 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :   40 (  50 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  32 expanded)
%              Number of equality atoms :   21 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k7_enumset1 > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k7_enumset1,type,(
    k7_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_379,plain,(
    ! [D_106,C_107,B_108,A_109] : k2_enumset1(D_106,C_107,B_108,A_109) = k2_enumset1(A_109,B_108,C_107,D_106) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_36,plain,(
    ! [A_66,B_67,C_68] : k2_enumset1(A_66,A_66,B_67,C_68) = k1_enumset1(A_66,B_67,C_68) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_205,plain,(
    ! [D_96,B_97,C_98,A_99] : k2_enumset1(D_96,B_97,C_98,A_99) = k2_enumset1(A_99,B_97,C_98,D_96) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_264,plain,(
    ! [C_68,A_66,B_67] : k2_enumset1(C_68,A_66,B_67,A_66) = k1_enumset1(A_66,B_67,C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_205])).

tff(c_399,plain,(
    ! [A_109,B_108,D_106] : k2_enumset1(A_109,B_108,A_109,D_106) = k1_enumset1(A_109,B_108,D_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_264])).

tff(c_162,plain,(
    ! [B_92,D_93,C_94,A_95] : k2_enumset1(B_92,D_93,C_94,A_95) = k2_enumset1(A_95,B_92,C_94,D_93) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_178,plain,(
    ! [B_92,D_93,C_94] : k2_enumset1(B_92,D_93,C_94,B_92) = k1_enumset1(B_92,C_94,D_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_36])).

tff(c_880,plain,(
    ! [B_128,C_129,D_130] : k2_enumset1(B_128,C_129,D_130,B_128) = k1_enumset1(B_128,C_129,D_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_379])).

tff(c_906,plain,(
    ! [B_128,D_130,C_129] : k1_enumset1(B_128,D_130,C_129) = k1_enumset1(B_128,C_129,D_130) ),
    inference(superposition,[status(thm),theory(equality)],[c_880,c_178])).

tff(c_22,plain,(
    ! [D_36,C_35,B_34,A_33] : k2_enumset1(D_36,C_35,B_34,A_33) = k2_enumset1(A_33,B_34,C_35,D_36) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14,D_15] : k2_xboole_0(k2_tarski(A_12,B_13),k2_tarski(C_14,D_15)) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_42,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_43,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_42])).

tff(c_44,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_43])).

tff(c_971,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_906,c_44])).

tff(c_1196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_971])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:17:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.50  
% 3.24/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.51  %$ k7_enumset1 > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 3.24/1.51  
% 3.24/1.51  %Foreground sorts:
% 3.24/1.51  
% 3.24/1.51  
% 3.24/1.51  %Background operators:
% 3.24/1.51  
% 3.24/1.51  
% 3.24/1.51  %Foreground operators:
% 3.24/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.24/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.24/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.24/1.51  tff(k7_enumset1, type, k7_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.24/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.24/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.24/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.24/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.24/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.24/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.24/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.24/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.24/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.24/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.24/1.51  
% 3.34/1.52  tff(f_47, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 3.34/1.52  tff(f_61, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.34/1.52  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_enumset1)).
% 3.34/1.52  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 3.34/1.52  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 3.34/1.52  tff(f_68, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 3.34/1.52  tff(c_379, plain, (![D_106, C_107, B_108, A_109]: (k2_enumset1(D_106, C_107, B_108, A_109)=k2_enumset1(A_109, B_108, C_107, D_106))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.34/1.52  tff(c_36, plain, (![A_66, B_67, C_68]: (k2_enumset1(A_66, A_66, B_67, C_68)=k1_enumset1(A_66, B_67, C_68))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.34/1.52  tff(c_205, plain, (![D_96, B_97, C_98, A_99]: (k2_enumset1(D_96, B_97, C_98, A_99)=k2_enumset1(A_99, B_97, C_98, D_96))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.34/1.52  tff(c_264, plain, (![C_68, A_66, B_67]: (k2_enumset1(C_68, A_66, B_67, A_66)=k1_enumset1(A_66, B_67, C_68))), inference(superposition, [status(thm), theory('equality')], [c_36, c_205])).
% 3.34/1.52  tff(c_399, plain, (![A_109, B_108, D_106]: (k2_enumset1(A_109, B_108, A_109, D_106)=k1_enumset1(A_109, B_108, D_106))), inference(superposition, [status(thm), theory('equality')], [c_379, c_264])).
% 3.34/1.52  tff(c_162, plain, (![B_92, D_93, C_94, A_95]: (k2_enumset1(B_92, D_93, C_94, A_95)=k2_enumset1(A_95, B_92, C_94, D_93))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.34/1.52  tff(c_178, plain, (![B_92, D_93, C_94]: (k2_enumset1(B_92, D_93, C_94, B_92)=k1_enumset1(B_92, C_94, D_93))), inference(superposition, [status(thm), theory('equality')], [c_162, c_36])).
% 3.34/1.52  tff(c_880, plain, (![B_128, C_129, D_130]: (k2_enumset1(B_128, C_129, D_130, B_128)=k1_enumset1(B_128, C_129, D_130))), inference(superposition, [status(thm), theory('equality')], [c_178, c_379])).
% 3.34/1.52  tff(c_906, plain, (![B_128, D_130, C_129]: (k1_enumset1(B_128, D_130, C_129)=k1_enumset1(B_128, C_129, D_130))), inference(superposition, [status(thm), theory('equality')], [c_880, c_178])).
% 3.34/1.52  tff(c_22, plain, (![D_36, C_35, B_34, A_33]: (k2_enumset1(D_36, C_35, B_34, A_33)=k2_enumset1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.34/1.52  tff(c_12, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k2_tarski(A_12, B_13), k2_tarski(C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.34/1.52  tff(c_42, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.34/1.52  tff(c_43, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_42])).
% 3.34/1.52  tff(c_44, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_43])).
% 3.34/1.52  tff(c_971, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_906, c_44])).
% 3.34/1.52  tff(c_1196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_399, c_971])).
% 3.34/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.52  
% 3.34/1.52  Inference rules
% 3.34/1.52  ----------------------
% 3.34/1.52  #Ref     : 0
% 3.34/1.52  #Sup     : 292
% 3.34/1.52  #Fact    : 0
% 3.34/1.52  #Define  : 0
% 3.34/1.52  #Split   : 0
% 3.34/1.52  #Chain   : 0
% 3.34/1.52  #Close   : 0
% 3.34/1.52  
% 3.34/1.52  Ordering : KBO
% 3.34/1.52  
% 3.34/1.52  Simplification rules
% 3.34/1.52  ----------------------
% 3.34/1.52  #Subsume      : 20
% 3.34/1.52  #Demod        : 106
% 3.34/1.52  #Tautology    : 164
% 3.34/1.52  #SimpNegUnit  : 0
% 3.34/1.52  #BackRed      : 1
% 3.34/1.52  
% 3.34/1.52  #Partial instantiations: 0
% 3.34/1.52  #Strategies tried      : 1
% 3.34/1.52  
% 3.34/1.52  Timing (in seconds)
% 3.34/1.52  ----------------------
% 3.34/1.52  Preprocessing        : 0.33
% 3.34/1.52  Parsing              : 0.17
% 3.34/1.52  CNF conversion       : 0.02
% 3.34/1.52  Main loop            : 0.43
% 3.34/1.52  Inferencing          : 0.15
% 3.34/1.52  Reduction            : 0.17
% 3.34/1.52  Demodulation         : 0.15
% 3.34/1.52  BG Simplification    : 0.03
% 3.34/1.52  Subsumption          : 0.06
% 3.34/1.52  Abstraction          : 0.03
% 3.39/1.52  MUC search           : 0.00
% 3.39/1.52  Cooper               : 0.00
% 3.39/1.52  Total                : 0.79
% 3.39/1.52  Index Insertion      : 0.00
% 3.39/1.52  Index Deletion       : 0.00
% 3.39/1.52  Index Matching       : 0.00
% 3.39/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
