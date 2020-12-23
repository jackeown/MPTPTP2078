%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:06 EST 2020

% Result     : Theorem 6.42s
% Output     : CNFRefutation 6.42s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(c_26,plain,(
    ! [A_26,B_27,C_28] : k2_xboole_0(k1_tarski(A_26),k2_tarski(B_27,C_28)) = k1_enumset1(A_26,B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_24,B_25] : k2_xboole_0(k1_tarski(A_24),k1_tarski(B_25)) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [A_38] : k2_tarski(A_38,A_38) = k1_tarski(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_423,plain,(
    ! [A_68,B_69,C_70] : k2_xboole_0(k1_tarski(A_68),k2_tarski(B_69,C_70)) = k1_enumset1(A_68,B_69,C_70) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_438,plain,(
    ! [A_68,A_38] : k2_xboole_0(k1_tarski(A_68),k1_tarski(A_38)) = k1_enumset1(A_68,A_38,A_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_423])).

tff(c_623,plain,(
    ! [A_84,A_85] : k1_enumset1(A_84,A_85,A_85) = k2_tarski(A_84,A_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_438])).

tff(c_28,plain,(
    ! [A_29,B_30,C_31,D_32] : k2_xboole_0(k1_tarski(A_29),k1_enumset1(B_30,C_31,D_32)) = k2_enumset1(A_29,B_30,C_31,D_32) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_632,plain,(
    ! [A_29,A_84,A_85] : k2_xboole_0(k1_tarski(A_29),k2_tarski(A_84,A_85)) = k2_enumset1(A_29,A_84,A_85,A_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_28])).

tff(c_8274,plain,(
    ! [A_272,A_273,A_274] : k2_enumset1(A_272,A_273,A_274,A_274) = k1_enumset1(A_272,A_273,A_274) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_632])).

tff(c_703,plain,(
    ! [A_88,B_89,C_90,D_91] : k2_xboole_0(k2_tarski(A_88,B_89),k2_tarski(C_90,D_91)) = k2_enumset1(A_88,B_89,C_90,D_91) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2911,plain,(
    ! [A_172,B_173,A_174] : k2_xboole_0(k2_tarski(A_172,B_173),k1_tarski(A_174)) = k2_enumset1(A_172,B_173,A_174,A_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_703])).

tff(c_2969,plain,(
    ! [A_38,A_174] : k2_xboole_0(k1_tarski(A_38),k1_tarski(A_174)) = k2_enumset1(A_38,A_38,A_174,A_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2911])).

tff(c_2980,plain,(
    ! [A_38,A_174] : k2_enumset1(A_38,A_38,A_174,A_174) = k2_tarski(A_38,A_174) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2969])).

tff(c_8285,plain,(
    ! [A_273,A_274] : k1_enumset1(A_273,A_273,A_274) = k2_tarski(A_273,A_274) ),
    inference(superposition,[status(thm),theory(equality)],[c_8274,c_2980])).

tff(c_34,plain,(
    k1_enumset1('#skF_1','#skF_1','#skF_2') != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8285,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:16:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.42/2.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.42/2.43  
% 6.42/2.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.42/2.43  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 6.42/2.43  
% 6.42/2.43  %Foreground sorts:
% 6.42/2.43  
% 6.42/2.43  
% 6.42/2.43  %Background operators:
% 6.42/2.43  
% 6.42/2.43  
% 6.42/2.43  %Foreground operators:
% 6.42/2.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.42/2.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.42/2.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.42/2.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.42/2.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.42/2.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.42/2.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.42/2.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.42/2.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.42/2.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.42/2.43  tff('#skF_2', type, '#skF_2': $i).
% 6.42/2.43  tff('#skF_1', type, '#skF_1': $i).
% 6.42/2.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.42/2.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.42/2.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.42/2.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.42/2.43  
% 6.42/2.44  tff(f_53, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 6.42/2.44  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 6.42/2.44  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.42/2.44  tff(f_55, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 6.42/2.44  tff(f_49, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 6.42/2.44  tff(f_62, negated_conjecture, ~(![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.42/2.44  tff(c_26, plain, (![A_26, B_27, C_28]: (k2_xboole_0(k1_tarski(A_26), k2_tarski(B_27, C_28))=k1_enumset1(A_26, B_27, C_28))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.42/2.44  tff(c_24, plain, (![A_24, B_25]: (k2_xboole_0(k1_tarski(A_24), k1_tarski(B_25))=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.42/2.44  tff(c_32, plain, (![A_38]: (k2_tarski(A_38, A_38)=k1_tarski(A_38))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.42/2.44  tff(c_423, plain, (![A_68, B_69, C_70]: (k2_xboole_0(k1_tarski(A_68), k2_tarski(B_69, C_70))=k1_enumset1(A_68, B_69, C_70))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.42/2.44  tff(c_438, plain, (![A_68, A_38]: (k2_xboole_0(k1_tarski(A_68), k1_tarski(A_38))=k1_enumset1(A_68, A_38, A_38))), inference(superposition, [status(thm), theory('equality')], [c_32, c_423])).
% 6.42/2.44  tff(c_623, plain, (![A_84, A_85]: (k1_enumset1(A_84, A_85, A_85)=k2_tarski(A_84, A_85))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_438])).
% 6.42/2.44  tff(c_28, plain, (![A_29, B_30, C_31, D_32]: (k2_xboole_0(k1_tarski(A_29), k1_enumset1(B_30, C_31, D_32))=k2_enumset1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.42/2.44  tff(c_632, plain, (![A_29, A_84, A_85]: (k2_xboole_0(k1_tarski(A_29), k2_tarski(A_84, A_85))=k2_enumset1(A_29, A_84, A_85, A_85))), inference(superposition, [status(thm), theory('equality')], [c_623, c_28])).
% 6.42/2.44  tff(c_8274, plain, (![A_272, A_273, A_274]: (k2_enumset1(A_272, A_273, A_274, A_274)=k1_enumset1(A_272, A_273, A_274))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_632])).
% 6.42/2.44  tff(c_703, plain, (![A_88, B_89, C_90, D_91]: (k2_xboole_0(k2_tarski(A_88, B_89), k2_tarski(C_90, D_91))=k2_enumset1(A_88, B_89, C_90, D_91))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.42/2.44  tff(c_2911, plain, (![A_172, B_173, A_174]: (k2_xboole_0(k2_tarski(A_172, B_173), k1_tarski(A_174))=k2_enumset1(A_172, B_173, A_174, A_174))), inference(superposition, [status(thm), theory('equality')], [c_32, c_703])).
% 6.42/2.44  tff(c_2969, plain, (![A_38, A_174]: (k2_xboole_0(k1_tarski(A_38), k1_tarski(A_174))=k2_enumset1(A_38, A_38, A_174, A_174))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2911])).
% 6.42/2.44  tff(c_2980, plain, (![A_38, A_174]: (k2_enumset1(A_38, A_38, A_174, A_174)=k2_tarski(A_38, A_174))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2969])).
% 6.42/2.44  tff(c_8285, plain, (![A_273, A_274]: (k1_enumset1(A_273, A_273, A_274)=k2_tarski(A_273, A_274))), inference(superposition, [status(thm), theory('equality')], [c_8274, c_2980])).
% 6.42/2.44  tff(c_34, plain, (k1_enumset1('#skF_1', '#skF_1', '#skF_2')!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.42/2.44  tff(c_8332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8285, c_34])).
% 6.42/2.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.42/2.44  
% 6.42/2.44  Inference rules
% 6.42/2.44  ----------------------
% 6.42/2.44  #Ref     : 0
% 6.42/2.44  #Sup     : 2051
% 6.42/2.44  #Fact    : 0
% 6.42/2.44  #Define  : 0
% 6.42/2.44  #Split   : 0
% 6.42/2.44  #Chain   : 0
% 6.42/2.44  #Close   : 0
% 6.42/2.44  
% 6.42/2.44  Ordering : KBO
% 6.42/2.44  
% 6.42/2.44  Simplification rules
% 6.42/2.44  ----------------------
% 6.42/2.44  #Subsume      : 11
% 6.42/2.44  #Demod        : 2147
% 6.42/2.44  #Tautology    : 1445
% 6.42/2.44  #SimpNegUnit  : 0
% 6.42/2.44  #BackRed      : 8
% 6.42/2.44  
% 6.42/2.44  #Partial instantiations: 0
% 6.42/2.44  #Strategies tried      : 1
% 6.42/2.44  
% 6.42/2.44  Timing (in seconds)
% 6.42/2.44  ----------------------
% 6.42/2.45  Preprocessing        : 0.37
% 6.42/2.45  Parsing              : 0.19
% 6.42/2.45  CNF conversion       : 0.02
% 6.42/2.45  Main loop            : 1.23
% 6.42/2.45  Inferencing          : 0.36
% 6.42/2.45  Reduction            : 0.61
% 6.42/2.45  Demodulation         : 0.52
% 6.42/2.45  BG Simplification    : 0.04
% 6.42/2.45  Subsumption          : 0.16
% 6.42/2.45  Abstraction          : 0.07
% 6.42/2.45  MUC search           : 0.00
% 6.42/2.45  Cooper               : 0.00
% 6.42/2.45  Total                : 1.64
% 6.42/2.45  Index Insertion      : 0.00
% 6.42/2.45  Index Deletion       : 0.00
% 6.42/2.45  Index Matching       : 0.00
% 6.42/2.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
