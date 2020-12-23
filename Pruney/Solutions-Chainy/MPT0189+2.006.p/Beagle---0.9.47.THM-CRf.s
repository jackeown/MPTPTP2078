%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:51 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   34 (  37 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   20 (  23 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_42,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_40,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_45,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,A,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).

tff(c_22,plain,(
    ! [A_20,C_22,B_21] : k1_enumset1(A_20,C_22,B_21) = k1_enumset1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_166,plain,(
    ! [A_45,B_46,C_47,D_48] : k2_xboole_0(k1_tarski(A_45),k1_enumset1(B_46,C_47,D_48)) = k2_enumset1(A_45,B_46,C_47,D_48) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_606,plain,(
    ! [A_71,A_72,C_73,B_74] : k2_xboole_0(k1_tarski(A_71),k1_enumset1(A_72,C_73,B_74)) = k2_enumset1(A_71,A_72,B_74,C_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_166])).

tff(c_18,plain,(
    ! [A_12,B_13,C_14,D_15] : k2_xboole_0(k1_tarski(A_12),k1_enumset1(B_13,C_14,D_15)) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_615,plain,(
    ! [A_71,A_72,C_73,B_74] : k2_enumset1(A_71,A_72,C_73,B_74) = k2_enumset1(A_71,A_72,B_74,C_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_606,c_18])).

tff(c_16,plain,(
    ! [A_8,D_11,C_10,B_9] : k2_enumset1(A_8,D_11,C_10,B_9) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_133,plain,(
    ! [A_39,B_40,C_41,D_42] : k2_xboole_0(k1_enumset1(A_39,B_40,C_41),k1_tarski(D_42)) = k2_enumset1(A_39,B_40,C_41,D_42) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_193,plain,(
    ! [D_49,A_50,B_51,C_52] : k2_xboole_0(k1_tarski(D_49),k1_enumset1(A_50,B_51,C_52)) = k2_enumset1(A_50,B_51,C_52,D_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_133])).

tff(c_199,plain,(
    ! [D_49,A_50,B_51,C_52] : k2_enumset1(D_49,A_50,B_51,C_52) = k2_enumset1(A_50,B_51,C_52,D_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_18])).

tff(c_24,plain,(
    k2_enumset1('#skF_3','#skF_4','#skF_5','#skF_6') != k2_enumset1('#skF_4','#skF_3','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_230,plain,(
    k2_enumset1('#skF_4','#skF_5','#skF_6','#skF_3') != k2_enumset1('#skF_4','#skF_3','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_24])).

tff(c_231,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_5','#skF_6') != k2_enumset1('#skF_4','#skF_3','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_230])).

tff(c_798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_615,c_231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.45  
% 2.93/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.45  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.93/1.45  
% 2.93/1.45  %Foreground sorts:
% 2.93/1.45  
% 2.93/1.45  
% 2.93/1.45  %Background operators:
% 2.93/1.45  
% 2.93/1.45  
% 2.93/1.45  %Foreground operators:
% 2.93/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.93/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.93/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.93/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.93/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.93/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.93/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.93/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.93/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.93/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.93/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.93/1.45  
% 2.93/1.46  tff(f_42, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_enumset1)).
% 2.93/1.46  tff(f_38, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.93/1.46  tff(f_36, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 2.93/1.46  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.93/1.46  tff(f_40, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.93/1.46  tff(f_45, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, A, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_enumset1)).
% 2.93/1.46  tff(c_22, plain, (![A_20, C_22, B_21]: (k1_enumset1(A_20, C_22, B_21)=k1_enumset1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.93/1.46  tff(c_166, plain, (![A_45, B_46, C_47, D_48]: (k2_xboole_0(k1_tarski(A_45), k1_enumset1(B_46, C_47, D_48))=k2_enumset1(A_45, B_46, C_47, D_48))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.93/1.46  tff(c_606, plain, (![A_71, A_72, C_73, B_74]: (k2_xboole_0(k1_tarski(A_71), k1_enumset1(A_72, C_73, B_74))=k2_enumset1(A_71, A_72, B_74, C_73))), inference(superposition, [status(thm), theory('equality')], [c_22, c_166])).
% 2.93/1.46  tff(c_18, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k1_tarski(A_12), k1_enumset1(B_13, C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.93/1.46  tff(c_615, plain, (![A_71, A_72, C_73, B_74]: (k2_enumset1(A_71, A_72, C_73, B_74)=k2_enumset1(A_71, A_72, B_74, C_73))), inference(superposition, [status(thm), theory('equality')], [c_606, c_18])).
% 2.93/1.46  tff(c_16, plain, (![A_8, D_11, C_10, B_9]: (k2_enumset1(A_8, D_11, C_10, B_9)=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.93/1.46  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.93/1.46  tff(c_133, plain, (![A_39, B_40, C_41, D_42]: (k2_xboole_0(k1_enumset1(A_39, B_40, C_41), k1_tarski(D_42))=k2_enumset1(A_39, B_40, C_41, D_42))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.93/1.46  tff(c_193, plain, (![D_49, A_50, B_51, C_52]: (k2_xboole_0(k1_tarski(D_49), k1_enumset1(A_50, B_51, C_52))=k2_enumset1(A_50, B_51, C_52, D_49))), inference(superposition, [status(thm), theory('equality')], [c_2, c_133])).
% 2.93/1.46  tff(c_199, plain, (![D_49, A_50, B_51, C_52]: (k2_enumset1(D_49, A_50, B_51, C_52)=k2_enumset1(A_50, B_51, C_52, D_49))), inference(superposition, [status(thm), theory('equality')], [c_193, c_18])).
% 2.93/1.46  tff(c_24, plain, (k2_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6')!=k2_enumset1('#skF_4', '#skF_3', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.93/1.46  tff(c_230, plain, (k2_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_3')!=k2_enumset1('#skF_4', '#skF_3', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_24])).
% 2.93/1.46  tff(c_231, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_5', '#skF_6')!=k2_enumset1('#skF_4', '#skF_3', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_230])).
% 2.93/1.46  tff(c_798, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_615, c_231])).
% 2.93/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.46  
% 2.93/1.46  Inference rules
% 2.93/1.46  ----------------------
% 2.93/1.46  #Ref     : 0
% 2.93/1.46  #Sup     : 225
% 2.93/1.46  #Fact    : 0
% 2.93/1.46  #Define  : 0
% 2.93/1.46  #Split   : 0
% 2.93/1.46  #Chain   : 0
% 2.93/1.46  #Close   : 0
% 2.93/1.46  
% 2.93/1.46  Ordering : KBO
% 2.93/1.46  
% 2.93/1.46  Simplification rules
% 2.93/1.46  ----------------------
% 2.93/1.46  #Subsume      : 59
% 2.93/1.46  #Demod        : 9
% 2.93/1.46  #Tautology    : 71
% 2.93/1.46  #SimpNegUnit  : 0
% 2.93/1.46  #BackRed      : 2
% 2.93/1.46  
% 2.93/1.46  #Partial instantiations: 0
% 2.93/1.46  #Strategies tried      : 1
% 2.93/1.46  
% 2.93/1.46  Timing (in seconds)
% 2.93/1.46  ----------------------
% 2.93/1.46  Preprocessing        : 0.30
% 2.93/1.46  Parsing              : 0.15
% 2.93/1.46  CNF conversion       : 0.02
% 2.93/1.46  Main loop            : 0.40
% 2.93/1.46  Inferencing          : 0.13
% 2.93/1.46  Reduction            : 0.17
% 2.93/1.46  Demodulation         : 0.15
% 2.93/1.46  BG Simplification    : 0.02
% 2.93/1.46  Subsumption          : 0.06
% 2.93/1.46  Abstraction          : 0.02
% 2.93/1.46  MUC search           : 0.00
% 2.93/1.46  Cooper               : 0.00
% 2.93/1.46  Total                : 0.72
% 2.93/1.46  Index Insertion      : 0.00
% 2.93/1.46  Index Deletion       : 0.00
% 2.93/1.46  Index Matching       : 0.00
% 2.93/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
