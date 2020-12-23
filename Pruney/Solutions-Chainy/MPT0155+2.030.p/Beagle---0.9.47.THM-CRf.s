%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:12 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   40 (  50 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   25 (  35 expanded)
%              Number of equality atoms :   24 (  34 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k1_tarski(A_3),k2_tarski(B_4,C_5)) = k1_enumset1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_27,B_28] : k1_enumset1(A_27,A_27,B_28) = k2_tarski(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_58,plain,(
    ! [A_37,B_38,C_39,D_40] : k2_xboole_0(k1_tarski(A_37),k1_enumset1(B_38,C_39,D_40)) = k2_enumset1(A_37,B_38,C_39,D_40) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [A_37,A_27,B_28] : k2_xboole_0(k1_tarski(A_37),k2_tarski(A_27,B_28)) = k2_enumset1(A_37,A_27,A_27,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_58])).

tff(c_70,plain,(
    ! [A_37,A_27,B_28] : k2_enumset1(A_37,A_27,A_27,B_28) = k1_enumset1(A_37,A_27,B_28) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_67])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8,D_9] : k2_xboole_0(k1_tarski(A_6),k1_enumset1(B_7,C_8,D_9)) = k2_enumset1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_158,plain,(
    ! [A_50,A_51,B_52] : k2_enumset1(A_50,A_51,A_51,B_52) = k1_enumset1(A_50,A_51,B_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_67])).

tff(c_8,plain,(
    ! [B_11,A_10,C_12,E_14,D_13] : k2_xboole_0(k1_tarski(A_10),k2_enumset1(B_11,C_12,D_13,E_14)) = k3_enumset1(A_10,B_11,C_12,D_13,E_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_164,plain,(
    ! [A_10,A_50,A_51,B_52] : k3_enumset1(A_10,A_50,A_51,A_51,B_52) = k2_xboole_0(k1_tarski(A_10),k1_enumset1(A_50,A_51,B_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_8])).

tff(c_275,plain,(
    ! [A_65,A_66,A_67,B_68] : k3_enumset1(A_65,A_66,A_67,A_67,B_68) = k2_enumset1(A_65,A_66,A_67,B_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_164])).

tff(c_14,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_243,plain,(
    ! [C_56,A_60,E_59,B_58,D_57] : k2_xboole_0(k2_tarski(A_60,B_58),k1_enumset1(C_56,D_57,E_59)) = k3_enumset1(A_60,B_58,C_56,D_57,E_59) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_261,plain,(
    ! [A_26,C_56,D_57,E_59] : k3_enumset1(A_26,A_26,C_56,D_57,E_59) = k2_xboole_0(k1_tarski(A_26),k1_enumset1(C_56,D_57,E_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_243])).

tff(c_264,plain,(
    ! [A_26,C_56,D_57,E_59] : k3_enumset1(A_26,A_26,C_56,D_57,E_59) = k2_enumset1(A_26,C_56,D_57,E_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_261])).

tff(c_282,plain,(
    ! [A_66,A_67,B_68] : k2_enumset1(A_66,A_67,A_67,B_68) = k2_enumset1(A_66,A_66,A_67,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_264])).

tff(c_291,plain,(
    ! [A_66,A_67,B_68] : k2_enumset1(A_66,A_66,A_67,B_68) = k1_enumset1(A_66,A_67,B_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_282])).

tff(c_18,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.19  
% 1.93/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.19  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.93/1.19  
% 1.93/1.19  %Foreground sorts:
% 1.93/1.19  
% 1.93/1.19  
% 1.93/1.19  %Background operators:
% 1.93/1.19  
% 1.93/1.19  
% 1.93/1.19  %Foreground operators:
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.93/1.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.93/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.19  
% 1.93/1.20  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 1.93/1.20  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.93/1.20  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 1.93/1.20  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 1.93/1.20  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.93/1.20  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 1.93/1.20  tff(f_44, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.93/1.20  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k1_tarski(A_3), k2_tarski(B_4, C_5))=k1_enumset1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.20  tff(c_16, plain, (![A_27, B_28]: (k1_enumset1(A_27, A_27, B_28)=k2_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.93/1.20  tff(c_58, plain, (![A_37, B_38, C_39, D_40]: (k2_xboole_0(k1_tarski(A_37), k1_enumset1(B_38, C_39, D_40))=k2_enumset1(A_37, B_38, C_39, D_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.20  tff(c_67, plain, (![A_37, A_27, B_28]: (k2_xboole_0(k1_tarski(A_37), k2_tarski(A_27, B_28))=k2_enumset1(A_37, A_27, A_27, B_28))), inference(superposition, [status(thm), theory('equality')], [c_16, c_58])).
% 1.93/1.20  tff(c_70, plain, (![A_37, A_27, B_28]: (k2_enumset1(A_37, A_27, A_27, B_28)=k1_enumset1(A_37, A_27, B_28))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_67])).
% 1.93/1.20  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k2_xboole_0(k1_tarski(A_6), k1_enumset1(B_7, C_8, D_9))=k2_enumset1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.20  tff(c_158, plain, (![A_50, A_51, B_52]: (k2_enumset1(A_50, A_51, A_51, B_52)=k1_enumset1(A_50, A_51, B_52))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_67])).
% 1.93/1.20  tff(c_8, plain, (![B_11, A_10, C_12, E_14, D_13]: (k2_xboole_0(k1_tarski(A_10), k2_enumset1(B_11, C_12, D_13, E_14))=k3_enumset1(A_10, B_11, C_12, D_13, E_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.20  tff(c_164, plain, (![A_10, A_50, A_51, B_52]: (k3_enumset1(A_10, A_50, A_51, A_51, B_52)=k2_xboole_0(k1_tarski(A_10), k1_enumset1(A_50, A_51, B_52)))), inference(superposition, [status(thm), theory('equality')], [c_158, c_8])).
% 1.93/1.20  tff(c_275, plain, (![A_65, A_66, A_67, B_68]: (k3_enumset1(A_65, A_66, A_67, A_67, B_68)=k2_enumset1(A_65, A_66, A_67, B_68))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_164])).
% 1.93/1.20  tff(c_14, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.93/1.20  tff(c_243, plain, (![C_56, A_60, E_59, B_58, D_57]: (k2_xboole_0(k2_tarski(A_60, B_58), k1_enumset1(C_56, D_57, E_59))=k3_enumset1(A_60, B_58, C_56, D_57, E_59))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.20  tff(c_261, plain, (![A_26, C_56, D_57, E_59]: (k3_enumset1(A_26, A_26, C_56, D_57, E_59)=k2_xboole_0(k1_tarski(A_26), k1_enumset1(C_56, D_57, E_59)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_243])).
% 1.93/1.20  tff(c_264, plain, (![A_26, C_56, D_57, E_59]: (k3_enumset1(A_26, A_26, C_56, D_57, E_59)=k2_enumset1(A_26, C_56, D_57, E_59))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_261])).
% 1.93/1.20  tff(c_282, plain, (![A_66, A_67, B_68]: (k2_enumset1(A_66, A_67, A_67, B_68)=k2_enumset1(A_66, A_66, A_67, B_68))), inference(superposition, [status(thm), theory('equality')], [c_275, c_264])).
% 1.93/1.20  tff(c_291, plain, (![A_66, A_67, B_68]: (k2_enumset1(A_66, A_66, A_67, B_68)=k1_enumset1(A_66, A_67, B_68))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_282])).
% 1.93/1.20  tff(c_18, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.93/1.20  tff(c_313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_291, c_18])).
% 1.93/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  Inference rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Ref     : 0
% 1.93/1.20  #Sup     : 69
% 1.93/1.20  #Fact    : 0
% 1.93/1.20  #Define  : 0
% 1.93/1.20  #Split   : 0
% 1.93/1.20  #Chain   : 0
% 1.93/1.20  #Close   : 0
% 1.93/1.20  
% 1.93/1.20  Ordering : KBO
% 1.93/1.20  
% 1.93/1.20  Simplification rules
% 1.93/1.20  ----------------------
% 1.93/1.20  #Subsume      : 2
% 1.93/1.20  #Demod        : 27
% 1.93/1.20  #Tautology    : 49
% 1.93/1.20  #SimpNegUnit  : 0
% 1.93/1.20  #BackRed      : 1
% 1.93/1.20  
% 1.93/1.20  #Partial instantiations: 0
% 1.93/1.20  #Strategies tried      : 1
% 1.93/1.20  
% 1.93/1.20  Timing (in seconds)
% 1.93/1.20  ----------------------
% 1.93/1.21  Preprocessing        : 0.28
% 1.93/1.21  Parsing              : 0.15
% 1.93/1.21  CNF conversion       : 0.01
% 1.93/1.21  Main loop            : 0.17
% 1.93/1.21  Inferencing          : 0.08
% 1.93/1.21  Reduction            : 0.06
% 1.93/1.21  Demodulation         : 0.05
% 1.93/1.21  BG Simplification    : 0.01
% 1.93/1.21  Subsumption          : 0.02
% 1.93/1.21  Abstraction          : 0.01
% 1.93/1.21  MUC search           : 0.00
% 1.93/1.21  Cooper               : 0.00
% 1.93/1.21  Total                : 0.47
% 1.93/1.21  Index Insertion      : 0.00
% 1.93/1.21  Index Deletion       : 0.00
% 1.93/1.21  Index Matching       : 0.00
% 1.93/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
