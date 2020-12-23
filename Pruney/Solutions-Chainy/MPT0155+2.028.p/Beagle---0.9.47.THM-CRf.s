%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:12 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   41 (  50 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   26 (  35 expanded)
%              Number of equality atoms :   25 (  34 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_8,plain,(
    ! [A_8,B_9,C_10,D_11] : k2_xboole_0(k1_tarski(A_8),k1_enumset1(B_9,C_10,D_11)) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_301,plain,(
    ! [C_65,D_64,B_61,E_63,A_62] : k2_xboole_0(k2_tarski(A_62,B_61),k1_enumset1(C_65,D_64,E_63)) = k3_enumset1(A_62,B_61,C_65,D_64,E_63) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_319,plain,(
    ! [A_22,C_65,D_64,E_63] : k3_enumset1(A_22,A_22,C_65,D_64,E_63) = k2_xboole_0(k1_tarski(A_22),k1_enumset1(C_65,D_64,E_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_301])).

tff(c_323,plain,(
    ! [A_66,C_67,D_68,E_69] : k3_enumset1(A_66,A_66,C_67,D_68,E_69) = k2_enumset1(A_66,C_67,D_68,E_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_319])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k2_xboole_0(k1_tarski(A_5),k2_tarski(B_6,C_7)) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ! [A_32,B_33,C_34] : k2_xboole_0(k1_tarski(A_32),k2_tarski(B_33,C_34)) = k1_enumset1(A_32,B_33,C_34) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [A_35,A_36] : k2_xboole_0(k1_tarski(A_35),k1_tarski(A_36)) = k1_enumset1(A_35,A_36,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_55])).

tff(c_16,plain,(
    ! [A_23,B_24] : k1_enumset1(A_23,A_23,B_24) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_77,plain,(
    ! [A_36] : k2_xboole_0(k1_tarski(A_36),k1_tarski(A_36)) = k2_tarski(A_36,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_16])).

tff(c_94,plain,(
    ! [A_37] : k2_xboole_0(k1_tarski(A_37),k1_tarski(A_37)) = k1_tarski(A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_77])).

tff(c_64,plain,(
    ! [A_32,A_22] : k2_xboole_0(k1_tarski(A_32),k1_tarski(A_22)) = k1_enumset1(A_32,A_22,A_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_55])).

tff(c_100,plain,(
    ! [A_37] : k1_enumset1(A_37,A_37,A_37) = k1_tarski(A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_64])).

tff(c_233,plain,(
    ! [A_50,B_51,D_52,C_49,E_53] : k2_xboole_0(k1_enumset1(A_50,B_51,C_49),k2_tarski(D_52,E_53)) = k3_enumset1(A_50,B_51,C_49,D_52,E_53) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_242,plain,(
    ! [A_37,D_52,E_53] : k3_enumset1(A_37,A_37,A_37,D_52,E_53) = k2_xboole_0(k1_tarski(A_37),k2_tarski(D_52,E_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_233])).

tff(c_254,plain,(
    ! [A_37,D_52,E_53] : k3_enumset1(A_37,A_37,A_37,D_52,E_53) = k1_enumset1(A_37,D_52,E_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_242])).

tff(c_334,plain,(
    ! [C_67,D_68,E_69] : k2_enumset1(C_67,C_67,D_68,E_69) = k1_enumset1(C_67,D_68,E_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_254])).

tff(c_18,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:46:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.23  
% 1.89/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.23  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.89/1.23  
% 1.89/1.23  %Foreground sorts:
% 1.89/1.23  
% 1.89/1.23  
% 1.89/1.23  %Background operators:
% 1.89/1.23  
% 1.89/1.23  
% 1.89/1.23  %Foreground operators:
% 1.89/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.89/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.89/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.89/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.89/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.89/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.89/1.23  
% 2.06/1.24  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.06/1.24  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.06/1.24  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 2.06/1.24  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.06/1.24  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.06/1.24  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_enumset1)).
% 2.06/1.24  tff(f_44, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.06/1.24  tff(c_8, plain, (![A_8, B_9, C_10, D_11]: (k2_xboole_0(k1_tarski(A_8), k1_enumset1(B_9, C_10, D_11))=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.24  tff(c_14, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.24  tff(c_301, plain, (![C_65, D_64, B_61, E_63, A_62]: (k2_xboole_0(k2_tarski(A_62, B_61), k1_enumset1(C_65, D_64, E_63))=k3_enumset1(A_62, B_61, C_65, D_64, E_63))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.24  tff(c_319, plain, (![A_22, C_65, D_64, E_63]: (k3_enumset1(A_22, A_22, C_65, D_64, E_63)=k2_xboole_0(k1_tarski(A_22), k1_enumset1(C_65, D_64, E_63)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_301])).
% 2.06/1.24  tff(c_323, plain, (![A_66, C_67, D_68, E_69]: (k3_enumset1(A_66, A_66, C_67, D_68, E_69)=k2_enumset1(A_66, C_67, D_68, E_69))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_319])).
% 2.06/1.24  tff(c_6, plain, (![A_5, B_6, C_7]: (k2_xboole_0(k1_tarski(A_5), k2_tarski(B_6, C_7))=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.24  tff(c_55, plain, (![A_32, B_33, C_34]: (k2_xboole_0(k1_tarski(A_32), k2_tarski(B_33, C_34))=k1_enumset1(A_32, B_33, C_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.24  tff(c_67, plain, (![A_35, A_36]: (k2_xboole_0(k1_tarski(A_35), k1_tarski(A_36))=k1_enumset1(A_35, A_36, A_36))), inference(superposition, [status(thm), theory('equality')], [c_14, c_55])).
% 2.06/1.24  tff(c_16, plain, (![A_23, B_24]: (k1_enumset1(A_23, A_23, B_24)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.06/1.24  tff(c_77, plain, (![A_36]: (k2_xboole_0(k1_tarski(A_36), k1_tarski(A_36))=k2_tarski(A_36, A_36))), inference(superposition, [status(thm), theory('equality')], [c_67, c_16])).
% 2.06/1.24  tff(c_94, plain, (![A_37]: (k2_xboole_0(k1_tarski(A_37), k1_tarski(A_37))=k1_tarski(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_77])).
% 2.06/1.24  tff(c_64, plain, (![A_32, A_22]: (k2_xboole_0(k1_tarski(A_32), k1_tarski(A_22))=k1_enumset1(A_32, A_22, A_22))), inference(superposition, [status(thm), theory('equality')], [c_14, c_55])).
% 2.06/1.24  tff(c_100, plain, (![A_37]: (k1_enumset1(A_37, A_37, A_37)=k1_tarski(A_37))), inference(superposition, [status(thm), theory('equality')], [c_94, c_64])).
% 2.06/1.24  tff(c_233, plain, (![A_50, B_51, D_52, C_49, E_53]: (k2_xboole_0(k1_enumset1(A_50, B_51, C_49), k2_tarski(D_52, E_53))=k3_enumset1(A_50, B_51, C_49, D_52, E_53))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.06/1.24  tff(c_242, plain, (![A_37, D_52, E_53]: (k3_enumset1(A_37, A_37, A_37, D_52, E_53)=k2_xboole_0(k1_tarski(A_37), k2_tarski(D_52, E_53)))), inference(superposition, [status(thm), theory('equality')], [c_100, c_233])).
% 2.06/1.24  tff(c_254, plain, (![A_37, D_52, E_53]: (k3_enumset1(A_37, A_37, A_37, D_52, E_53)=k1_enumset1(A_37, D_52, E_53))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_242])).
% 2.06/1.24  tff(c_334, plain, (![C_67, D_68, E_69]: (k2_enumset1(C_67, C_67, D_68, E_69)=k1_enumset1(C_67, D_68, E_69))), inference(superposition, [status(thm), theory('equality')], [c_323, c_254])).
% 2.06/1.24  tff(c_18, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.06/1.24  tff(c_351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_334, c_18])).
% 2.06/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.24  
% 2.06/1.24  Inference rules
% 2.06/1.24  ----------------------
% 2.06/1.24  #Ref     : 0
% 2.06/1.24  #Sup     : 79
% 2.06/1.24  #Fact    : 0
% 2.06/1.24  #Define  : 0
% 2.06/1.24  #Split   : 0
% 2.06/1.24  #Chain   : 0
% 2.06/1.24  #Close   : 0
% 2.06/1.24  
% 2.06/1.24  Ordering : KBO
% 2.06/1.24  
% 2.06/1.24  Simplification rules
% 2.06/1.24  ----------------------
% 2.06/1.24  #Subsume      : 4
% 2.06/1.24  #Demod        : 29
% 2.06/1.24  #Tautology    : 53
% 2.06/1.24  #SimpNegUnit  : 0
% 2.06/1.24  #BackRed      : 1
% 2.06/1.24  
% 2.06/1.24  #Partial instantiations: 0
% 2.06/1.24  #Strategies tried      : 1
% 2.06/1.24  
% 2.06/1.24  Timing (in seconds)
% 2.06/1.24  ----------------------
% 2.06/1.24  Preprocessing        : 0.28
% 2.06/1.24  Parsing              : 0.15
% 2.06/1.24  CNF conversion       : 0.02
% 2.06/1.24  Main loop            : 0.18
% 2.06/1.24  Inferencing          : 0.08
% 2.06/1.25  Reduction            : 0.07
% 2.06/1.25  Demodulation         : 0.05
% 2.06/1.25  BG Simplification    : 0.01
% 2.06/1.25  Subsumption          : 0.02
% 2.06/1.25  Abstraction          : 0.01
% 2.06/1.25  MUC search           : 0.00
% 2.06/1.25  Cooper               : 0.00
% 2.06/1.25  Total                : 0.49
% 2.06/1.25  Index Insertion      : 0.00
% 2.06/1.25  Index Deletion       : 0.00
% 2.06/1.25  Index Matching       : 0.00
% 2.06/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
