%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:35 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  71 expanded)
%              Number of leaves         :   18 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :   26 (  59 expanded)
%              Number of equality atoms :   25 (  58 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_33,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_enumset1(A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C] : k6_enumset1(A,A,A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_enumset1)).

tff(c_4,plain,(
    ! [A_7,B_8,C_9,D_10] : k2_xboole_0(k1_tarski(A_7),k1_enumset1(B_8,C_9,D_10)) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_19] : k1_enumset1(A_19,A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    ! [B_36,C_37,A_38,F_33,E_34,D_35] : k2_xboole_0(k1_enumset1(A_38,B_36,C_37),k1_enumset1(D_35,E_34,F_33)) = k4_enumset1(A_38,B_36,C_37,D_35,E_34,F_33) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_69,plain,(
    ! [A_19,D_35,E_34,F_33] : k4_enumset1(A_19,A_19,A_19,D_35,E_34,F_33) = k2_xboole_0(k1_tarski(A_19),k1_enumset1(D_35,E_34,F_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_60])).

tff(c_76,plain,(
    ! [A_39,D_40,E_41,F_42] : k4_enumset1(A_39,A_39,A_39,D_40,E_41,F_42) = k2_enumset1(A_39,D_40,E_41,F_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_69])).

tff(c_10,plain,(
    ! [A_20,B_21,C_22] : k4_enumset1(A_20,A_20,A_20,A_20,B_21,C_22) = k1_enumset1(A_20,B_21,C_22) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_83,plain,(
    ! [D_40,E_41,F_42] : k2_enumset1(D_40,D_40,E_41,F_42) = k1_enumset1(D_40,E_41,F_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_10])).

tff(c_92,plain,(
    ! [D_43,E_44,F_45] : k2_enumset1(D_43,D_43,E_44,F_45) = k1_enumset1(D_43,E_44,F_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_10])).

tff(c_31,plain,(
    ! [A_27,B_28,C_29,D_30] : k2_xboole_0(k1_tarski(A_27),k1_enumset1(B_28,C_29,D_30)) = k2_enumset1(A_27,B_28,C_29,D_30) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    ! [A_27,A_19] : k2_xboole_0(k1_tarski(A_27),k1_tarski(A_19)) = k2_enumset1(A_27,A_19,A_19,A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_31])).

tff(c_99,plain,(
    ! [F_45] : k2_xboole_0(k1_tarski(F_45),k1_tarski(F_45)) = k1_enumset1(F_45,F_45,F_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_40])).

tff(c_111,plain,(
    ! [F_46] : k2_xboole_0(k1_tarski(F_46),k1_tarski(F_46)) = k1_tarski(F_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_99])).

tff(c_149,plain,(
    ! [F_55] : k2_enumset1(F_55,F_55,F_55,F_55) = k1_tarski(F_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_40])).

tff(c_6,plain,(
    ! [G_17,F_16,D_14,E_15,H_18,B_12,A_11,C_13] : k2_xboole_0(k2_enumset1(A_11,B_12,C_13,D_14),k2_enumset1(E_15,F_16,G_17,H_18)) = k6_enumset1(A_11,B_12,C_13,D_14,E_15,F_16,G_17,H_18) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_354,plain,(
    ! [F_68,H_72,F_71,E_70,G_69] : k6_enumset1(F_71,F_71,F_71,F_71,E_70,F_68,G_69,H_72) = k2_xboole_0(k1_tarski(F_71),k2_enumset1(E_70,F_68,G_69,H_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_6])).

tff(c_380,plain,(
    ! [F_71,D_40,E_41,F_42] : k6_enumset1(F_71,F_71,F_71,F_71,D_40,D_40,E_41,F_42) = k2_xboole_0(k1_tarski(F_71),k1_enumset1(D_40,E_41,F_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_354])).

tff(c_390,plain,(
    ! [F_71,D_40,E_41,F_42] : k6_enumset1(F_71,F_71,F_71,F_71,D_40,D_40,E_41,F_42) = k2_enumset1(F_71,D_40,E_41,F_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_380])).

tff(c_12,plain,(
    k6_enumset1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_484,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_12])).

tff(c_487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:55:26 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.39  
% 2.21/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.39  %$ k6_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.21/1.39  
% 2.21/1.39  %Foreground sorts:
% 2.21/1.39  
% 2.21/1.39  
% 2.21/1.39  %Background operators:
% 2.21/1.39  
% 2.21/1.39  
% 2.21/1.39  %Foreground operators:
% 2.21/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.21/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.21/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.21/1.39  
% 2.21/1.40  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 2.21/1.40  tff(f_33, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 2.21/1.40  tff(f_27, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 2.21/1.40  tff(f_35, axiom, (![A, B, C]: (k4_enumset1(A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_enumset1)).
% 2.21/1.40  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_enumset1)).
% 2.21/1.40  tff(f_38, negated_conjecture, ~(![A, B, C]: (k6_enumset1(A, A, A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_enumset1)).
% 2.21/1.40  tff(c_4, plain, (![A_7, B_8, C_9, D_10]: (k2_xboole_0(k1_tarski(A_7), k1_enumset1(B_8, C_9, D_10))=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.40  tff(c_8, plain, (![A_19]: (k1_enumset1(A_19, A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.21/1.40  tff(c_60, plain, (![B_36, C_37, A_38, F_33, E_34, D_35]: (k2_xboole_0(k1_enumset1(A_38, B_36, C_37), k1_enumset1(D_35, E_34, F_33))=k4_enumset1(A_38, B_36, C_37, D_35, E_34, F_33))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.40  tff(c_69, plain, (![A_19, D_35, E_34, F_33]: (k4_enumset1(A_19, A_19, A_19, D_35, E_34, F_33)=k2_xboole_0(k1_tarski(A_19), k1_enumset1(D_35, E_34, F_33)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_60])).
% 2.21/1.40  tff(c_76, plain, (![A_39, D_40, E_41, F_42]: (k4_enumset1(A_39, A_39, A_39, D_40, E_41, F_42)=k2_enumset1(A_39, D_40, E_41, F_42))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_69])).
% 2.21/1.40  tff(c_10, plain, (![A_20, B_21, C_22]: (k4_enumset1(A_20, A_20, A_20, A_20, B_21, C_22)=k1_enumset1(A_20, B_21, C_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.21/1.40  tff(c_83, plain, (![D_40, E_41, F_42]: (k2_enumset1(D_40, D_40, E_41, F_42)=k1_enumset1(D_40, E_41, F_42))), inference(superposition, [status(thm), theory('equality')], [c_76, c_10])).
% 2.21/1.40  tff(c_92, plain, (![D_43, E_44, F_45]: (k2_enumset1(D_43, D_43, E_44, F_45)=k1_enumset1(D_43, E_44, F_45))), inference(superposition, [status(thm), theory('equality')], [c_76, c_10])).
% 2.21/1.40  tff(c_31, plain, (![A_27, B_28, C_29, D_30]: (k2_xboole_0(k1_tarski(A_27), k1_enumset1(B_28, C_29, D_30))=k2_enumset1(A_27, B_28, C_29, D_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.40  tff(c_40, plain, (![A_27, A_19]: (k2_xboole_0(k1_tarski(A_27), k1_tarski(A_19))=k2_enumset1(A_27, A_19, A_19, A_19))), inference(superposition, [status(thm), theory('equality')], [c_8, c_31])).
% 2.21/1.40  tff(c_99, plain, (![F_45]: (k2_xboole_0(k1_tarski(F_45), k1_tarski(F_45))=k1_enumset1(F_45, F_45, F_45))), inference(superposition, [status(thm), theory('equality')], [c_92, c_40])).
% 2.21/1.40  tff(c_111, plain, (![F_46]: (k2_xboole_0(k1_tarski(F_46), k1_tarski(F_46))=k1_tarski(F_46))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_99])).
% 2.21/1.40  tff(c_149, plain, (![F_55]: (k2_enumset1(F_55, F_55, F_55, F_55)=k1_tarski(F_55))), inference(superposition, [status(thm), theory('equality')], [c_111, c_40])).
% 2.21/1.40  tff(c_6, plain, (![G_17, F_16, D_14, E_15, H_18, B_12, A_11, C_13]: (k2_xboole_0(k2_enumset1(A_11, B_12, C_13, D_14), k2_enumset1(E_15, F_16, G_17, H_18))=k6_enumset1(A_11, B_12, C_13, D_14, E_15, F_16, G_17, H_18))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.21/1.40  tff(c_354, plain, (![F_68, H_72, F_71, E_70, G_69]: (k6_enumset1(F_71, F_71, F_71, F_71, E_70, F_68, G_69, H_72)=k2_xboole_0(k1_tarski(F_71), k2_enumset1(E_70, F_68, G_69, H_72)))), inference(superposition, [status(thm), theory('equality')], [c_149, c_6])).
% 2.21/1.40  tff(c_380, plain, (![F_71, D_40, E_41, F_42]: (k6_enumset1(F_71, F_71, F_71, F_71, D_40, D_40, E_41, F_42)=k2_xboole_0(k1_tarski(F_71), k1_enumset1(D_40, E_41, F_42)))), inference(superposition, [status(thm), theory('equality')], [c_83, c_354])).
% 2.21/1.40  tff(c_390, plain, (![F_71, D_40, E_41, F_42]: (k6_enumset1(F_71, F_71, F_71, F_71, D_40, D_40, E_41, F_42)=k2_enumset1(F_71, D_40, E_41, F_42))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_380])).
% 2.21/1.40  tff(c_12, plain, (k6_enumset1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.21/1.40  tff(c_484, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_390, c_12])).
% 2.21/1.40  tff(c_487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_484])).
% 2.21/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.40  
% 2.21/1.40  Inference rules
% 2.21/1.40  ----------------------
% 2.21/1.40  #Ref     : 0
% 2.21/1.40  #Sup     : 112
% 2.21/1.40  #Fact    : 0
% 2.21/1.40  #Define  : 0
% 2.21/1.40  #Split   : 0
% 2.21/1.40  #Chain   : 0
% 2.21/1.40  #Close   : 0
% 2.21/1.40  
% 2.21/1.40  Ordering : KBO
% 2.21/1.40  
% 2.21/1.40  Simplification rules
% 2.21/1.40  ----------------------
% 2.21/1.40  #Subsume      : 5
% 2.21/1.40  #Demod        : 77
% 2.21/1.40  #Tautology    : 83
% 2.21/1.40  #SimpNegUnit  : 0
% 2.21/1.40  #BackRed      : 1
% 2.21/1.40  
% 2.21/1.40  #Partial instantiations: 0
% 2.21/1.40  #Strategies tried      : 1
% 2.21/1.40  
% 2.21/1.40  Timing (in seconds)
% 2.21/1.40  ----------------------
% 2.21/1.40  Preprocessing        : 0.37
% 2.21/1.40  Parsing              : 0.20
% 2.21/1.40  CNF conversion       : 0.02
% 2.21/1.40  Main loop            : 0.23
% 2.21/1.40  Inferencing          : 0.10
% 2.21/1.40  Reduction            : 0.08
% 2.21/1.40  Demodulation         : 0.07
% 2.21/1.40  BG Simplification    : 0.02
% 2.21/1.40  Subsumption          : 0.02
% 2.21/1.40  Abstraction          : 0.02
% 2.21/1.40  MUC search           : 0.00
% 2.21/1.40  Cooper               : 0.00
% 2.21/1.40  Total                : 0.63
% 2.21/1.40  Index Insertion      : 0.00
% 2.21/1.40  Index Deletion       : 0.00
% 2.21/1.40  Index Matching       : 0.00
% 2.21/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
