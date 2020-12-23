%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:12 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   41 (  51 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   25 (  35 expanded)
%              Number of equality atoms :   24 (  34 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k1_tarski(A_3),k2_tarski(B_4,C_5)) = k1_enumset1(A_3,B_4,C_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_60,plain,(
    ! [A_46,B_47,C_48,D_49] : k2_xboole_0(k1_tarski(A_46),k1_enumset1(B_47,C_48,D_49)) = k2_enumset1(A_46,B_47,C_48,D_49) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [A_46,A_36,B_37] : k2_xboole_0(k1_tarski(A_46),k2_tarski(A_36,B_37)) = k2_enumset1(A_46,A_36,A_36,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_60])).

tff(c_72,plain,(
    ! [A_46,A_36,B_37] : k2_enumset1(A_46,A_36,A_36,B_37) = k1_enumset1(A_46,A_36,B_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_69])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8,D_9] : k2_xboole_0(k1_tarski(A_6),k1_enumset1(B_7,C_8,D_9)) = k2_enumset1(A_6,B_7,C_8,D_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_160,plain,(
    ! [A_59,A_60,B_61] : k2_enumset1(A_59,A_60,A_60,B_61) = k1_enumset1(A_59,A_60,B_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_69])).

tff(c_8,plain,(
    ! [B_11,A_10,C_12,E_14,D_13] : k2_xboole_0(k1_tarski(A_10),k2_enumset1(B_11,C_12,D_13,E_14)) = k3_enumset1(A_10,B_11,C_12,D_13,E_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_166,plain,(
    ! [A_10,A_59,A_60,B_61] : k3_enumset1(A_10,A_59,A_60,A_60,B_61) = k2_xboole_0(k1_tarski(A_10),k1_enumset1(A_59,A_60,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_8])).

tff(c_277,plain,(
    ! [A_74,A_75,A_76,B_77] : k3_enumset1(A_74,A_75,A_76,A_76,B_77) = k2_enumset1(A_74,A_75,A_76,B_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_166])).

tff(c_16,plain,(
    ! [A_35] : k2_tarski(A_35,A_35) = k1_tarski(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_245,plain,(
    ! [D_66,B_67,C_65,E_68,A_69] : k2_xboole_0(k2_tarski(A_69,B_67),k1_enumset1(C_65,D_66,E_68)) = k3_enumset1(A_69,B_67,C_65,D_66,E_68) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_263,plain,(
    ! [A_35,C_65,D_66,E_68] : k3_enumset1(A_35,A_35,C_65,D_66,E_68) = k2_xboole_0(k1_tarski(A_35),k1_enumset1(C_65,D_66,E_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_245])).

tff(c_266,plain,(
    ! [A_35,C_65,D_66,E_68] : k3_enumset1(A_35,A_35,C_65,D_66,E_68) = k2_enumset1(A_35,C_65,D_66,E_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_263])).

tff(c_284,plain,(
    ! [A_75,A_76,B_77] : k2_enumset1(A_75,A_76,A_76,B_77) = k2_enumset1(A_75,A_75,A_76,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_266])).

tff(c_293,plain,(
    ! [A_75,A_76,B_77] : k2_enumset1(A_75,A_75,A_76,B_77) = k1_enumset1(A_75,A_76,B_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_284])).

tff(c_20,plain,(
    k2_enumset1('#skF_1','#skF_1','#skF_2','#skF_3') != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_326,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.26  
% 2.11/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.26  %$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.11/1.26  
% 2.11/1.26  %Foreground sorts:
% 2.11/1.26  
% 2.11/1.26  
% 2.11/1.26  %Background operators:
% 2.11/1.26  
% 2.11/1.26  
% 2.11/1.26  %Foreground operators:
% 2.11/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.11/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.11/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.26  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.26  
% 2.11/1.27  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.11/1.27  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.11/1.27  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.11/1.27  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 2.11/1.27  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.11/1.27  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 2.11/1.27  tff(f_46, negated_conjecture, ~(![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.11/1.27  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k1_tarski(A_3), k2_tarski(B_4, C_5))=k1_enumset1(A_3, B_4, C_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.27  tff(c_18, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.27  tff(c_60, plain, (![A_46, B_47, C_48, D_49]: (k2_xboole_0(k1_tarski(A_46), k1_enumset1(B_47, C_48, D_49))=k2_enumset1(A_46, B_47, C_48, D_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.11/1.27  tff(c_69, plain, (![A_46, A_36, B_37]: (k2_xboole_0(k1_tarski(A_46), k2_tarski(A_36, B_37))=k2_enumset1(A_46, A_36, A_36, B_37))), inference(superposition, [status(thm), theory('equality')], [c_18, c_60])).
% 2.11/1.27  tff(c_72, plain, (![A_46, A_36, B_37]: (k2_enumset1(A_46, A_36, A_36, B_37)=k1_enumset1(A_46, A_36, B_37))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_69])).
% 2.11/1.27  tff(c_6, plain, (![A_6, B_7, C_8, D_9]: (k2_xboole_0(k1_tarski(A_6), k1_enumset1(B_7, C_8, D_9))=k2_enumset1(A_6, B_7, C_8, D_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.11/1.27  tff(c_160, plain, (![A_59, A_60, B_61]: (k2_enumset1(A_59, A_60, A_60, B_61)=k1_enumset1(A_59, A_60, B_61))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_69])).
% 2.11/1.27  tff(c_8, plain, (![B_11, A_10, C_12, E_14, D_13]: (k2_xboole_0(k1_tarski(A_10), k2_enumset1(B_11, C_12, D_13, E_14))=k3_enumset1(A_10, B_11, C_12, D_13, E_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.27  tff(c_166, plain, (![A_10, A_59, A_60, B_61]: (k3_enumset1(A_10, A_59, A_60, A_60, B_61)=k2_xboole_0(k1_tarski(A_10), k1_enumset1(A_59, A_60, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_160, c_8])).
% 2.11/1.27  tff(c_277, plain, (![A_74, A_75, A_76, B_77]: (k3_enumset1(A_74, A_75, A_76, A_76, B_77)=k2_enumset1(A_74, A_75, A_76, B_77))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_166])).
% 2.11/1.27  tff(c_16, plain, (![A_35]: (k2_tarski(A_35, A_35)=k1_tarski(A_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.11/1.27  tff(c_245, plain, (![D_66, B_67, C_65, E_68, A_69]: (k2_xboole_0(k2_tarski(A_69, B_67), k1_enumset1(C_65, D_66, E_68))=k3_enumset1(A_69, B_67, C_65, D_66, E_68))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.11/1.27  tff(c_263, plain, (![A_35, C_65, D_66, E_68]: (k3_enumset1(A_35, A_35, C_65, D_66, E_68)=k2_xboole_0(k1_tarski(A_35), k1_enumset1(C_65, D_66, E_68)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_245])).
% 2.11/1.27  tff(c_266, plain, (![A_35, C_65, D_66, E_68]: (k3_enumset1(A_35, A_35, C_65, D_66, E_68)=k2_enumset1(A_35, C_65, D_66, E_68))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_263])).
% 2.11/1.27  tff(c_284, plain, (![A_75, A_76, B_77]: (k2_enumset1(A_75, A_76, A_76, B_77)=k2_enumset1(A_75, A_75, A_76, B_77))), inference(superposition, [status(thm), theory('equality')], [c_277, c_266])).
% 2.11/1.27  tff(c_293, plain, (![A_75, A_76, B_77]: (k2_enumset1(A_75, A_75, A_76, B_77)=k1_enumset1(A_75, A_76, B_77))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_284])).
% 2.11/1.27  tff(c_20, plain, (k2_enumset1('#skF_1', '#skF_1', '#skF_2', '#skF_3')!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.11/1.27  tff(c_326, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_293, c_20])).
% 2.11/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.27  
% 2.11/1.27  Inference rules
% 2.11/1.27  ----------------------
% 2.11/1.27  #Ref     : 0
% 2.11/1.27  #Sup     : 73
% 2.11/1.27  #Fact    : 0
% 2.11/1.27  #Define  : 0
% 2.11/1.27  #Split   : 0
% 2.11/1.27  #Chain   : 0
% 2.11/1.27  #Close   : 0
% 2.11/1.27  
% 2.11/1.27  Ordering : KBO
% 2.11/1.27  
% 2.11/1.27  Simplification rules
% 2.11/1.27  ----------------------
% 2.11/1.27  #Subsume      : 2
% 2.11/1.27  #Demod        : 26
% 2.11/1.27  #Tautology    : 49
% 2.11/1.27  #SimpNegUnit  : 0
% 2.11/1.27  #BackRed      : 1
% 2.11/1.27  
% 2.11/1.27  #Partial instantiations: 0
% 2.11/1.27  #Strategies tried      : 1
% 2.11/1.27  
% 2.11/1.27  Timing (in seconds)
% 2.11/1.27  ----------------------
% 2.11/1.27  Preprocessing        : 0.30
% 2.11/1.27  Parsing              : 0.16
% 2.11/1.27  CNF conversion       : 0.02
% 2.11/1.27  Main loop            : 0.19
% 2.11/1.27  Inferencing          : 0.08
% 2.11/1.27  Reduction            : 0.07
% 2.11/1.27  Demodulation         : 0.05
% 2.11/1.27  BG Simplification    : 0.02
% 2.11/1.27  Subsumption          : 0.02
% 2.11/1.27  Abstraction          : 0.02
% 2.11/1.27  MUC search           : 0.00
% 2.11/1.27  Cooper               : 0.00
% 2.11/1.27  Total                : 0.52
% 2.11/1.27  Index Insertion      : 0.00
% 2.11/1.27  Index Deletion       : 0.00
% 2.11/1.27  Index Matching       : 0.00
% 2.11/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
