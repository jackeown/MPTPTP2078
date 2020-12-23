%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:23 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 147 expanded)
%              Number of leaves         :   19 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :   35 ( 136 expanded)
%              Number of equality atoms :   34 ( 135 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_6,plain,(
    ! [B_9,C_10,A_8] : k1_enumset1(B_9,C_10,A_8) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_14,B_15,C_16] : k2_xboole_0(k2_tarski(A_14,B_15),k1_tarski(C_16)) = k1_enumset1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_575,plain,(
    ! [A_56,B_57,C_58,D_59] : k2_xboole_0(k2_tarski(A_56,B_57),k2_tarski(C_58,D_59)) = k2_enumset1(A_56,B_57,C_58,D_59) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_590,plain,(
    ! [A_56,B_57,A_17] : k2_xboole_0(k2_tarski(A_56,B_57),k1_tarski(A_17)) = k2_enumset1(A_56,B_57,A_17,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_575])).

tff(c_594,plain,(
    ! [A_56,B_57,A_17] : k2_enumset1(A_56,B_57,A_17,A_17) = k1_enumset1(A_56,B_57,A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_590])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] : k2_xboole_0(k2_tarski(A_4,B_5),k2_tarski(C_6,D_7)) = k2_enumset1(A_4,B_5,C_6,D_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_547,plain,(
    ! [A_51,B_52,C_53] : k2_xboole_0(k2_tarski(A_51,B_52),k1_tarski(C_53)) = k1_enumset1(A_51,B_52,C_53) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_559,plain,(
    ! [A_17,C_53] : k2_xboole_0(k1_tarski(A_17),k1_tarski(C_53)) = k1_enumset1(A_17,A_17,C_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_547])).

tff(c_562,plain,(
    ! [A_17,C_53] : k2_xboole_0(k1_tarski(A_17),k1_tarski(C_53)) = k2_tarski(A_17,C_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_559])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_744,plain,(
    ! [A_74,B_75,C_76,C_77] : k2_xboole_0(k2_tarski(A_74,B_75),k2_xboole_0(k1_tarski(C_76),C_77)) = k2_xboole_0(k1_enumset1(A_74,B_75,C_76),C_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_547,c_2])).

tff(c_768,plain,(
    ! [A_74,B_75,A_17,C_53] : k2_xboole_0(k1_enumset1(A_74,B_75,A_17),k1_tarski(C_53)) = k2_xboole_0(k2_tarski(A_74,B_75),k2_tarski(A_17,C_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_744])).

tff(c_817,plain,(
    ! [A_81,B_82,A_83,C_84] : k2_xboole_0(k1_enumset1(A_81,B_82,A_83),k1_tarski(C_84)) = k2_enumset1(A_81,B_82,A_83,C_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_768])).

tff(c_933,plain,(
    ! [B_91,C_92,A_93,C_94] : k2_xboole_0(k1_enumset1(B_91,C_92,A_93),k1_tarski(C_94)) = k2_enumset1(A_93,B_91,C_92,C_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_817])).

tff(c_775,plain,(
    ! [A_74,B_75,A_17,C_53] : k2_xboole_0(k1_enumset1(A_74,B_75,A_17),k1_tarski(C_53)) = k2_enumset1(A_74,B_75,A_17,C_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_768])).

tff(c_989,plain,(
    ! [B_95,C_96,A_97,C_98] : k2_enumset1(B_95,C_96,A_97,C_98) = k2_enumset1(A_97,B_95,C_96,C_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_933,c_775])).

tff(c_1060,plain,(
    ! [A_17,A_56,B_57] : k2_enumset1(A_17,A_56,B_57,A_17) = k1_enumset1(A_56,B_57,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_989])).

tff(c_939,plain,(
    ! [B_91,C_92,A_93,C_94] : k2_enumset1(B_91,C_92,A_93,C_94) = k2_enumset1(A_93,B_91,C_92,C_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_933,c_775])).

tff(c_18,plain,(
    ! [A_23,C_25,B_24] : k1_enumset1(A_23,C_25,B_24) = k1_enumset1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_21,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_22,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_21])).

tff(c_988,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_1') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_939,c_22])).

tff(c_1202,plain,(
    k1_enumset1('#skF_3','#skF_2','#skF_1') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1060,c_988])).

tff(c_1205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.45  
% 2.86/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.46  %$ k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.86/1.46  
% 2.86/1.46  %Foreground sorts:
% 2.86/1.46  
% 2.86/1.46  
% 2.86/1.46  %Background operators:
% 2.86/1.46  
% 2.86/1.46  
% 2.86/1.46  %Foreground operators:
% 2.86/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.86/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.86/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.86/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.86/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.86/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.86/1.46  
% 3.19/1.47  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_enumset1)).
% 3.19/1.47  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 3.19/1.47  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.19/1.47  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 3.19/1.47  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.19/1.47  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.19/1.47  tff(f_43, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_enumset1)).
% 3.19/1.47  tff(f_46, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 3.19/1.47  tff(c_6, plain, (![B_9, C_10, A_8]: (k1_enumset1(B_9, C_10, A_8)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.19/1.47  tff(c_10, plain, (![A_14, B_15, C_16]: (k2_xboole_0(k2_tarski(A_14, B_15), k1_tarski(C_16))=k1_enumset1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.19/1.47  tff(c_12, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.19/1.47  tff(c_575, plain, (![A_56, B_57, C_58, D_59]: (k2_xboole_0(k2_tarski(A_56, B_57), k2_tarski(C_58, D_59))=k2_enumset1(A_56, B_57, C_58, D_59))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.19/1.47  tff(c_590, plain, (![A_56, B_57, A_17]: (k2_xboole_0(k2_tarski(A_56, B_57), k1_tarski(A_17))=k2_enumset1(A_56, B_57, A_17, A_17))), inference(superposition, [status(thm), theory('equality')], [c_12, c_575])).
% 3.19/1.47  tff(c_594, plain, (![A_56, B_57, A_17]: (k2_enumset1(A_56, B_57, A_17, A_17)=k1_enumset1(A_56, B_57, A_17))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_590])).
% 3.19/1.47  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k2_xboole_0(k2_tarski(A_4, B_5), k2_tarski(C_6, D_7))=k2_enumset1(A_4, B_5, C_6, D_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.19/1.47  tff(c_14, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.19/1.47  tff(c_547, plain, (![A_51, B_52, C_53]: (k2_xboole_0(k2_tarski(A_51, B_52), k1_tarski(C_53))=k1_enumset1(A_51, B_52, C_53))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.19/1.47  tff(c_559, plain, (![A_17, C_53]: (k2_xboole_0(k1_tarski(A_17), k1_tarski(C_53))=k1_enumset1(A_17, A_17, C_53))), inference(superposition, [status(thm), theory('equality')], [c_12, c_547])).
% 3.19/1.47  tff(c_562, plain, (![A_17, C_53]: (k2_xboole_0(k1_tarski(A_17), k1_tarski(C_53))=k2_tarski(A_17, C_53))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_559])).
% 3.19/1.47  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.19/1.47  tff(c_744, plain, (![A_74, B_75, C_76, C_77]: (k2_xboole_0(k2_tarski(A_74, B_75), k2_xboole_0(k1_tarski(C_76), C_77))=k2_xboole_0(k1_enumset1(A_74, B_75, C_76), C_77))), inference(superposition, [status(thm), theory('equality')], [c_547, c_2])).
% 3.19/1.47  tff(c_768, plain, (![A_74, B_75, A_17, C_53]: (k2_xboole_0(k1_enumset1(A_74, B_75, A_17), k1_tarski(C_53))=k2_xboole_0(k2_tarski(A_74, B_75), k2_tarski(A_17, C_53)))), inference(superposition, [status(thm), theory('equality')], [c_562, c_744])).
% 3.19/1.47  tff(c_817, plain, (![A_81, B_82, A_83, C_84]: (k2_xboole_0(k1_enumset1(A_81, B_82, A_83), k1_tarski(C_84))=k2_enumset1(A_81, B_82, A_83, C_84))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_768])).
% 3.19/1.47  tff(c_933, plain, (![B_91, C_92, A_93, C_94]: (k2_xboole_0(k1_enumset1(B_91, C_92, A_93), k1_tarski(C_94))=k2_enumset1(A_93, B_91, C_92, C_94))), inference(superposition, [status(thm), theory('equality')], [c_6, c_817])).
% 3.19/1.47  tff(c_775, plain, (![A_74, B_75, A_17, C_53]: (k2_xboole_0(k1_enumset1(A_74, B_75, A_17), k1_tarski(C_53))=k2_enumset1(A_74, B_75, A_17, C_53))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_768])).
% 3.19/1.47  tff(c_989, plain, (![B_95, C_96, A_97, C_98]: (k2_enumset1(B_95, C_96, A_97, C_98)=k2_enumset1(A_97, B_95, C_96, C_98))), inference(superposition, [status(thm), theory('equality')], [c_933, c_775])).
% 3.19/1.47  tff(c_1060, plain, (![A_17, A_56, B_57]: (k2_enumset1(A_17, A_56, B_57, A_17)=k1_enumset1(A_56, B_57, A_17))), inference(superposition, [status(thm), theory('equality')], [c_594, c_989])).
% 3.19/1.47  tff(c_939, plain, (![B_91, C_92, A_93, C_94]: (k2_enumset1(B_91, C_92, A_93, C_94)=k2_enumset1(A_93, B_91, C_92, C_94))), inference(superposition, [status(thm), theory('equality')], [c_933, c_775])).
% 3.19/1.47  tff(c_18, plain, (![A_23, C_25, B_24]: (k1_enumset1(A_23, C_25, B_24)=k1_enumset1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.19/1.47  tff(c_20, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.19/1.47  tff(c_21, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20])).
% 3.19/1.47  tff(c_22, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_21])).
% 3.19/1.47  tff(c_988, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_1')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_939, c_939, c_22])).
% 3.19/1.47  tff(c_1202, plain, (k1_enumset1('#skF_3', '#skF_2', '#skF_1')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1060, c_988])).
% 3.19/1.47  tff(c_1205, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1202])).
% 3.19/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.19/1.47  
% 3.19/1.47  Inference rules
% 3.19/1.47  ----------------------
% 3.19/1.47  #Ref     : 0
% 3.19/1.47  #Sup     : 303
% 3.19/1.47  #Fact    : 0
% 3.19/1.47  #Define  : 0
% 3.19/1.47  #Split   : 0
% 3.19/1.47  #Chain   : 0
% 3.19/1.47  #Close   : 0
% 3.19/1.47  
% 3.19/1.47  Ordering : KBO
% 3.19/1.47  
% 3.19/1.47  Simplification rules
% 3.19/1.47  ----------------------
% 3.19/1.47  #Subsume      : 64
% 3.19/1.47  #Demod        : 157
% 3.19/1.47  #Tautology    : 172
% 3.19/1.47  #SimpNegUnit  : 0
% 3.19/1.47  #BackRed      : 2
% 3.19/1.47  
% 3.19/1.47  #Partial instantiations: 0
% 3.19/1.47  #Strategies tried      : 1
% 3.19/1.47  
% 3.19/1.47  Timing (in seconds)
% 3.19/1.47  ----------------------
% 3.19/1.47  Preprocessing        : 0.28
% 3.19/1.47  Parsing              : 0.14
% 3.19/1.47  CNF conversion       : 0.01
% 3.19/1.47  Main loop            : 0.41
% 3.19/1.47  Inferencing          : 0.15
% 3.19/1.47  Reduction            : 0.17
% 3.19/1.47  Demodulation         : 0.15
% 3.19/1.47  BG Simplification    : 0.02
% 3.19/1.47  Subsumption          : 0.05
% 3.19/1.47  Abstraction          : 0.03
% 3.19/1.47  MUC search           : 0.00
% 3.19/1.47  Cooper               : 0.00
% 3.19/1.47  Total                : 0.71
% 3.19/1.47  Index Insertion      : 0.00
% 3.19/1.47  Index Deletion       : 0.00
% 3.19/1.47  Index Matching       : 0.00
% 3.19/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
