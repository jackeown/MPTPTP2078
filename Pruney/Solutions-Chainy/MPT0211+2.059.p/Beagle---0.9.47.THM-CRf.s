%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:22 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   53 (  64 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  50 expanded)
%              Number of equality atoms :   38 (  49 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_24,plain,(
    ! [A_37,C_39,B_38] : k1_enumset1(A_37,C_39,B_38) = k1_enumset1(A_37,B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [B_13,C_14,A_12] : k1_enumset1(B_13,C_14,A_12) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [C_17,B_16,A_15] : k1_enumset1(C_17,B_16,A_15) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_30,B_31,C_32] : k2_enumset1(A_30,A_30,B_31,C_32) = k1_enumset1(A_30,B_31,C_32) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] : k2_xboole_0(k2_tarski(A_3,B_4),k2_tarski(C_5,D_6)) = k2_enumset1(A_3,B_4,C_5,D_6) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_28,B_29] : k1_enumset1(A_28,A_28,B_29) = k2_tarski(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_697,plain,(
    ! [D_92,E_91,A_89,C_90,B_93] : k2_xboole_0(k2_tarski(A_89,B_93),k1_enumset1(C_90,D_92,E_91)) = k3_enumset1(A_89,B_93,C_90,D_92,E_91) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_736,plain,(
    ! [A_89,B_93,A_28,B_29] : k3_enumset1(A_89,B_93,A_28,A_28,B_29) = k2_xboole_0(k2_tarski(A_89,B_93),k2_tarski(A_28,B_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_697])).

tff(c_910,plain,(
    ! [A_109,B_110,A_111,B_112] : k3_enumset1(A_109,B_110,A_111,A_111,B_112) = k2_enumset1(A_109,B_110,A_111,B_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_736])).

tff(c_22,plain,(
    ! [A_33,B_34,C_35,D_36] : k3_enumset1(A_33,A_33,B_34,C_35,D_36) = k2_enumset1(A_33,B_34,C_35,D_36) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_921,plain,(
    ! [B_110,A_111,B_112] : k2_enumset1(B_110,B_110,A_111,B_112) = k2_enumset1(B_110,A_111,A_111,B_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_910,c_22])).

tff(c_935,plain,(
    ! [B_110,A_111,B_112] : k2_enumset1(B_110,A_111,A_111,B_112) = k1_enumset1(B_110,A_111,B_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_921])).

tff(c_132,plain,(
    ! [C_48,B_49,A_50] : k1_enumset1(C_48,B_49,A_50) = k1_enumset1(A_50,B_49,C_48) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_160,plain,(
    ! [C_48,B_49] : k1_enumset1(C_48,B_49,B_49) = k2_tarski(B_49,C_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_18])).

tff(c_718,plain,(
    ! [A_89,B_93,C_48,B_49] : k3_enumset1(A_89,B_93,C_48,B_49,B_49) = k2_xboole_0(k2_tarski(A_89,B_93),k2_tarski(B_49,C_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_697])).

tff(c_970,plain,(
    ! [A_116,B_117,C_118,B_119] : k3_enumset1(A_116,B_117,C_118,B_119,B_119) = k2_enumset1(A_116,B_117,B_119,C_118) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_718])).

tff(c_12,plain,(
    ! [A_18,B_19,C_20,D_21] : k2_xboole_0(k1_enumset1(A_18,B_19,C_20),k1_tarski(D_21)) = k2_enumset1(A_18,B_19,C_20,D_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_613,plain,(
    ! [B_77,C_78,E_80,A_79,D_76] : k2_xboole_0(k1_enumset1(A_79,B_77,C_78),k2_tarski(D_76,E_80)) = k3_enumset1(A_79,B_77,C_78,D_76,E_80) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_655,plain,(
    ! [A_79,B_77,C_78,A_27] : k3_enumset1(A_79,B_77,C_78,A_27,A_27) = k2_xboole_0(k1_enumset1(A_79,B_77,C_78),k1_tarski(A_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_613])).

tff(c_661,plain,(
    ! [A_79,B_77,C_78,A_27] : k3_enumset1(A_79,B_77,C_78,A_27,A_27) = k2_enumset1(A_79,B_77,C_78,A_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_655])).

tff(c_980,plain,(
    ! [A_116,B_117,C_118,B_119] : k2_enumset1(A_116,B_117,C_118,B_119) = k2_enumset1(A_116,B_117,B_119,C_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_970,c_661])).

tff(c_26,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_27,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_28,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_27])).

tff(c_1005,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_980,c_28])).

tff(c_1008,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_8,c_10,c_935,c_1005])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:43:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.38  
% 2.84/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.38  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.84/1.38  
% 2.84/1.38  %Foreground sorts:
% 2.84/1.38  
% 2.84/1.38  
% 2.84/1.38  %Background operators:
% 2.84/1.38  
% 2.84/1.38  
% 2.84/1.38  %Foreground operators:
% 2.84/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.84/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.84/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.84/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.84/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.84/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.84/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.84/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.84/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.84/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.84/1.38  
% 2.84/1.39  tff(f_49, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_enumset1)).
% 2.84/1.39  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_enumset1)).
% 2.84/1.39  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_enumset1)).
% 2.84/1.39  tff(f_45, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.84/1.39  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 2.84/1.39  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.84/1.39  tff(f_39, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 2.84/1.39  tff(f_47, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.84/1.39  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 2.84/1.39  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.84/1.39  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 2.84/1.39  tff(f_52, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 2.84/1.39  tff(c_24, plain, (![A_37, C_39, B_38]: (k1_enumset1(A_37, C_39, B_38)=k1_enumset1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.84/1.39  tff(c_8, plain, (![B_13, C_14, A_12]: (k1_enumset1(B_13, C_14, A_12)=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.84/1.39  tff(c_10, plain, (![C_17, B_16, A_15]: (k1_enumset1(C_17, B_16, A_15)=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.39  tff(c_20, plain, (![A_30, B_31, C_32]: (k2_enumset1(A_30, A_30, B_31, C_32)=k1_enumset1(A_30, B_31, C_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.84/1.39  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (k2_xboole_0(k2_tarski(A_3, B_4), k2_tarski(C_5, D_6))=k2_enumset1(A_3, B_4, C_5, D_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.84/1.39  tff(c_18, plain, (![A_28, B_29]: (k1_enumset1(A_28, A_28, B_29)=k2_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.84/1.39  tff(c_697, plain, (![D_92, E_91, A_89, C_90, B_93]: (k2_xboole_0(k2_tarski(A_89, B_93), k1_enumset1(C_90, D_92, E_91))=k3_enumset1(A_89, B_93, C_90, D_92, E_91))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.84/1.39  tff(c_736, plain, (![A_89, B_93, A_28, B_29]: (k3_enumset1(A_89, B_93, A_28, A_28, B_29)=k2_xboole_0(k2_tarski(A_89, B_93), k2_tarski(A_28, B_29)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_697])).
% 2.84/1.39  tff(c_910, plain, (![A_109, B_110, A_111, B_112]: (k3_enumset1(A_109, B_110, A_111, A_111, B_112)=k2_enumset1(A_109, B_110, A_111, B_112))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_736])).
% 2.84/1.39  tff(c_22, plain, (![A_33, B_34, C_35, D_36]: (k3_enumset1(A_33, A_33, B_34, C_35, D_36)=k2_enumset1(A_33, B_34, C_35, D_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.84/1.39  tff(c_921, plain, (![B_110, A_111, B_112]: (k2_enumset1(B_110, B_110, A_111, B_112)=k2_enumset1(B_110, A_111, A_111, B_112))), inference(superposition, [status(thm), theory('equality')], [c_910, c_22])).
% 2.84/1.39  tff(c_935, plain, (![B_110, A_111, B_112]: (k2_enumset1(B_110, A_111, A_111, B_112)=k1_enumset1(B_110, A_111, B_112))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_921])).
% 2.84/1.39  tff(c_132, plain, (![C_48, B_49, A_50]: (k1_enumset1(C_48, B_49, A_50)=k1_enumset1(A_50, B_49, C_48))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.39  tff(c_160, plain, (![C_48, B_49]: (k1_enumset1(C_48, B_49, B_49)=k2_tarski(B_49, C_48))), inference(superposition, [status(thm), theory('equality')], [c_132, c_18])).
% 2.84/1.39  tff(c_718, plain, (![A_89, B_93, C_48, B_49]: (k3_enumset1(A_89, B_93, C_48, B_49, B_49)=k2_xboole_0(k2_tarski(A_89, B_93), k2_tarski(B_49, C_48)))), inference(superposition, [status(thm), theory('equality')], [c_160, c_697])).
% 2.84/1.39  tff(c_970, plain, (![A_116, B_117, C_118, B_119]: (k3_enumset1(A_116, B_117, C_118, B_119, B_119)=k2_enumset1(A_116, B_117, B_119, C_118))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_718])).
% 2.84/1.39  tff(c_12, plain, (![A_18, B_19, C_20, D_21]: (k2_xboole_0(k1_enumset1(A_18, B_19, C_20), k1_tarski(D_21))=k2_enumset1(A_18, B_19, C_20, D_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.84/1.39  tff(c_16, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.84/1.39  tff(c_613, plain, (![B_77, C_78, E_80, A_79, D_76]: (k2_xboole_0(k1_enumset1(A_79, B_77, C_78), k2_tarski(D_76, E_80))=k3_enumset1(A_79, B_77, C_78, D_76, E_80))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.39  tff(c_655, plain, (![A_79, B_77, C_78, A_27]: (k3_enumset1(A_79, B_77, C_78, A_27, A_27)=k2_xboole_0(k1_enumset1(A_79, B_77, C_78), k1_tarski(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_613])).
% 2.84/1.39  tff(c_661, plain, (![A_79, B_77, C_78, A_27]: (k3_enumset1(A_79, B_77, C_78, A_27, A_27)=k2_enumset1(A_79, B_77, C_78, A_27))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_655])).
% 2.84/1.39  tff(c_980, plain, (![A_116, B_117, C_118, B_119]: (k2_enumset1(A_116, B_117, C_118, B_119)=k2_enumset1(A_116, B_117, B_119, C_118))), inference(superposition, [status(thm), theory('equality')], [c_970, c_661])).
% 2.84/1.39  tff(c_26, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.84/1.39  tff(c_27, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 2.84/1.39  tff(c_28, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_27])).
% 2.84/1.39  tff(c_1005, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_980, c_28])).
% 2.84/1.39  tff(c_1008, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_8, c_10, c_935, c_1005])).
% 2.84/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.39  
% 2.84/1.39  Inference rules
% 2.84/1.39  ----------------------
% 2.84/1.39  #Ref     : 0
% 2.84/1.39  #Sup     : 251
% 2.84/1.39  #Fact    : 0
% 2.84/1.39  #Define  : 0
% 2.84/1.39  #Split   : 0
% 2.84/1.39  #Chain   : 0
% 2.84/1.39  #Close   : 0
% 2.84/1.39  
% 2.84/1.39  Ordering : KBO
% 2.84/1.39  
% 2.84/1.39  Simplification rules
% 2.84/1.39  ----------------------
% 2.84/1.39  #Subsume      : 61
% 2.84/1.39  #Demod        : 111
% 2.84/1.39  #Tautology    : 137
% 2.84/1.39  #SimpNegUnit  : 0
% 2.84/1.39  #BackRed      : 1
% 2.84/1.39  
% 2.84/1.39  #Partial instantiations: 0
% 2.84/1.39  #Strategies tried      : 1
% 2.84/1.39  
% 2.84/1.39  Timing (in seconds)
% 2.84/1.39  ----------------------
% 2.84/1.39  Preprocessing        : 0.28
% 2.84/1.39  Parsing              : 0.15
% 2.84/1.39  CNF conversion       : 0.02
% 2.84/1.39  Main loop            : 0.36
% 2.84/1.39  Inferencing          : 0.12
% 2.84/1.39  Reduction            : 0.15
% 2.84/1.39  Demodulation         : 0.13
% 2.84/1.39  BG Simplification    : 0.02
% 2.84/1.39  Subsumption          : 0.05
% 2.84/1.39  Abstraction          : 0.02
% 2.84/1.39  MUC search           : 0.00
% 2.84/1.39  Cooper               : 0.00
% 2.84/1.39  Total                : 0.67
% 2.84/1.39  Index Insertion      : 0.00
% 2.84/1.39  Index Deletion       : 0.00
% 2.84/1.39  Index Matching       : 0.00
% 2.84/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
