%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:39 EST 2020

% Result     : Theorem 8.29s
% Output     : CNFRefutation 8.29s
% Verified   : 
% Statistics : Number of formulae       :   47 (  86 expanded)
%              Number of leaves         :   22 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   32 (  71 expanded)
%              Number of equality atoms :   31 (  70 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(c_12,plain,(
    ! [A_12,B_13,C_14,D_15] : k2_xboole_0(k2_tarski(A_12,B_13),k2_tarski(C_14,D_15)) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_58,plain,(
    ! [A_30,B_31] : k2_xboole_0(k1_tarski(A_30),k1_tarski(B_31)) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_163,plain,(
    ! [B_41,A_42] : k2_xboole_0(k1_tarski(B_41),k1_tarski(A_42)) = k2_tarski(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_58])).

tff(c_14,plain,(
    ! [A_16,B_17] : k2_xboole_0(k1_tarski(A_16),k1_tarski(B_17)) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_172,plain,(
    ! [B_41,A_42] : k2_tarski(B_41,A_42) = k2_tarski(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_14])).

tff(c_453,plain,(
    ! [A_61,B_62,C_63,D_64] : k2_xboole_0(k2_tarski(A_61,B_62),k2_tarski(C_63,D_64)) = k2_enumset1(A_61,B_62,C_63,D_64) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6448,plain,(
    ! [A_218,B_219,A_220,B_221] : k2_xboole_0(k2_tarski(A_218,B_219),k2_tarski(A_220,B_221)) = k2_enumset1(A_218,B_219,B_221,A_220) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_453])).

tff(c_6558,plain,(
    ! [A_12,B_13,D_15,C_14] : k2_enumset1(A_12,B_13,D_15,C_14) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_6448])).

tff(c_20,plain,(
    ! [A_24,B_25,C_26,D_27] : k2_xboole_0(k1_tarski(A_24),k1_enumset1(B_25,C_26,D_27)) = k2_enumset1(A_24,B_25,C_26,D_27) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_358,plain,(
    ! [A_54,B_55,C_56] : k2_xboole_0(k2_tarski(A_54,B_55),k1_tarski(C_56)) = k1_enumset1(A_54,B_55,C_56) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_561,plain,(
    ! [C_75,A_76,B_77] : k2_xboole_0(k1_tarski(C_75),k2_tarski(A_76,B_77)) = k1_enumset1(A_76,B_77,C_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_358])).

tff(c_16,plain,(
    ! [A_18,B_19,C_20] : k2_xboole_0(k1_tarski(A_18),k2_tarski(B_19,C_20)) = k1_enumset1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_697,plain,(
    ! [C_83,A_84,B_85] : k1_enumset1(C_83,A_84,B_85) = k1_enumset1(A_84,B_85,C_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_16])).

tff(c_11978,plain,(
    ! [A_282,A_283,B_284,C_285] : k2_xboole_0(k1_tarski(A_282),k1_enumset1(A_283,B_284,C_285)) = k2_enumset1(A_282,C_285,A_283,B_284) ),
    inference(superposition,[status(thm),theory(equality)],[c_697,c_20])).

tff(c_12076,plain,(
    ! [A_24,D_27,B_25,C_26] : k2_enumset1(A_24,D_27,B_25,C_26) = k2_enumset1(A_24,B_25,C_26,D_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_11978])).

tff(c_486,plain,(
    ! [C_63,D_64,A_61,B_62] : k2_xboole_0(k2_tarski(C_63,D_64),k2_tarski(A_61,B_62)) = k2_enumset1(A_61,B_62,C_63,D_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_453])).

tff(c_6486,plain,(
    ! [A_220,B_221,A_218,B_219] : k2_enumset1(A_220,B_221,A_218,B_219) = k2_enumset1(A_218,B_219,B_221,A_220) ),
    inference(superposition,[status(thm),theory(equality)],[c_6448,c_486])).

tff(c_22,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k1_tarski('#skF_4')) != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_23,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_enumset1('#skF_1','#skF_2','#skF_3')) != k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_24,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_23])).

tff(c_6607,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6486,c_24])).

tff(c_9719,plain,(
    k2_enumset1('#skF_4','#skF_3','#skF_1','#skF_2') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6558,c_6607])).

tff(c_12121,plain,(
    k2_enumset1('#skF_4','#skF_1','#skF_2','#skF_3') != k2_enumset1('#skF_4','#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12076,c_9719])).

tff(c_12124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6558,c_12121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.29/2.86  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.29/2.86  
% 8.29/2.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.29/2.87  %$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.29/2.87  
% 8.29/2.87  %Foreground sorts:
% 8.29/2.87  
% 8.29/2.87  
% 8.29/2.87  %Background operators:
% 8.29/2.87  
% 8.29/2.87  
% 8.29/2.87  %Foreground operators:
% 8.29/2.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.29/2.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.29/2.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.29/2.87  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.29/2.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.29/2.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.29/2.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.29/2.87  tff('#skF_2', type, '#skF_2': $i).
% 8.29/2.87  tff('#skF_3', type, '#skF_3': $i).
% 8.29/2.87  tff('#skF_1', type, '#skF_1': $i).
% 8.29/2.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.29/2.87  tff('#skF_4', type, '#skF_4': $i).
% 8.29/2.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.29/2.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.29/2.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.29/2.87  
% 8.29/2.88  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 8.29/2.88  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.29/2.88  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 8.29/2.88  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 8.29/2.88  tff(f_43, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 8.29/2.88  tff(f_41, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 8.29/2.88  tff(f_48, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 8.29/2.88  tff(c_12, plain, (![A_12, B_13, C_14, D_15]: (k2_xboole_0(k2_tarski(A_12, B_13), k2_tarski(C_14, D_15))=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.29/2.88  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.29/2.88  tff(c_58, plain, (![A_30, B_31]: (k2_xboole_0(k1_tarski(A_30), k1_tarski(B_31))=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.29/2.88  tff(c_163, plain, (![B_41, A_42]: (k2_xboole_0(k1_tarski(B_41), k1_tarski(A_42))=k2_tarski(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_2, c_58])).
% 8.29/2.88  tff(c_14, plain, (![A_16, B_17]: (k2_xboole_0(k1_tarski(A_16), k1_tarski(B_17))=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.29/2.88  tff(c_172, plain, (![B_41, A_42]: (k2_tarski(B_41, A_42)=k2_tarski(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_163, c_14])).
% 8.29/2.88  tff(c_453, plain, (![A_61, B_62, C_63, D_64]: (k2_xboole_0(k2_tarski(A_61, B_62), k2_tarski(C_63, D_64))=k2_enumset1(A_61, B_62, C_63, D_64))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.29/2.88  tff(c_6448, plain, (![A_218, B_219, A_220, B_221]: (k2_xboole_0(k2_tarski(A_218, B_219), k2_tarski(A_220, B_221))=k2_enumset1(A_218, B_219, B_221, A_220))), inference(superposition, [status(thm), theory('equality')], [c_172, c_453])).
% 8.29/2.88  tff(c_6558, plain, (![A_12, B_13, D_15, C_14]: (k2_enumset1(A_12, B_13, D_15, C_14)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(superposition, [status(thm), theory('equality')], [c_12, c_6448])).
% 8.29/2.88  tff(c_20, plain, (![A_24, B_25, C_26, D_27]: (k2_xboole_0(k1_tarski(A_24), k1_enumset1(B_25, C_26, D_27))=k2_enumset1(A_24, B_25, C_26, D_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.29/2.88  tff(c_358, plain, (![A_54, B_55, C_56]: (k2_xboole_0(k2_tarski(A_54, B_55), k1_tarski(C_56))=k1_enumset1(A_54, B_55, C_56))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.29/2.88  tff(c_561, plain, (![C_75, A_76, B_77]: (k2_xboole_0(k1_tarski(C_75), k2_tarski(A_76, B_77))=k1_enumset1(A_76, B_77, C_75))), inference(superposition, [status(thm), theory('equality')], [c_2, c_358])).
% 8.29/2.88  tff(c_16, plain, (![A_18, B_19, C_20]: (k2_xboole_0(k1_tarski(A_18), k2_tarski(B_19, C_20))=k1_enumset1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.29/2.88  tff(c_697, plain, (![C_83, A_84, B_85]: (k1_enumset1(C_83, A_84, B_85)=k1_enumset1(A_84, B_85, C_83))), inference(superposition, [status(thm), theory('equality')], [c_561, c_16])).
% 8.29/2.88  tff(c_11978, plain, (![A_282, A_283, B_284, C_285]: (k2_xboole_0(k1_tarski(A_282), k1_enumset1(A_283, B_284, C_285))=k2_enumset1(A_282, C_285, A_283, B_284))), inference(superposition, [status(thm), theory('equality')], [c_697, c_20])).
% 8.29/2.88  tff(c_12076, plain, (![A_24, D_27, B_25, C_26]: (k2_enumset1(A_24, D_27, B_25, C_26)=k2_enumset1(A_24, B_25, C_26, D_27))), inference(superposition, [status(thm), theory('equality')], [c_20, c_11978])).
% 8.29/2.88  tff(c_486, plain, (![C_63, D_64, A_61, B_62]: (k2_xboole_0(k2_tarski(C_63, D_64), k2_tarski(A_61, B_62))=k2_enumset1(A_61, B_62, C_63, D_64))), inference(superposition, [status(thm), theory('equality')], [c_2, c_453])).
% 8.29/2.88  tff(c_6486, plain, (![A_220, B_221, A_218, B_219]: (k2_enumset1(A_220, B_221, A_218, B_219)=k2_enumset1(A_218, B_219, B_221, A_220))), inference(superposition, [status(thm), theory('equality')], [c_6448, c_486])).
% 8.29/2.88  tff(c_22, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k1_tarski('#skF_4'))!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.29/2.88  tff(c_23, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_enumset1('#skF_1', '#skF_2', '#skF_3'))!=k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 8.29/2.88  tff(c_24, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_23])).
% 8.29/2.88  tff(c_6607, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6486, c_24])).
% 8.29/2.88  tff(c_9719, plain, (k2_enumset1('#skF_4', '#skF_3', '#skF_1', '#skF_2')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6558, c_6607])).
% 8.29/2.88  tff(c_12121, plain, (k2_enumset1('#skF_4', '#skF_1', '#skF_2', '#skF_3')!=k2_enumset1('#skF_4', '#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12076, c_9719])).
% 8.29/2.88  tff(c_12124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6558, c_12121])).
% 8.29/2.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.29/2.88  
% 8.29/2.88  Inference rules
% 8.29/2.88  ----------------------
% 8.29/2.88  #Ref     : 0
% 8.29/2.88  #Sup     : 2834
% 8.29/2.88  #Fact    : 0
% 8.29/2.88  #Define  : 0
% 8.29/2.88  #Split   : 0
% 8.29/2.88  #Chain   : 0
% 8.29/2.88  #Close   : 0
% 8.29/2.88  
% 8.29/2.88  Ordering : KBO
% 8.29/2.88  
% 8.29/2.88  Simplification rules
% 8.29/2.88  ----------------------
% 8.29/2.88  #Subsume      : 491
% 8.29/2.88  #Demod        : 3754
% 8.29/2.88  #Tautology    : 1842
% 8.29/2.88  #SimpNegUnit  : 0
% 8.29/2.88  #BackRed      : 3
% 8.29/2.88  
% 8.29/2.88  #Partial instantiations: 0
% 8.29/2.88  #Strategies tried      : 1
% 8.29/2.88  
% 8.29/2.88  Timing (in seconds)
% 8.29/2.88  ----------------------
% 8.29/2.89  Preprocessing        : 0.27
% 8.29/2.89  Parsing              : 0.15
% 8.29/2.89  CNF conversion       : 0.02
% 8.29/2.89  Main loop            : 1.86
% 8.29/2.89  Inferencing          : 0.50
% 8.29/2.89  Reduction            : 1.05
% 8.29/2.89  Demodulation         : 0.94
% 8.29/2.89  BG Simplification    : 0.05
% 8.29/2.89  Subsumption          : 0.20
% 8.29/2.89  Abstraction          : 0.10
% 8.29/2.89  MUC search           : 0.00
% 8.29/2.89  Cooper               : 0.00
% 8.29/2.89  Total                : 2.16
% 8.29/2.89  Index Insertion      : 0.00
% 8.29/2.89  Index Deletion       : 0.00
% 8.29/2.89  Index Matching       : 0.00
% 8.29/2.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
