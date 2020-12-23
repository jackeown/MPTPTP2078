%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:24 EST 2020

% Result     : Theorem 6.93s
% Output     : CNFRefutation 6.93s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 217 expanded)
%              Number of leaves         :   24 (  85 expanded)
%              Depth                    :   11
%              Number of atoms          :   41 ( 203 expanded)
%              Number of equality atoms :   40 ( 202 expanded)
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

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,D,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,A,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_18,plain,(
    ! [A_27,B_28,C_29] : k2_enumset1(A_27,A_27,B_28,C_29) = k1_enumset1(A_27,B_28,C_29) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_8,C_10,D_11,B_9] : k2_enumset1(A_8,C_10,D_11,B_9) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_30,B_31,C_32,D_33] : k3_enumset1(A_30,A_30,B_31,C_32,D_33) = k2_enumset1(A_30,B_31,C_32,D_33) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_25,B_26] : k1_enumset1(A_25,A_25,B_26) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1677,plain,(
    ! [C_105,D_103,A_104,E_102,B_106] : k2_xboole_0(k1_enumset1(A_104,B_106,C_105),k2_tarski(D_103,E_102)) = k3_enumset1(A_104,B_106,C_105,D_103,E_102) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1701,plain,(
    ! [A_25,B_26,D_103,E_102] : k3_enumset1(A_25,A_25,B_26,D_103,E_102) = k2_xboole_0(k2_tarski(A_25,B_26),k2_tarski(D_103,E_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1677])).

tff(c_1707,plain,(
    ! [A_25,B_26,D_103,E_102] : k2_xboole_0(k2_tarski(A_25,B_26),k2_tarski(D_103,E_102)) = k2_enumset1(A_25,B_26,D_103,E_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1701])).

tff(c_400,plain,(
    ! [B_63,D_64,A_65,C_66] : k2_enumset1(B_63,D_64,A_65,C_66) = k2_enumset1(A_65,B_63,C_66,D_64) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_538,plain,(
    ! [A_67,D_68,C_69] : k2_enumset1(A_67,D_68,C_69,D_68) = k1_enumset1(D_68,A_67,C_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_18])).

tff(c_570,plain,(
    ! [A_67,C_69,D_68] : k2_enumset1(A_67,C_69,D_68,D_68) = k1_enumset1(D_68,A_67,C_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_538,c_6])).

tff(c_12,plain,(
    ! [A_20,B_21,C_22,D_23] : k2_xboole_0(k1_enumset1(A_20,B_21,C_22),k1_tarski(D_23)) = k2_enumset1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1704,plain,(
    ! [A_104,B_106,C_105,A_24] : k3_enumset1(A_104,B_106,C_105,A_24,A_24) = k2_xboole_0(k1_enumset1(A_104,B_106,C_105),k1_tarski(A_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1677])).

tff(c_7023,plain,(
    ! [A_160,B_161,C_162,A_163] : k3_enumset1(A_160,B_161,C_162,A_163,A_163) = k2_enumset1(A_160,B_161,C_162,A_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1704])).

tff(c_7030,plain,(
    ! [B_161,C_162,A_163] : k2_enumset1(B_161,C_162,A_163,A_163) = k2_enumset1(B_161,B_161,C_162,A_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_7023,c_20])).

tff(c_7042,plain,(
    ! [B_164,C_165,A_166] : k1_enumset1(B_164,C_165,A_166) = k1_enumset1(A_166,B_164,C_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_18,c_7030])).

tff(c_102,plain,(
    ! [B_46,D_47,C_48,A_49] : k2_enumset1(B_46,D_47,C_48,A_49) = k2_enumset1(A_49,B_46,C_48,D_47) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_299,plain,(
    ! [A_58,D_59,C_60] : k2_enumset1(A_58,D_59,C_60,D_59) = k1_enumset1(D_59,C_60,A_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_18])).

tff(c_59,plain,(
    ! [A_42,C_43,D_44,B_45] : k2_enumset1(A_42,C_43,D_44,B_45) = k2_enumset1(A_42,B_45,C_43,D_44) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [C_43,B_45,D_44] : k2_enumset1(C_43,B_45,C_43,D_44) = k1_enumset1(C_43,D_44,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_18])).

tff(c_306,plain,(
    ! [D_59,C_60] : k1_enumset1(D_59,C_60,C_60) = k1_enumset1(C_60,D_59,D_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_79])).

tff(c_7082,plain,(
    ! [C_165,A_166] : k1_enumset1(C_165,C_165,A_166) = k1_enumset1(C_165,A_166,A_166) ),
    inference(superposition,[status(thm),theory(equality)],[c_7042,c_306])).

tff(c_7161,plain,(
    ! [C_165,A_166] : k1_enumset1(C_165,A_166,A_166) = k2_tarski(C_165,A_166) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_7082])).

tff(c_7175,plain,(
    ! [D_59,C_60] : k2_tarski(D_59,C_60) = k2_tarski(C_60,D_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7161,c_7161,c_306])).

tff(c_134,plain,(
    ! [A_49,D_47,C_48] : k2_enumset1(A_49,D_47,C_48,D_47) = k1_enumset1(D_47,C_48,A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_18])).

tff(c_550,plain,(
    ! [D_68,C_69,A_67] : k1_enumset1(D_68,C_69,A_67) = k1_enumset1(D_68,A_67,C_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_538,c_134])).

tff(c_22,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_627,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_22])).

tff(c_7226,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_3')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7175,c_7175,c_627])).

tff(c_7336,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1707,c_7226])).

tff(c_7339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6,c_6,c_7336])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:18:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.93/2.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.93/2.66  
% 6.93/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.93/2.66  %$ k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 6.93/2.66  
% 6.93/2.66  %Foreground sorts:
% 6.93/2.66  
% 6.93/2.66  
% 6.93/2.66  %Background operators:
% 6.93/2.66  
% 6.93/2.66  
% 6.93/2.66  %Foreground operators:
% 6.93/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.93/2.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.93/2.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.93/2.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.93/2.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.93/2.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.93/2.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.93/2.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.93/2.66  tff('#skF_2', type, '#skF_2': $i).
% 6.93/2.66  tff('#skF_3', type, '#skF_3': $i).
% 6.93/2.66  tff('#skF_1', type, '#skF_1': $i).
% 6.93/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.93/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.93/2.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.93/2.66  
% 6.93/2.67  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 6.93/2.67  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, D, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_enumset1)).
% 6.93/2.67  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 6.93/2.67  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.93/2.67  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 6.93/2.67  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_enumset1)).
% 6.93/2.67  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 6.93/2.67  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.93/2.67  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 6.93/2.67  tff(f_48, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 6.93/2.67  tff(c_18, plain, (![A_27, B_28, C_29]: (k2_enumset1(A_27, A_27, B_28, C_29)=k1_enumset1(A_27, B_28, C_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.93/2.67  tff(c_6, plain, (![A_8, C_10, D_11, B_9]: (k2_enumset1(A_8, C_10, D_11, B_9)=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.93/2.67  tff(c_20, plain, (![A_30, B_31, C_32, D_33]: (k3_enumset1(A_30, A_30, B_31, C_32, D_33)=k2_enumset1(A_30, B_31, C_32, D_33))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.93/2.67  tff(c_16, plain, (![A_25, B_26]: (k1_enumset1(A_25, A_25, B_26)=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.93/2.67  tff(c_1677, plain, (![C_105, D_103, A_104, E_102, B_106]: (k2_xboole_0(k1_enumset1(A_104, B_106, C_105), k2_tarski(D_103, E_102))=k3_enumset1(A_104, B_106, C_105, D_103, E_102))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.93/2.67  tff(c_1701, plain, (![A_25, B_26, D_103, E_102]: (k3_enumset1(A_25, A_25, B_26, D_103, E_102)=k2_xboole_0(k2_tarski(A_25, B_26), k2_tarski(D_103, E_102)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1677])).
% 6.93/2.67  tff(c_1707, plain, (![A_25, B_26, D_103, E_102]: (k2_xboole_0(k2_tarski(A_25, B_26), k2_tarski(D_103, E_102))=k2_enumset1(A_25, B_26, D_103, E_102))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1701])).
% 6.93/2.67  tff(c_400, plain, (![B_63, D_64, A_65, C_66]: (k2_enumset1(B_63, D_64, A_65, C_66)=k2_enumset1(A_65, B_63, C_66, D_64))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.93/2.67  tff(c_538, plain, (![A_67, D_68, C_69]: (k2_enumset1(A_67, D_68, C_69, D_68)=k1_enumset1(D_68, A_67, C_69))), inference(superposition, [status(thm), theory('equality')], [c_400, c_18])).
% 6.93/2.67  tff(c_570, plain, (![A_67, C_69, D_68]: (k2_enumset1(A_67, C_69, D_68, D_68)=k1_enumset1(D_68, A_67, C_69))), inference(superposition, [status(thm), theory('equality')], [c_538, c_6])).
% 6.93/2.67  tff(c_12, plain, (![A_20, B_21, C_22, D_23]: (k2_xboole_0(k1_enumset1(A_20, B_21, C_22), k1_tarski(D_23))=k2_enumset1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.93/2.67  tff(c_14, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.93/2.67  tff(c_1704, plain, (![A_104, B_106, C_105, A_24]: (k3_enumset1(A_104, B_106, C_105, A_24, A_24)=k2_xboole_0(k1_enumset1(A_104, B_106, C_105), k1_tarski(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1677])).
% 6.93/2.67  tff(c_7023, plain, (![A_160, B_161, C_162, A_163]: (k3_enumset1(A_160, B_161, C_162, A_163, A_163)=k2_enumset1(A_160, B_161, C_162, A_163))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1704])).
% 6.93/2.67  tff(c_7030, plain, (![B_161, C_162, A_163]: (k2_enumset1(B_161, C_162, A_163, A_163)=k2_enumset1(B_161, B_161, C_162, A_163))), inference(superposition, [status(thm), theory('equality')], [c_7023, c_20])).
% 6.93/2.67  tff(c_7042, plain, (![B_164, C_165, A_166]: (k1_enumset1(B_164, C_165, A_166)=k1_enumset1(A_166, B_164, C_165))), inference(demodulation, [status(thm), theory('equality')], [c_570, c_18, c_7030])).
% 6.93/2.67  tff(c_102, plain, (![B_46, D_47, C_48, A_49]: (k2_enumset1(B_46, D_47, C_48, A_49)=k2_enumset1(A_49, B_46, C_48, D_47))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.93/2.67  tff(c_299, plain, (![A_58, D_59, C_60]: (k2_enumset1(A_58, D_59, C_60, D_59)=k1_enumset1(D_59, C_60, A_58))), inference(superposition, [status(thm), theory('equality')], [c_102, c_18])).
% 6.93/2.67  tff(c_59, plain, (![A_42, C_43, D_44, B_45]: (k2_enumset1(A_42, C_43, D_44, B_45)=k2_enumset1(A_42, B_45, C_43, D_44))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.93/2.67  tff(c_79, plain, (![C_43, B_45, D_44]: (k2_enumset1(C_43, B_45, C_43, D_44)=k1_enumset1(C_43, D_44, B_45))), inference(superposition, [status(thm), theory('equality')], [c_59, c_18])).
% 6.93/2.67  tff(c_306, plain, (![D_59, C_60]: (k1_enumset1(D_59, C_60, C_60)=k1_enumset1(C_60, D_59, D_59))), inference(superposition, [status(thm), theory('equality')], [c_299, c_79])).
% 6.93/2.67  tff(c_7082, plain, (![C_165, A_166]: (k1_enumset1(C_165, C_165, A_166)=k1_enumset1(C_165, A_166, A_166))), inference(superposition, [status(thm), theory('equality')], [c_7042, c_306])).
% 6.93/2.67  tff(c_7161, plain, (![C_165, A_166]: (k1_enumset1(C_165, A_166, A_166)=k2_tarski(C_165, A_166))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_7082])).
% 6.93/2.67  tff(c_7175, plain, (![D_59, C_60]: (k2_tarski(D_59, C_60)=k2_tarski(C_60, D_59))), inference(demodulation, [status(thm), theory('equality')], [c_7161, c_7161, c_306])).
% 6.93/2.67  tff(c_134, plain, (![A_49, D_47, C_48]: (k2_enumset1(A_49, D_47, C_48, D_47)=k1_enumset1(D_47, C_48, A_49))), inference(superposition, [status(thm), theory('equality')], [c_102, c_18])).
% 6.93/2.67  tff(c_550, plain, (![D_68, C_69, A_67]: (k1_enumset1(D_68, C_69, A_67)=k1_enumset1(D_68, A_67, C_69))), inference(superposition, [status(thm), theory('equality')], [c_538, c_134])).
% 6.93/2.67  tff(c_22, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.93/2.67  tff(c_627, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_550, c_22])).
% 6.93/2.67  tff(c_7226, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_3'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7175, c_7175, c_627])).
% 6.93/2.67  tff(c_7336, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1707, c_7226])).
% 6.93/2.67  tff(c_7339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_6, c_6, c_7336])).
% 6.93/2.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.93/2.67  
% 6.93/2.67  Inference rules
% 6.93/2.67  ----------------------
% 6.93/2.67  #Ref     : 0
% 6.93/2.67  #Sup     : 1932
% 6.93/2.67  #Fact    : 0
% 6.93/2.67  #Define  : 0
% 6.93/2.67  #Split   : 0
% 6.93/2.67  #Chain   : 0
% 6.93/2.67  #Close   : 0
% 6.93/2.67  
% 6.93/2.67  Ordering : KBO
% 6.93/2.67  
% 6.93/2.67  Simplification rules
% 6.93/2.67  ----------------------
% 6.93/2.67  #Subsume      : 655
% 6.93/2.67  #Demod        : 932
% 6.93/2.67  #Tautology    : 963
% 6.93/2.67  #SimpNegUnit  : 0
% 6.93/2.68  #BackRed      : 4
% 6.93/2.68  
% 6.93/2.68  #Partial instantiations: 0
% 6.93/2.68  #Strategies tried      : 1
% 6.93/2.68  
% 6.93/2.68  Timing (in seconds)
% 6.93/2.68  ----------------------
% 6.93/2.68  Preprocessing        : 0.31
% 6.93/2.68  Parsing              : 0.17
% 6.93/2.68  CNF conversion       : 0.02
% 6.93/2.68  Main loop            : 1.53
% 6.93/2.68  Inferencing          : 0.42
% 6.93/2.68  Reduction            : 0.87
% 6.93/2.68  Demodulation         : 0.81
% 6.93/2.68  BG Simplification    : 0.04
% 6.93/2.68  Subsumption          : 0.16
% 6.93/2.68  Abstraction          : 0.07
% 6.93/2.68  MUC search           : 0.00
% 6.93/2.68  Cooper               : 0.00
% 6.93/2.68  Total                : 1.88
% 6.93/2.68  Index Insertion      : 0.00
% 6.93/2.68  Index Deletion       : 0.00
% 6.93/2.68  Index Matching       : 0.00
% 6.93/2.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
