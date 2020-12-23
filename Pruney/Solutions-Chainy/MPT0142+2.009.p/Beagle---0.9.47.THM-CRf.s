%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:50 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   42 (  56 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   26 (  40 expanded)
%              Number of equality atoms :   25 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

tff(c_4,plain,(
    ! [B_5,D_7,A_4,G_10,E_8,C_6,F_9] : k2_xboole_0(k2_enumset1(A_4,B_5,C_6,D_7),k1_enumset1(E_8,F_9,G_10)) = k5_enumset1(A_4,B_5,C_6,D_7,E_8,F_9,G_10) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_16,B_17,C_18,D_19] : k2_xboole_0(k1_enumset1(A_16,B_17,C_18),k1_tarski(D_19)) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k2_tarski(A_13,B_14),k1_tarski(C_15)) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_31,plain,(
    ! [A_25,B_26,C_27] : k2_xboole_0(k2_xboole_0(A_25,B_26),C_27) = k2_xboole_0(A_25,k2_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_104,plain,(
    ! [A_38,B_39,C_40,C_41] : k2_xboole_0(k2_tarski(A_38,B_39),k2_xboole_0(k1_tarski(C_40),C_41)) = k2_xboole_0(k1_enumset1(A_38,B_39,C_40),C_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_31])).

tff(c_122,plain,(
    ! [A_38,B_39,A_11,B_12] : k2_xboole_0(k1_enumset1(A_38,B_39,A_11),k1_tarski(B_12)) = k2_xboole_0(k2_tarski(A_38,B_39),k2_tarski(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_104])).

tff(c_126,plain,(
    ! [A_38,B_39,A_11,B_12] : k2_xboole_0(k2_tarski(A_38,B_39),k2_tarski(A_11,B_12)) = k2_enumset1(A_38,B_39,A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_122])).

tff(c_66,plain,(
    ! [A_32,B_33,C_34] : k2_xboole_0(k1_tarski(A_32),k2_xboole_0(k1_tarski(B_33),C_34)) = k2_xboole_0(k2_tarski(A_32,B_33),C_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_31])).

tff(c_84,plain,(
    ! [A_32,A_11,B_12] : k2_xboole_0(k2_tarski(A_32,A_11),k1_tarski(B_12)) = k2_xboole_0(k1_tarski(A_32),k2_tarski(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_66])).

tff(c_88,plain,(
    ! [A_32,A_11,B_12] : k2_xboole_0(k1_tarski(A_32),k2_tarski(A_11,B_12)) = k1_enumset1(A_32,A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_84])).

tff(c_49,plain,(
    ! [A_11,B_12,C_27] : k2_xboole_0(k1_tarski(A_11),k2_xboole_0(k1_tarski(B_12),C_27)) = k2_xboole_0(k2_tarski(A_11,B_12),C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_31])).

tff(c_54,plain,(
    ! [A_28,B_29,C_30,D_31] : k2_xboole_0(k1_enumset1(A_28,B_29,C_30),k1_tarski(D_31)) = k2_enumset1(A_28,B_29,C_30,D_31) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_199,plain,(
    ! [B_63,A_61,C_62,C_65,D_64] : k2_xboole_0(k1_enumset1(A_61,B_63,C_62),k2_xboole_0(k1_tarski(D_64),C_65)) = k2_xboole_0(k2_enumset1(A_61,B_63,C_62,D_64),C_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2])).

tff(c_476,plain,(
    ! [B_144,C_140,A_145,B_143,C_141,A_142] : k2_xboole_0(k2_enumset1(A_145,B_143,C_140,A_142),k2_xboole_0(k1_tarski(B_144),C_141)) = k2_xboole_0(k1_enumset1(A_145,B_143,C_140),k2_xboole_0(k2_tarski(A_142,B_144),C_141)) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_199])).

tff(c_497,plain,(
    ! [C_140,A_145,B_143,A_142,A_32,B_12,A_11] : k2_xboole_0(k1_enumset1(A_145,B_143,C_140),k2_xboole_0(k2_tarski(A_142,A_32),k2_tarski(A_11,B_12))) = k2_xboole_0(k2_enumset1(A_145,B_143,C_140,A_142),k1_enumset1(A_32,A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_476])).

tff(c_509,plain,(
    ! [C_140,A_145,B_143,A_142,A_32,B_12,A_11] : k2_xboole_0(k1_enumset1(A_145,B_143,C_140),k2_enumset1(A_142,A_32,A_11,B_12)) = k5_enumset1(A_145,B_143,C_140,A_142,A_32,A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_126,c_497])).

tff(c_12,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k2_enumset1('#skF_4','#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.35  
% 2.54/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.35  %$ k5_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.54/1.35  
% 2.54/1.35  %Foreground sorts:
% 2.54/1.35  
% 2.54/1.35  
% 2.54/1.35  %Background operators:
% 2.54/1.35  
% 2.54/1.35  
% 2.54/1.35  %Foreground operators:
% 2.54/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.54/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.54/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.54/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.54/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.54/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.54/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.54/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.54/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.54/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.54/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.54/1.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.54/1.35  
% 2.54/1.36  tff(f_29, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 2.54/1.36  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.54/1.36  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.54/1.36  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.54/1.36  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.54/1.36  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 2.54/1.36  tff(c_4, plain, (![B_5, D_7, A_4, G_10, E_8, C_6, F_9]: (k2_xboole_0(k2_enumset1(A_4, B_5, C_6, D_7), k1_enumset1(E_8, F_9, G_10))=k5_enumset1(A_4, B_5, C_6, D_7, E_8, F_9, G_10))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.54/1.36  tff(c_10, plain, (![A_16, B_17, C_18, D_19]: (k2_xboole_0(k1_enumset1(A_16, B_17, C_18), k1_tarski(D_19))=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.54/1.36  tff(c_6, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(B_12))=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.54/1.36  tff(c_8, plain, (![A_13, B_14, C_15]: (k2_xboole_0(k2_tarski(A_13, B_14), k1_tarski(C_15))=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.54/1.36  tff(c_31, plain, (![A_25, B_26, C_27]: (k2_xboole_0(k2_xboole_0(A_25, B_26), C_27)=k2_xboole_0(A_25, k2_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.54/1.36  tff(c_104, plain, (![A_38, B_39, C_40, C_41]: (k2_xboole_0(k2_tarski(A_38, B_39), k2_xboole_0(k1_tarski(C_40), C_41))=k2_xboole_0(k1_enumset1(A_38, B_39, C_40), C_41))), inference(superposition, [status(thm), theory('equality')], [c_8, c_31])).
% 2.54/1.36  tff(c_122, plain, (![A_38, B_39, A_11, B_12]: (k2_xboole_0(k1_enumset1(A_38, B_39, A_11), k1_tarski(B_12))=k2_xboole_0(k2_tarski(A_38, B_39), k2_tarski(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_104])).
% 2.54/1.36  tff(c_126, plain, (![A_38, B_39, A_11, B_12]: (k2_xboole_0(k2_tarski(A_38, B_39), k2_tarski(A_11, B_12))=k2_enumset1(A_38, B_39, A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_122])).
% 2.54/1.36  tff(c_66, plain, (![A_32, B_33, C_34]: (k2_xboole_0(k1_tarski(A_32), k2_xboole_0(k1_tarski(B_33), C_34))=k2_xboole_0(k2_tarski(A_32, B_33), C_34))), inference(superposition, [status(thm), theory('equality')], [c_6, c_31])).
% 2.54/1.36  tff(c_84, plain, (![A_32, A_11, B_12]: (k2_xboole_0(k2_tarski(A_32, A_11), k1_tarski(B_12))=k2_xboole_0(k1_tarski(A_32), k2_tarski(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_66])).
% 2.54/1.36  tff(c_88, plain, (![A_32, A_11, B_12]: (k2_xboole_0(k1_tarski(A_32), k2_tarski(A_11, B_12))=k1_enumset1(A_32, A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_84])).
% 2.54/1.36  tff(c_49, plain, (![A_11, B_12, C_27]: (k2_xboole_0(k1_tarski(A_11), k2_xboole_0(k1_tarski(B_12), C_27))=k2_xboole_0(k2_tarski(A_11, B_12), C_27))), inference(superposition, [status(thm), theory('equality')], [c_6, c_31])).
% 2.54/1.36  tff(c_54, plain, (![A_28, B_29, C_30, D_31]: (k2_xboole_0(k1_enumset1(A_28, B_29, C_30), k1_tarski(D_31))=k2_enumset1(A_28, B_29, C_30, D_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.54/1.36  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.54/1.36  tff(c_199, plain, (![B_63, A_61, C_62, C_65, D_64]: (k2_xboole_0(k1_enumset1(A_61, B_63, C_62), k2_xboole_0(k1_tarski(D_64), C_65))=k2_xboole_0(k2_enumset1(A_61, B_63, C_62, D_64), C_65))), inference(superposition, [status(thm), theory('equality')], [c_54, c_2])).
% 2.54/1.36  tff(c_476, plain, (![B_144, C_140, A_145, B_143, C_141, A_142]: (k2_xboole_0(k2_enumset1(A_145, B_143, C_140, A_142), k2_xboole_0(k1_tarski(B_144), C_141))=k2_xboole_0(k1_enumset1(A_145, B_143, C_140), k2_xboole_0(k2_tarski(A_142, B_144), C_141)))), inference(superposition, [status(thm), theory('equality')], [c_49, c_199])).
% 2.54/1.36  tff(c_497, plain, (![C_140, A_145, B_143, A_142, A_32, B_12, A_11]: (k2_xboole_0(k1_enumset1(A_145, B_143, C_140), k2_xboole_0(k2_tarski(A_142, A_32), k2_tarski(A_11, B_12)))=k2_xboole_0(k2_enumset1(A_145, B_143, C_140, A_142), k1_enumset1(A_32, A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_476])).
% 2.54/1.36  tff(c_509, plain, (![C_140, A_145, B_143, A_142, A_32, B_12, A_11]: (k2_xboole_0(k1_enumset1(A_145, B_143, C_140), k2_enumset1(A_142, A_32, A_11, B_12))=k5_enumset1(A_145, B_143, C_140, A_142, A_32, A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_126, c_497])).
% 2.54/1.36  tff(c_12, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k2_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.54/1.36  tff(c_514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_509, c_12])).
% 2.54/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.36  
% 2.54/1.36  Inference rules
% 2.54/1.36  ----------------------
% 2.54/1.36  #Ref     : 0
% 2.54/1.36  #Sup     : 124
% 2.54/1.36  #Fact    : 0
% 2.54/1.36  #Define  : 0
% 2.54/1.36  #Split   : 0
% 2.54/1.36  #Chain   : 0
% 2.54/1.36  #Close   : 0
% 2.54/1.36  
% 2.54/1.36  Ordering : KBO
% 2.54/1.36  
% 2.54/1.36  Simplification rules
% 2.54/1.36  ----------------------
% 2.54/1.36  #Subsume      : 0
% 2.54/1.36  #Demod        : 84
% 2.54/1.36  #Tautology    : 74
% 2.54/1.36  #SimpNegUnit  : 0
% 2.54/1.36  #BackRed      : 5
% 2.54/1.36  
% 2.54/1.36  #Partial instantiations: 0
% 2.54/1.36  #Strategies tried      : 1
% 2.54/1.36  
% 2.54/1.36  Timing (in seconds)
% 2.54/1.36  ----------------------
% 2.54/1.37  Preprocessing        : 0.25
% 2.54/1.37  Parsing              : 0.14
% 2.54/1.37  CNF conversion       : 0.02
% 2.54/1.37  Main loop            : 0.34
% 2.54/1.37  Inferencing          : 0.15
% 2.54/1.37  Reduction            : 0.12
% 2.54/1.37  Demodulation         : 0.10
% 2.54/1.37  BG Simplification    : 0.02
% 2.54/1.37  Subsumption          : 0.04
% 2.54/1.37  Abstraction          : 0.03
% 2.54/1.37  MUC search           : 0.00
% 2.54/1.37  Cooper               : 0.00
% 2.54/1.37  Total                : 0.62
% 2.54/1.37  Index Insertion      : 0.00
% 2.54/1.37  Index Deletion       : 0.00
% 2.54/1.37  Index Matching       : 0.00
% 2.54/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
