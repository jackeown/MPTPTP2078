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
% DateTime   : Thu Dec  3 09:45:51 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
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

tff(f_35,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_enumset1)).

tff(c_10,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,G_19,D_16] : k2_xboole_0(k1_enumset1(A_13,B_14,C_15),k2_enumset1(D_16,E_17,F_18,G_19)) = k5_enumset1(A_13,B_14,C_15,D_16,E_17,F_18,G_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11,D_12] : k2_xboole_0(k1_enumset1(A_9,B_10,C_11),k1_tarski(D_12)) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),k1_tarski(B_5)) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k2_xboole_0(k2_tarski(A_6,B_7),k1_tarski(C_8)) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_31,plain,(
    ! [A_25,B_26,C_27] : k2_xboole_0(k2_xboole_0(A_25,B_26),C_27) = k2_xboole_0(A_25,k2_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_116,plain,(
    ! [A_45,B_46,C_47,C_48] : k2_xboole_0(k2_tarski(A_45,B_46),k2_xboole_0(k1_tarski(C_47),C_48)) = k2_xboole_0(k1_enumset1(A_45,B_46,C_47),C_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_31])).

tff(c_134,plain,(
    ! [A_45,B_46,A_4,B_5] : k2_xboole_0(k1_enumset1(A_45,B_46,A_4),k1_tarski(B_5)) = k2_xboole_0(k2_tarski(A_45,B_46),k2_tarski(A_4,B_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_116])).

tff(c_138,plain,(
    ! [A_45,B_46,A_4,B_5] : k2_xboole_0(k2_tarski(A_45,B_46),k2_tarski(A_4,B_5)) = k2_enumset1(A_45,B_46,A_4,B_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_134])).

tff(c_66,plain,(
    ! [A_32,B_33,C_34] : k2_xboole_0(k1_tarski(A_32),k2_xboole_0(k1_tarski(B_33),C_34)) = k2_xboole_0(k2_tarski(A_32,B_33),C_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_31])).

tff(c_84,plain,(
    ! [A_32,A_4,B_5] : k2_xboole_0(k2_tarski(A_32,A_4),k1_tarski(B_5)) = k2_xboole_0(k1_tarski(A_32),k2_tarski(A_4,B_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_66])).

tff(c_88,plain,(
    ! [A_32,A_4,B_5] : k2_xboole_0(k1_tarski(A_32),k2_tarski(A_4,B_5)) = k1_enumset1(A_32,A_4,B_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_84])).

tff(c_49,plain,(
    ! [A_4,B_5,C_27] : k2_xboole_0(k1_tarski(A_4),k2_xboole_0(k1_tarski(B_5),C_27)) = k2_xboole_0(k2_tarski(A_4,B_5),C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_31])).

tff(c_54,plain,(
    ! [A_28,B_29,C_30,D_31] : k2_xboole_0(k1_enumset1(A_28,B_29,C_30),k1_tarski(D_31)) = k2_enumset1(A_28,B_29,C_30,D_31) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_199,plain,(
    ! [B_63,A_61,C_62,C_65,D_64] : k2_xboole_0(k1_enumset1(A_61,B_63,C_62),k2_xboole_0(k1_tarski(D_64),C_65)) = k2_xboole_0(k2_enumset1(A_61,B_63,C_62,D_64),C_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2])).

tff(c_486,plain,(
    ! [C_140,A_145,B_143,A_144,B_141,C_142] : k2_xboole_0(k2_enumset1(A_144,B_143,C_140,A_145),k2_xboole_0(k1_tarski(B_141),C_142)) = k2_xboole_0(k1_enumset1(A_144,B_143,C_140),k2_xboole_0(k2_tarski(A_145,B_141),C_142)) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_199])).

tff(c_510,plain,(
    ! [B_5,C_140,A_145,B_143,A_4,A_144,A_32] : k2_xboole_0(k1_enumset1(A_144,B_143,C_140),k2_xboole_0(k2_tarski(A_145,A_32),k2_tarski(A_4,B_5))) = k2_xboole_0(k2_enumset1(A_144,B_143,C_140,A_145),k1_enumset1(A_32,A_4,B_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_486])).

tff(c_522,plain,(
    ! [B_5,C_140,A_145,B_143,A_4,A_144,A_32] : k2_xboole_0(k2_enumset1(A_144,B_143,C_140,A_145),k1_enumset1(A_32,A_4,B_5)) = k5_enumset1(A_144,B_143,C_140,A_145,A_32,A_4,B_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_138,c_510])).

tff(c_12,plain,(
    k2_xboole_0(k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4'),k1_enumset1('#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_527,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.38  
% 2.69/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.38  %$ k5_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.69/1.38  
% 2.69/1.38  %Foreground sorts:
% 2.69/1.38  
% 2.69/1.38  
% 2.69/1.38  %Background operators:
% 2.69/1.38  
% 2.69/1.38  
% 2.69/1.38  %Foreground operators:
% 2.69/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.69/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.69/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.69/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.69/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.69/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.69/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.69/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.69/1.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.69/1.38  
% 2.69/1.39  tff(f_35, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 2.69/1.39  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.69/1.39  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.69/1.39  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 2.69/1.39  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.69/1.39  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_enumset1)).
% 2.69/1.39  tff(c_10, plain, (![E_17, F_18, A_13, B_14, C_15, G_19, D_16]: (k2_xboole_0(k1_enumset1(A_13, B_14, C_15), k2_enumset1(D_16, E_17, F_18, G_19))=k5_enumset1(A_13, B_14, C_15, D_16, E_17, F_18, G_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.69/1.39  tff(c_8, plain, (![A_9, B_10, C_11, D_12]: (k2_xboole_0(k1_enumset1(A_9, B_10, C_11), k1_tarski(D_12))=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.69/1.39  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(B_5))=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.39  tff(c_6, plain, (![A_6, B_7, C_8]: (k2_xboole_0(k2_tarski(A_6, B_7), k1_tarski(C_8))=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.39  tff(c_31, plain, (![A_25, B_26, C_27]: (k2_xboole_0(k2_xboole_0(A_25, B_26), C_27)=k2_xboole_0(A_25, k2_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.69/1.39  tff(c_116, plain, (![A_45, B_46, C_47, C_48]: (k2_xboole_0(k2_tarski(A_45, B_46), k2_xboole_0(k1_tarski(C_47), C_48))=k2_xboole_0(k1_enumset1(A_45, B_46, C_47), C_48))), inference(superposition, [status(thm), theory('equality')], [c_6, c_31])).
% 2.69/1.39  tff(c_134, plain, (![A_45, B_46, A_4, B_5]: (k2_xboole_0(k1_enumset1(A_45, B_46, A_4), k1_tarski(B_5))=k2_xboole_0(k2_tarski(A_45, B_46), k2_tarski(A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_116])).
% 2.69/1.39  tff(c_138, plain, (![A_45, B_46, A_4, B_5]: (k2_xboole_0(k2_tarski(A_45, B_46), k2_tarski(A_4, B_5))=k2_enumset1(A_45, B_46, A_4, B_5))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_134])).
% 2.69/1.39  tff(c_66, plain, (![A_32, B_33, C_34]: (k2_xboole_0(k1_tarski(A_32), k2_xboole_0(k1_tarski(B_33), C_34))=k2_xboole_0(k2_tarski(A_32, B_33), C_34))), inference(superposition, [status(thm), theory('equality')], [c_4, c_31])).
% 2.69/1.39  tff(c_84, plain, (![A_32, A_4, B_5]: (k2_xboole_0(k2_tarski(A_32, A_4), k1_tarski(B_5))=k2_xboole_0(k1_tarski(A_32), k2_tarski(A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_66])).
% 2.69/1.39  tff(c_88, plain, (![A_32, A_4, B_5]: (k2_xboole_0(k1_tarski(A_32), k2_tarski(A_4, B_5))=k1_enumset1(A_32, A_4, B_5))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_84])).
% 2.69/1.39  tff(c_49, plain, (![A_4, B_5, C_27]: (k2_xboole_0(k1_tarski(A_4), k2_xboole_0(k1_tarski(B_5), C_27))=k2_xboole_0(k2_tarski(A_4, B_5), C_27))), inference(superposition, [status(thm), theory('equality')], [c_4, c_31])).
% 2.69/1.39  tff(c_54, plain, (![A_28, B_29, C_30, D_31]: (k2_xboole_0(k1_enumset1(A_28, B_29, C_30), k1_tarski(D_31))=k2_enumset1(A_28, B_29, C_30, D_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.69/1.39  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.69/1.39  tff(c_199, plain, (![B_63, A_61, C_62, C_65, D_64]: (k2_xboole_0(k1_enumset1(A_61, B_63, C_62), k2_xboole_0(k1_tarski(D_64), C_65))=k2_xboole_0(k2_enumset1(A_61, B_63, C_62, D_64), C_65))), inference(superposition, [status(thm), theory('equality')], [c_54, c_2])).
% 2.69/1.39  tff(c_486, plain, (![C_140, A_145, B_143, A_144, B_141, C_142]: (k2_xboole_0(k2_enumset1(A_144, B_143, C_140, A_145), k2_xboole_0(k1_tarski(B_141), C_142))=k2_xboole_0(k1_enumset1(A_144, B_143, C_140), k2_xboole_0(k2_tarski(A_145, B_141), C_142)))), inference(superposition, [status(thm), theory('equality')], [c_49, c_199])).
% 2.69/1.39  tff(c_510, plain, (![B_5, C_140, A_145, B_143, A_4, A_144, A_32]: (k2_xboole_0(k1_enumset1(A_144, B_143, C_140), k2_xboole_0(k2_tarski(A_145, A_32), k2_tarski(A_4, B_5)))=k2_xboole_0(k2_enumset1(A_144, B_143, C_140, A_145), k1_enumset1(A_32, A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_486])).
% 2.69/1.39  tff(c_522, plain, (![B_5, C_140, A_145, B_143, A_4, A_144, A_32]: (k2_xboole_0(k2_enumset1(A_144, B_143, C_140, A_145), k1_enumset1(A_32, A_4, B_5))=k5_enumset1(A_144, B_143, C_140, A_145, A_32, A_4, B_5))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_138, c_510])).
% 2.69/1.39  tff(c_12, plain, (k2_xboole_0(k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k1_enumset1('#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.69/1.39  tff(c_527, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_522, c_12])).
% 2.69/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.39  
% 2.69/1.39  Inference rules
% 2.69/1.39  ----------------------
% 2.69/1.39  #Ref     : 0
% 2.69/1.39  #Sup     : 128
% 2.69/1.39  #Fact    : 0
% 2.69/1.39  #Define  : 0
% 2.69/1.39  #Split   : 0
% 2.69/1.39  #Chain   : 0
% 2.69/1.39  #Close   : 0
% 2.69/1.39  
% 2.69/1.39  Ordering : KBO
% 2.69/1.39  
% 2.69/1.39  Simplification rules
% 2.69/1.39  ----------------------
% 2.69/1.39  #Subsume      : 0
% 2.69/1.39  #Demod        : 85
% 2.69/1.39  #Tautology    : 74
% 2.69/1.39  #SimpNegUnit  : 0
% 2.69/1.39  #BackRed      : 5
% 2.69/1.39  
% 2.69/1.39  #Partial instantiations: 0
% 2.69/1.39  #Strategies tried      : 1
% 2.69/1.39  
% 2.69/1.39  Timing (in seconds)
% 2.69/1.39  ----------------------
% 2.69/1.39  Preprocessing        : 0.26
% 2.69/1.39  Parsing              : 0.15
% 2.69/1.39  CNF conversion       : 0.01
% 2.69/1.39  Main loop            : 0.33
% 2.69/1.39  Inferencing          : 0.15
% 2.69/1.39  Reduction            : 0.11
% 2.69/1.39  Demodulation         : 0.09
% 2.69/1.39  BG Simplification    : 0.02
% 2.69/1.39  Subsumption          : 0.04
% 2.69/1.39  Abstraction          : 0.03
% 2.69/1.39  MUC search           : 0.00
% 2.69/1.39  Cooper               : 0.00
% 2.69/1.39  Total                : 0.62
% 2.69/1.39  Index Insertion      : 0.00
% 2.69/1.39  Index Deletion       : 0.00
% 2.69/1.39  Index Matching       : 0.00
% 2.69/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
