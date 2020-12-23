%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:50 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   40 (  59 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   24 (  43 expanded)
%              Number of equality atoms :   23 (  42 expanded)
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

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_38,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

tff(c_8,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k1_tarski(A_13),k2_tarski(B_14,C_15)) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_31,plain,(
    ! [A_25,B_26,C_27] : k2_xboole_0(k2_xboole_0(A_25,B_26),C_27) = k2_xboole_0(A_25,k2_xboole_0(B_26,C_27)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    ! [A_32,B_33,C_34] : k2_xboole_0(k1_tarski(A_32),k2_xboole_0(k1_tarski(B_33),C_34)) = k2_xboole_0(k2_tarski(A_32,B_33),C_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_31])).

tff(c_90,plain,(
    ! [A_32,A_11,B_12] : k2_xboole_0(k2_tarski(A_32,A_11),k1_tarski(B_12)) = k2_xboole_0(k1_tarski(A_32),k2_tarski(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_66])).

tff(c_96,plain,(
    ! [A_35,A_36,B_37] : k2_xboole_0(k2_tarski(A_35,A_36),k1_tarski(B_37)) = k1_enumset1(A_35,A_36,B_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_90])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_102,plain,(
    ! [A_35,A_36,B_37,C_3] : k2_xboole_0(k2_tarski(A_35,A_36),k2_xboole_0(k1_tarski(B_37),C_3)) = k2_xboole_0(k1_enumset1(A_35,A_36,B_37),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_2])).

tff(c_4,plain,(
    ! [B_5,D_7,A_4,G_10,E_8,C_6,F_9] : k2_xboole_0(k2_enumset1(A_4,B_5,C_6,D_7),k1_enumset1(E_8,F_9,G_10)) = k5_enumset1(A_4,B_5,C_6,D_7,E_8,F_9,G_10) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_16,B_17,C_18,D_19] : k2_xboole_0(k1_tarski(A_16),k1_enumset1(B_17,C_18,D_19)) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [C_18,B_17,A_16,D_19,A_32] : k2_xboole_0(k2_tarski(A_32,A_16),k1_enumset1(B_17,C_18,D_19)) = k2_xboole_0(k1_tarski(A_32),k2_enumset1(A_16,B_17,C_18,D_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_66])).

tff(c_87,plain,(
    ! [A_32,A_13,B_14,C_15] : k2_xboole_0(k2_tarski(A_32,A_13),k2_tarski(B_14,C_15)) = k2_xboole_0(k1_tarski(A_32),k1_enumset1(A_13,B_14,C_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_66])).

tff(c_108,plain,(
    ! [A_38,A_39,B_40,C_41] : k2_xboole_0(k2_tarski(A_38,A_39),k2_tarski(B_40,C_41)) = k2_enumset1(A_38,A_39,B_40,C_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_87])).

tff(c_276,plain,(
    ! [A_85,C_87,A_84,C_88,B_86] : k2_xboole_0(k2_tarski(A_85,A_84),k2_xboole_0(k2_tarski(B_86,C_87),C_88)) = k2_xboole_0(k2_enumset1(A_85,A_84,B_86,C_87),C_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_2])).

tff(c_297,plain,(
    ! [A_85,C_18,B_17,A_16,D_19,A_84,A_32] : k2_xboole_0(k2_tarski(A_85,A_84),k2_xboole_0(k1_tarski(A_32),k2_enumset1(A_16,B_17,C_18,D_19))) = k2_xboole_0(k2_enumset1(A_85,A_84,A_32,A_16),k1_enumset1(B_17,C_18,D_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_276])).

tff(c_310,plain,(
    ! [A_85,C_18,B_17,A_16,D_19,A_84,A_32] : k2_xboole_0(k1_enumset1(A_85,A_84,A_32),k2_enumset1(A_16,B_17,C_18,D_19)) = k5_enumset1(A_85,A_84,A_32,A_16,B_17,C_18,D_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_4,c_297])).

tff(c_12,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k2_enumset1('#skF_4','#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:04:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.44  
% 2.39/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.44  %$ k5_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.39/1.44  
% 2.39/1.44  %Foreground sorts:
% 2.39/1.44  
% 2.39/1.44  
% 2.39/1.44  %Background operators:
% 2.39/1.44  
% 2.39/1.44  
% 2.39/1.44  %Foreground operators:
% 2.39/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.39/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.39/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.39/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.39/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.39/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.39/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.39/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.39/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.39/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.39/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.39/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.39/1.44  
% 2.39/1.45  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.39/1.45  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.39/1.45  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.39/1.45  tff(f_29, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 2.39/1.45  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 2.39/1.45  tff(f_38, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 2.39/1.45  tff(c_8, plain, (![A_13, B_14, C_15]: (k2_xboole_0(k1_tarski(A_13), k2_tarski(B_14, C_15))=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.39/1.45  tff(c_6, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(B_12))=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.39/1.45  tff(c_31, plain, (![A_25, B_26, C_27]: (k2_xboole_0(k2_xboole_0(A_25, B_26), C_27)=k2_xboole_0(A_25, k2_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.39/1.45  tff(c_66, plain, (![A_32, B_33, C_34]: (k2_xboole_0(k1_tarski(A_32), k2_xboole_0(k1_tarski(B_33), C_34))=k2_xboole_0(k2_tarski(A_32, B_33), C_34))), inference(superposition, [status(thm), theory('equality')], [c_6, c_31])).
% 2.39/1.45  tff(c_90, plain, (![A_32, A_11, B_12]: (k2_xboole_0(k2_tarski(A_32, A_11), k1_tarski(B_12))=k2_xboole_0(k1_tarski(A_32), k2_tarski(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_66])).
% 2.39/1.45  tff(c_96, plain, (![A_35, A_36, B_37]: (k2_xboole_0(k2_tarski(A_35, A_36), k1_tarski(B_37))=k1_enumset1(A_35, A_36, B_37))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_90])).
% 2.39/1.45  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.39/1.45  tff(c_102, plain, (![A_35, A_36, B_37, C_3]: (k2_xboole_0(k2_tarski(A_35, A_36), k2_xboole_0(k1_tarski(B_37), C_3))=k2_xboole_0(k1_enumset1(A_35, A_36, B_37), C_3))), inference(superposition, [status(thm), theory('equality')], [c_96, c_2])).
% 2.39/1.45  tff(c_4, plain, (![B_5, D_7, A_4, G_10, E_8, C_6, F_9]: (k2_xboole_0(k2_enumset1(A_4, B_5, C_6, D_7), k1_enumset1(E_8, F_9, G_10))=k5_enumset1(A_4, B_5, C_6, D_7, E_8, F_9, G_10))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.39/1.45  tff(c_10, plain, (![A_16, B_17, C_18, D_19]: (k2_xboole_0(k1_tarski(A_16), k1_enumset1(B_17, C_18, D_19))=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.39/1.45  tff(c_84, plain, (![C_18, B_17, A_16, D_19, A_32]: (k2_xboole_0(k2_tarski(A_32, A_16), k1_enumset1(B_17, C_18, D_19))=k2_xboole_0(k1_tarski(A_32), k2_enumset1(A_16, B_17, C_18, D_19)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_66])).
% 2.39/1.45  tff(c_87, plain, (![A_32, A_13, B_14, C_15]: (k2_xboole_0(k2_tarski(A_32, A_13), k2_tarski(B_14, C_15))=k2_xboole_0(k1_tarski(A_32), k1_enumset1(A_13, B_14, C_15)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_66])).
% 2.39/1.45  tff(c_108, plain, (![A_38, A_39, B_40, C_41]: (k2_xboole_0(k2_tarski(A_38, A_39), k2_tarski(B_40, C_41))=k2_enumset1(A_38, A_39, B_40, C_41))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_87])).
% 2.39/1.45  tff(c_276, plain, (![A_85, C_87, A_84, C_88, B_86]: (k2_xboole_0(k2_tarski(A_85, A_84), k2_xboole_0(k2_tarski(B_86, C_87), C_88))=k2_xboole_0(k2_enumset1(A_85, A_84, B_86, C_87), C_88))), inference(superposition, [status(thm), theory('equality')], [c_108, c_2])).
% 2.39/1.45  tff(c_297, plain, (![A_85, C_18, B_17, A_16, D_19, A_84, A_32]: (k2_xboole_0(k2_tarski(A_85, A_84), k2_xboole_0(k1_tarski(A_32), k2_enumset1(A_16, B_17, C_18, D_19)))=k2_xboole_0(k2_enumset1(A_85, A_84, A_32, A_16), k1_enumset1(B_17, C_18, D_19)))), inference(superposition, [status(thm), theory('equality')], [c_84, c_276])).
% 2.39/1.45  tff(c_310, plain, (![A_85, C_18, B_17, A_16, D_19, A_84, A_32]: (k2_xboole_0(k1_enumset1(A_85, A_84, A_32), k2_enumset1(A_16, B_17, C_18, D_19))=k5_enumset1(A_85, A_84, A_32, A_16, B_17, C_18, D_19))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_4, c_297])).
% 2.39/1.45  tff(c_12, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k2_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.39/1.45  tff(c_427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_310, c_12])).
% 2.39/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.45  
% 2.39/1.45  Inference rules
% 2.39/1.45  ----------------------
% 2.39/1.45  #Ref     : 0
% 2.39/1.45  #Sup     : 105
% 2.39/1.45  #Fact    : 0
% 2.39/1.45  #Define  : 0
% 2.39/1.45  #Split   : 0
% 2.39/1.45  #Chain   : 0
% 2.39/1.45  #Close   : 0
% 2.39/1.45  
% 2.39/1.45  Ordering : KBO
% 2.39/1.45  
% 2.39/1.45  Simplification rules
% 2.39/1.45  ----------------------
% 2.39/1.45  #Subsume      : 0
% 2.39/1.45  #Demod        : 71
% 2.39/1.45  #Tautology    : 59
% 2.39/1.45  #SimpNegUnit  : 0
% 2.39/1.45  #BackRed      : 1
% 2.39/1.45  
% 2.39/1.45  #Partial instantiations: 0
% 2.39/1.45  #Strategies tried      : 1
% 2.39/1.45  
% 2.39/1.45  Timing (in seconds)
% 2.39/1.45  ----------------------
% 2.39/1.45  Preprocessing        : 0.29
% 2.39/1.45  Parsing              : 0.16
% 2.39/1.45  CNF conversion       : 0.02
% 2.39/1.45  Main loop            : 0.31
% 2.39/1.45  Inferencing          : 0.14
% 2.39/1.45  Reduction            : 0.10
% 2.39/1.45  Demodulation         : 0.09
% 2.39/1.45  BG Simplification    : 0.02
% 2.39/1.45  Subsumption          : 0.04
% 2.39/1.46  Abstraction          : 0.02
% 2.39/1.46  MUC search           : 0.00
% 2.39/1.46  Cooper               : 0.00
% 2.39/1.46  Total                : 0.63
% 2.39/1.46  Index Insertion      : 0.00
% 2.39/1.46  Index Deletion       : 0.00
% 2.39/1.46  Index Matching       : 0.00
% 2.39/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
