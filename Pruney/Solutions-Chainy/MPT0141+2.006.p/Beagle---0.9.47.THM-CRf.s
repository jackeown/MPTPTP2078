%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:48 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   49 (  96 expanded)
%              Number of leaves         :   24 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :   32 (  79 expanded)
%              Number of equality atoms :   31 (  78 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

tff(c_4,plain,(
    ! [B_5,D_7,A_4,G_10,E_8,C_6,F_9] : k2_xboole_0(k2_enumset1(A_4,B_5,C_6,D_7),k1_enumset1(E_8,F_9,G_10)) = k5_enumset1(A_4,B_5,C_6,D_7,E_8,F_9,G_10) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33,plain,(
    ! [A_30,B_31,C_32] : k2_xboole_0(k2_xboole_0(A_30,B_31),C_32) = k2_xboole_0(A_30,k2_xboole_0(B_31,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_51,plain,(
    ! [A_11,B_12,C_32] : k2_xboole_0(k1_tarski(A_11),k2_xboole_0(k1_tarski(B_12),C_32)) = k2_xboole_0(k2_tarski(A_11,B_12),C_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_33])).

tff(c_94,plain,(
    ! [E_43,A_44,D_42,C_40,B_41] : k2_xboole_0(k1_tarski(A_44),k2_enumset1(B_41,C_40,D_42,E_43)) = k3_enumset1(A_44,B_41,C_40,D_42,E_43) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_100,plain,(
    ! [E_43,A_44,D_42,C_40,A_11,B_41] : k2_xboole_0(k2_tarski(A_11,A_44),k2_enumset1(B_41,C_40,D_42,E_43)) = k2_xboole_0(k1_tarski(A_11),k3_enumset1(A_44,B_41,C_40,D_42,E_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_51])).

tff(c_10,plain,(
    ! [A_16,B_17,C_18,D_19] : k2_xboole_0(k1_enumset1(A_16,B_17,C_18),k1_tarski(D_19)) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k1_tarski(A_13),k2_tarski(B_14,C_15)) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,(
    ! [A_37,B_38,C_39] : k2_xboole_0(k1_tarski(A_37),k2_xboole_0(k1_tarski(B_38),C_39)) = k2_xboole_0(k2_tarski(A_37,B_38),C_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_33])).

tff(c_89,plain,(
    ! [A_37,A_11,B_12] : k2_xboole_0(k2_tarski(A_37,A_11),k1_tarski(B_12)) = k2_xboole_0(k1_tarski(A_37),k2_tarski(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_68])).

tff(c_93,plain,(
    ! [A_37,A_11,B_12] : k2_xboole_0(k2_tarski(A_37,A_11),k1_tarski(B_12)) = k1_enumset1(A_37,A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_89])).

tff(c_121,plain,(
    ! [A_48,B_49,C_50,C_51] : k2_xboole_0(k1_tarski(A_48),k2_xboole_0(k2_tarski(B_49,C_50),C_51)) = k2_xboole_0(k1_enumset1(A_48,B_49,C_50),C_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_33])).

tff(c_136,plain,(
    ! [A_48,A_37,A_11,B_12] : k2_xboole_0(k1_enumset1(A_48,A_37,A_11),k1_tarski(B_12)) = k2_xboole_0(k1_tarski(A_48),k1_enumset1(A_37,A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_121])).

tff(c_140,plain,(
    ! [A_48,A_37,A_11,B_12] : k2_xboole_0(k1_tarski(A_48),k1_enumset1(A_37,A_11,B_12)) = k2_enumset1(A_48,A_37,A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_136])).

tff(c_109,plain,(
    ! [A_45,A_46,B_47] : k2_xboole_0(k2_tarski(A_45,A_46),k1_tarski(B_47)) = k1_enumset1(A_45,A_46,B_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_89])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_174,plain,(
    ! [A_60,A_61,B_62,C_63] : k2_xboole_0(k2_tarski(A_60,A_61),k2_xboole_0(k1_tarski(B_62),C_63)) = k2_xboole_0(k1_enumset1(A_60,A_61,B_62),C_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_2])).

tff(c_189,plain,(
    ! [A_61,A_60,A_48,A_37,B_12,A_11] : k2_xboole_0(k1_enumset1(A_60,A_61,A_48),k1_enumset1(A_37,A_11,B_12)) = k2_xboole_0(k2_tarski(A_60,A_61),k2_enumset1(A_48,A_37,A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_174])).

tff(c_458,plain,(
    ! [A_127,A_132,A_128,A_131,B_130,A_129] : k2_xboole_0(k1_enumset1(A_131,A_132,A_128),k1_enumset1(A_127,A_129,B_130)) = k2_xboole_0(k1_tarski(A_131),k3_enumset1(A_132,A_128,A_127,A_129,B_130)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_189])).

tff(c_141,plain,(
    ! [A_52,A_53,A_54,B_55] : k2_xboole_0(k1_tarski(A_52),k1_enumset1(A_53,A_54,B_55)) = k2_enumset1(A_52,A_53,A_54,B_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_136])).

tff(c_150,plain,(
    ! [A_53,C_3,A_52,B_55,A_54] : k2_xboole_0(k1_tarski(A_52),k2_xboole_0(k1_enumset1(A_53,A_54,B_55),C_3)) = k2_xboole_0(k2_enumset1(A_52,A_53,A_54,B_55),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_2])).

tff(c_467,plain,(
    ! [A_127,A_132,A_128,A_131,A_52,B_130,A_129] : k2_xboole_0(k1_tarski(A_52),k2_xboole_0(k1_tarski(A_131),k3_enumset1(A_132,A_128,A_127,A_129,B_130))) = k2_xboole_0(k2_enumset1(A_52,A_131,A_132,A_128),k1_enumset1(A_127,A_129,B_130)) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_150])).

tff(c_475,plain,(
    ! [A_127,A_132,A_128,A_131,A_52,B_130,A_129] : k2_xboole_0(k2_tarski(A_52,A_131),k3_enumset1(A_132,A_128,A_127,A_129,B_130)) = k5_enumset1(A_52,A_131,A_132,A_128,A_127,A_129,B_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_51,c_467])).

tff(c_14,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k3_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:20:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.45  
% 2.70/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.45  %$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.99/1.45  
% 2.99/1.45  %Foreground sorts:
% 2.99/1.45  
% 2.99/1.45  
% 2.99/1.45  %Background operators:
% 2.99/1.45  
% 2.99/1.45  
% 2.99/1.45  %Foreground operators:
% 2.99/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.99/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.99/1.45  tff('#skF_7', type, '#skF_7': $i).
% 2.99/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.99/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.99/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.99/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.99/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.99/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.99/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.99/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.99/1.45  
% 2.99/1.46  tff(f_29, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 2.99/1.46  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.99/1.46  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.99/1.46  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 2.99/1.46  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 2.99/1.46  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.99/1.46  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_enumset1)).
% 2.99/1.46  tff(c_4, plain, (![B_5, D_7, A_4, G_10, E_8, C_6, F_9]: (k2_xboole_0(k2_enumset1(A_4, B_5, C_6, D_7), k1_enumset1(E_8, F_9, G_10))=k5_enumset1(A_4, B_5, C_6, D_7, E_8, F_9, G_10))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.99/1.46  tff(c_6, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(B_12))=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.99/1.46  tff(c_33, plain, (![A_30, B_31, C_32]: (k2_xboole_0(k2_xboole_0(A_30, B_31), C_32)=k2_xboole_0(A_30, k2_xboole_0(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.99/1.46  tff(c_51, plain, (![A_11, B_12, C_32]: (k2_xboole_0(k1_tarski(A_11), k2_xboole_0(k1_tarski(B_12), C_32))=k2_xboole_0(k2_tarski(A_11, B_12), C_32))), inference(superposition, [status(thm), theory('equality')], [c_6, c_33])).
% 2.99/1.46  tff(c_94, plain, (![E_43, A_44, D_42, C_40, B_41]: (k2_xboole_0(k1_tarski(A_44), k2_enumset1(B_41, C_40, D_42, E_43))=k3_enumset1(A_44, B_41, C_40, D_42, E_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.99/1.46  tff(c_100, plain, (![E_43, A_44, D_42, C_40, A_11, B_41]: (k2_xboole_0(k2_tarski(A_11, A_44), k2_enumset1(B_41, C_40, D_42, E_43))=k2_xboole_0(k1_tarski(A_11), k3_enumset1(A_44, B_41, C_40, D_42, E_43)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_51])).
% 2.99/1.46  tff(c_10, plain, (![A_16, B_17, C_18, D_19]: (k2_xboole_0(k1_enumset1(A_16, B_17, C_18), k1_tarski(D_19))=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.99/1.46  tff(c_8, plain, (![A_13, B_14, C_15]: (k2_xboole_0(k1_tarski(A_13), k2_tarski(B_14, C_15))=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.99/1.46  tff(c_68, plain, (![A_37, B_38, C_39]: (k2_xboole_0(k1_tarski(A_37), k2_xboole_0(k1_tarski(B_38), C_39))=k2_xboole_0(k2_tarski(A_37, B_38), C_39))), inference(superposition, [status(thm), theory('equality')], [c_6, c_33])).
% 2.99/1.46  tff(c_89, plain, (![A_37, A_11, B_12]: (k2_xboole_0(k2_tarski(A_37, A_11), k1_tarski(B_12))=k2_xboole_0(k1_tarski(A_37), k2_tarski(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_68])).
% 2.99/1.46  tff(c_93, plain, (![A_37, A_11, B_12]: (k2_xboole_0(k2_tarski(A_37, A_11), k1_tarski(B_12))=k1_enumset1(A_37, A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_89])).
% 2.99/1.46  tff(c_121, plain, (![A_48, B_49, C_50, C_51]: (k2_xboole_0(k1_tarski(A_48), k2_xboole_0(k2_tarski(B_49, C_50), C_51))=k2_xboole_0(k1_enumset1(A_48, B_49, C_50), C_51))), inference(superposition, [status(thm), theory('equality')], [c_8, c_33])).
% 2.99/1.46  tff(c_136, plain, (![A_48, A_37, A_11, B_12]: (k2_xboole_0(k1_enumset1(A_48, A_37, A_11), k1_tarski(B_12))=k2_xboole_0(k1_tarski(A_48), k1_enumset1(A_37, A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_121])).
% 2.99/1.46  tff(c_140, plain, (![A_48, A_37, A_11, B_12]: (k2_xboole_0(k1_tarski(A_48), k1_enumset1(A_37, A_11, B_12))=k2_enumset1(A_48, A_37, A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_136])).
% 2.99/1.46  tff(c_109, plain, (![A_45, A_46, B_47]: (k2_xboole_0(k2_tarski(A_45, A_46), k1_tarski(B_47))=k1_enumset1(A_45, A_46, B_47))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_89])).
% 2.99/1.46  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.99/1.46  tff(c_174, plain, (![A_60, A_61, B_62, C_63]: (k2_xboole_0(k2_tarski(A_60, A_61), k2_xboole_0(k1_tarski(B_62), C_63))=k2_xboole_0(k1_enumset1(A_60, A_61, B_62), C_63))), inference(superposition, [status(thm), theory('equality')], [c_109, c_2])).
% 2.99/1.46  tff(c_189, plain, (![A_61, A_60, A_48, A_37, B_12, A_11]: (k2_xboole_0(k1_enumset1(A_60, A_61, A_48), k1_enumset1(A_37, A_11, B_12))=k2_xboole_0(k2_tarski(A_60, A_61), k2_enumset1(A_48, A_37, A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_140, c_174])).
% 2.99/1.46  tff(c_458, plain, (![A_127, A_132, A_128, A_131, B_130, A_129]: (k2_xboole_0(k1_enumset1(A_131, A_132, A_128), k1_enumset1(A_127, A_129, B_130))=k2_xboole_0(k1_tarski(A_131), k3_enumset1(A_132, A_128, A_127, A_129, B_130)))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_189])).
% 2.99/1.46  tff(c_141, plain, (![A_52, A_53, A_54, B_55]: (k2_xboole_0(k1_tarski(A_52), k1_enumset1(A_53, A_54, B_55))=k2_enumset1(A_52, A_53, A_54, B_55))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_136])).
% 2.99/1.46  tff(c_150, plain, (![A_53, C_3, A_52, B_55, A_54]: (k2_xboole_0(k1_tarski(A_52), k2_xboole_0(k1_enumset1(A_53, A_54, B_55), C_3))=k2_xboole_0(k2_enumset1(A_52, A_53, A_54, B_55), C_3))), inference(superposition, [status(thm), theory('equality')], [c_141, c_2])).
% 2.99/1.46  tff(c_467, plain, (![A_127, A_132, A_128, A_131, A_52, B_130, A_129]: (k2_xboole_0(k1_tarski(A_52), k2_xboole_0(k1_tarski(A_131), k3_enumset1(A_132, A_128, A_127, A_129, B_130)))=k2_xboole_0(k2_enumset1(A_52, A_131, A_132, A_128), k1_enumset1(A_127, A_129, B_130)))), inference(superposition, [status(thm), theory('equality')], [c_458, c_150])).
% 2.99/1.46  tff(c_475, plain, (![A_127, A_132, A_128, A_131, A_52, B_130, A_129]: (k2_xboole_0(k2_tarski(A_52, A_131), k3_enumset1(A_132, A_128, A_127, A_129, B_130))=k5_enumset1(A_52, A_131, A_132, A_128, A_127, A_129, B_130))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_51, c_467])).
% 2.99/1.46  tff(c_14, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k3_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.99/1.46  tff(c_676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_475, c_14])).
% 2.99/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.46  
% 2.99/1.46  Inference rules
% 2.99/1.46  ----------------------
% 2.99/1.46  #Ref     : 0
% 2.99/1.46  #Sup     : 170
% 2.99/1.46  #Fact    : 0
% 2.99/1.46  #Define  : 0
% 2.99/1.46  #Split   : 0
% 2.99/1.46  #Chain   : 0
% 2.99/1.46  #Close   : 0
% 2.99/1.46  
% 2.99/1.46  Ordering : KBO
% 2.99/1.46  
% 3.05/1.46  Simplification rules
% 3.05/1.46  ----------------------
% 3.05/1.46  #Subsume      : 0
% 3.05/1.46  #Demod        : 99
% 3.05/1.46  #Tautology    : 87
% 3.05/1.46  #SimpNegUnit  : 0
% 3.05/1.46  #BackRed      : 3
% 3.05/1.46  
% 3.05/1.46  #Partial instantiations: 0
% 3.05/1.46  #Strategies tried      : 1
% 3.05/1.46  
% 3.05/1.46  Timing (in seconds)
% 3.05/1.46  ----------------------
% 3.05/1.46  Preprocessing        : 0.24
% 3.05/1.46  Parsing              : 0.14
% 3.05/1.46  CNF conversion       : 0.02
% 3.05/1.46  Main loop            : 0.38
% 3.05/1.46  Inferencing          : 0.17
% 3.05/1.46  Reduction            : 0.13
% 3.05/1.46  Demodulation         : 0.11
% 3.05/1.46  BG Simplification    : 0.03
% 3.05/1.46  Subsumption          : 0.04
% 3.05/1.46  Abstraction          : 0.03
% 3.05/1.46  MUC search           : 0.00
% 3.05/1.46  Cooper               : 0.00
% 3.05/1.46  Total                : 0.66
% 3.05/1.47  Index Insertion      : 0.00
% 3.05/1.47  Index Deletion       : 0.00
% 3.05/1.47  Index Matching       : 0.00
% 3.05/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
