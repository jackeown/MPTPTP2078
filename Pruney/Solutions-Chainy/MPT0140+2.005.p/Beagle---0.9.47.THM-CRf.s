%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:47 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   47 (  52 expanded)
%              Number of leaves         :   28 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   27 (  32 expanded)
%              Number of equality atoms :   26 (  31 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(c_6,plain,(
    ! [B_7,D_9,C_8,F_11,G_12,E_10,A_6] : k2_xboole_0(k2_enumset1(A_6,B_7,C_8,D_9),k1_enumset1(E_10,F_11,G_12)) = k5_enumset1(A_6,B_7,C_8,D_9,E_10,F_11,G_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_15,B_16,C_17] : k2_xboole_0(k1_tarski(A_15),k2_tarski(B_16,C_17)) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),k1_tarski(B_14)) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_39,plain,(
    ! [A_45,B_46,C_47] : k2_xboole_0(k2_xboole_0(A_45,B_46),C_47) = k2_xboole_0(A_45,k2_xboole_0(B_46,C_47)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_71,plain,(
    ! [A_51,B_52,C_53] : k2_xboole_0(k1_tarski(A_51),k2_xboole_0(k1_tarski(B_52),C_53)) = k2_xboole_0(k2_tarski(A_51,B_52),C_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_39])).

tff(c_92,plain,(
    ! [A_51,A_13,B_14] : k2_xboole_0(k2_tarski(A_51,A_13),k1_tarski(B_14)) = k2_xboole_0(k1_tarski(A_51),k2_tarski(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_71])).

tff(c_96,plain,(
    ! [A_51,A_13,B_14] : k2_xboole_0(k2_tarski(A_51,A_13),k1_tarski(B_14)) = k1_enumset1(A_51,A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_92])).

tff(c_236,plain,(
    ! [E_94,C_95,A_92,B_91,F_93,D_90] : k2_xboole_0(k2_enumset1(A_92,B_91,C_95,D_90),k2_tarski(E_94,F_93)) = k4_enumset1(A_92,B_91,C_95,D_90,E_94,F_93) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_357,plain,(
    ! [E_127,C_130,D_125,A_129,F_126,C_131,B_128] : k2_xboole_0(k2_enumset1(A_129,B_128,C_130,D_125),k2_xboole_0(k2_tarski(E_127,F_126),C_131)) = k2_xboole_0(k4_enumset1(A_129,B_128,C_130,D_125,E_127,F_126),C_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_2])).

tff(c_384,plain,(
    ! [A_13,C_130,B_14,D_125,A_129,A_51,B_128] : k2_xboole_0(k4_enumset1(A_129,B_128,C_130,D_125,A_51,A_13),k1_tarski(B_14)) = k2_xboole_0(k2_enumset1(A_129,B_128,C_130,D_125),k1_enumset1(A_51,A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_357])).

tff(c_388,plain,(
    ! [A_13,C_130,B_14,D_125,A_129,A_51,B_128] : k2_xboole_0(k4_enumset1(A_129,B_128,C_130,D_125,A_51,A_13),k1_tarski(B_14)) = k5_enumset1(A_129,B_128,C_130,D_125,A_51,A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_384])).

tff(c_18,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39] : k2_xboole_0(k3_enumset1(A_35,B_36,C_37,D_38,E_39),k1_tarski(F_40)) = k4_enumset1(A_35,B_36,C_37,D_38,E_39,F_40) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_218,plain,(
    ! [D_88,B_87,F_85,C_84,A_89,E_86] : k2_xboole_0(k1_tarski(A_89),k3_enumset1(B_87,C_84,D_88,E_86,F_85)) = k4_enumset1(A_89,B_87,C_84,D_88,E_86,F_85) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_439,plain,(
    ! [D_147,A_148,E_150,F_144,C_149,B_145,C_146] : k2_xboole_0(k1_tarski(A_148),k2_xboole_0(k3_enumset1(B_145,C_146,D_147,E_150,F_144),C_149)) = k2_xboole_0(k4_enumset1(A_148,B_145,C_146,D_147,E_150,F_144),C_149) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_2])).

tff(c_460,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,A_148,E_39] : k2_xboole_0(k4_enumset1(A_148,A_35,B_36,C_37,D_38,E_39),k1_tarski(F_40)) = k2_xboole_0(k1_tarski(A_148),k4_enumset1(A_35,B_36,C_37,D_38,E_39,F_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_439])).

tff(c_464,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,A_148,E_39] : k2_xboole_0(k1_tarski(A_148),k4_enumset1(A_35,B_36,C_37,D_38,E_39,F_40)) = k5_enumset1(A_148,A_35,B_36,C_37,D_38,E_39,F_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_460])).

tff(c_20,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_enumset1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:14:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.35  
% 2.52/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.35  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.52/1.35  
% 2.52/1.35  %Foreground sorts:
% 2.52/1.35  
% 2.52/1.35  
% 2.52/1.35  %Background operators:
% 2.52/1.35  
% 2.52/1.35  
% 2.52/1.35  %Foreground operators:
% 2.52/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.52/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.52/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.52/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.52/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.52/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.52/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.52/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.52/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.52/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.52/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.52/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.52/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.52/1.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.52/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.52/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.52/1.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.52/1.35  
% 2.75/1.36  tff(f_31, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 2.75/1.36  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.75/1.36  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.75/1.36  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.75/1.36  tff(f_41, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 2.75/1.36  tff(f_43, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_enumset1)).
% 2.75/1.36  tff(f_39, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 2.75/1.36  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 2.75/1.36  tff(c_6, plain, (![B_7, D_9, C_8, F_11, G_12, E_10, A_6]: (k2_xboole_0(k2_enumset1(A_6, B_7, C_8, D_9), k1_enumset1(E_10, F_11, G_12))=k5_enumset1(A_6, B_7, C_8, D_9, E_10, F_11, G_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.75/1.36  tff(c_10, plain, (![A_15, B_16, C_17]: (k2_xboole_0(k1_tarski(A_15), k2_tarski(B_16, C_17))=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.75/1.36  tff(c_8, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(B_14))=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.75/1.36  tff(c_39, plain, (![A_45, B_46, C_47]: (k2_xboole_0(k2_xboole_0(A_45, B_46), C_47)=k2_xboole_0(A_45, k2_xboole_0(B_46, C_47)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.75/1.36  tff(c_71, plain, (![A_51, B_52, C_53]: (k2_xboole_0(k1_tarski(A_51), k2_xboole_0(k1_tarski(B_52), C_53))=k2_xboole_0(k2_tarski(A_51, B_52), C_53))), inference(superposition, [status(thm), theory('equality')], [c_8, c_39])).
% 2.75/1.36  tff(c_92, plain, (![A_51, A_13, B_14]: (k2_xboole_0(k2_tarski(A_51, A_13), k1_tarski(B_14))=k2_xboole_0(k1_tarski(A_51), k2_tarski(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_71])).
% 2.75/1.36  tff(c_96, plain, (![A_51, A_13, B_14]: (k2_xboole_0(k2_tarski(A_51, A_13), k1_tarski(B_14))=k1_enumset1(A_51, A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_92])).
% 2.75/1.36  tff(c_236, plain, (![E_94, C_95, A_92, B_91, F_93, D_90]: (k2_xboole_0(k2_enumset1(A_92, B_91, C_95, D_90), k2_tarski(E_94, F_93))=k4_enumset1(A_92, B_91, C_95, D_90, E_94, F_93))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.75/1.36  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.75/1.36  tff(c_357, plain, (![E_127, C_130, D_125, A_129, F_126, C_131, B_128]: (k2_xboole_0(k2_enumset1(A_129, B_128, C_130, D_125), k2_xboole_0(k2_tarski(E_127, F_126), C_131))=k2_xboole_0(k4_enumset1(A_129, B_128, C_130, D_125, E_127, F_126), C_131))), inference(superposition, [status(thm), theory('equality')], [c_236, c_2])).
% 2.75/1.36  tff(c_384, plain, (![A_13, C_130, B_14, D_125, A_129, A_51, B_128]: (k2_xboole_0(k4_enumset1(A_129, B_128, C_130, D_125, A_51, A_13), k1_tarski(B_14))=k2_xboole_0(k2_enumset1(A_129, B_128, C_130, D_125), k1_enumset1(A_51, A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_357])).
% 2.75/1.36  tff(c_388, plain, (![A_13, C_130, B_14, D_125, A_129, A_51, B_128]: (k2_xboole_0(k4_enumset1(A_129, B_128, C_130, D_125, A_51, A_13), k1_tarski(B_14))=k5_enumset1(A_129, B_128, C_130, D_125, A_51, A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_384])).
% 2.75/1.36  tff(c_18, plain, (![A_35, F_40, B_36, C_37, D_38, E_39]: (k2_xboole_0(k3_enumset1(A_35, B_36, C_37, D_38, E_39), k1_tarski(F_40))=k4_enumset1(A_35, B_36, C_37, D_38, E_39, F_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.75/1.36  tff(c_218, plain, (![D_88, B_87, F_85, C_84, A_89, E_86]: (k2_xboole_0(k1_tarski(A_89), k3_enumset1(B_87, C_84, D_88, E_86, F_85))=k4_enumset1(A_89, B_87, C_84, D_88, E_86, F_85))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.75/1.36  tff(c_439, plain, (![D_147, A_148, E_150, F_144, C_149, B_145, C_146]: (k2_xboole_0(k1_tarski(A_148), k2_xboole_0(k3_enumset1(B_145, C_146, D_147, E_150, F_144), C_149))=k2_xboole_0(k4_enumset1(A_148, B_145, C_146, D_147, E_150, F_144), C_149))), inference(superposition, [status(thm), theory('equality')], [c_218, c_2])).
% 2.75/1.36  tff(c_460, plain, (![A_35, F_40, B_36, C_37, D_38, A_148, E_39]: (k2_xboole_0(k4_enumset1(A_148, A_35, B_36, C_37, D_38, E_39), k1_tarski(F_40))=k2_xboole_0(k1_tarski(A_148), k4_enumset1(A_35, B_36, C_37, D_38, E_39, F_40)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_439])).
% 2.75/1.36  tff(c_464, plain, (![A_35, F_40, B_36, C_37, D_38, A_148, E_39]: (k2_xboole_0(k1_tarski(A_148), k4_enumset1(A_35, B_36, C_37, D_38, E_39, F_40))=k5_enumset1(A_148, A_35, B_36, C_37, D_38, E_39, F_40))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_460])).
% 2.75/1.36  tff(c_20, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.75/1.36  tff(c_467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_464, c_20])).
% 2.75/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.36  
% 2.75/1.36  Inference rules
% 2.75/1.36  ----------------------
% 2.75/1.36  #Ref     : 0
% 2.75/1.36  #Sup     : 114
% 2.75/1.36  #Fact    : 0
% 2.75/1.36  #Define  : 0
% 2.75/1.36  #Split   : 0
% 2.75/1.36  #Chain   : 0
% 2.75/1.36  #Close   : 0
% 2.75/1.36  
% 2.75/1.36  Ordering : KBO
% 2.75/1.36  
% 2.75/1.36  Simplification rules
% 2.75/1.36  ----------------------
% 2.75/1.36  #Subsume      : 0
% 2.75/1.36  #Demod        : 66
% 2.75/1.36  #Tautology    : 66
% 2.75/1.36  #SimpNegUnit  : 0
% 2.75/1.36  #BackRed      : 1
% 2.75/1.36  
% 2.75/1.36  #Partial instantiations: 0
% 2.75/1.36  #Strategies tried      : 1
% 2.75/1.36  
% 2.75/1.36  Timing (in seconds)
% 2.75/1.36  ----------------------
% 2.75/1.37  Preprocessing        : 0.29
% 2.75/1.37  Parsing              : 0.16
% 2.75/1.37  CNF conversion       : 0.02
% 2.75/1.37  Main loop            : 0.31
% 2.75/1.37  Inferencing          : 0.14
% 2.75/1.37  Reduction            : 0.10
% 2.75/1.37  Demodulation         : 0.09
% 2.75/1.37  BG Simplification    : 0.02
% 2.75/1.37  Subsumption          : 0.04
% 2.75/1.37  Abstraction          : 0.02
% 2.75/1.37  MUC search           : 0.00
% 2.75/1.37  Cooper               : 0.00
% 2.75/1.37  Total                : 0.63
% 2.75/1.37  Index Insertion      : 0.00
% 2.75/1.37  Index Deletion       : 0.00
% 2.75/1.37  Index Matching       : 0.00
% 2.75/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
