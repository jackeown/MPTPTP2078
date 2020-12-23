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
% DateTime   : Thu Dec  3 09:45:48 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   48 (  76 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   31 (  59 expanded)
%              Number of equality atoms :   30 (  58 expanded)
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

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_tarski(A,B),k3_enumset1(C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

tff(c_4,plain,(
    ! [B_5,D_7,A_4,G_10,E_8,C_6,F_9] : k2_xboole_0(k2_enumset1(A_4,B_5,C_6,D_7),k1_enumset1(E_8,F_9,G_10)) = k5_enumset1(A_4,B_5,C_6,D_7,E_8,F_9,G_10) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [C_22,D_23,A_20,B_21,E_24] : k2_xboole_0(k1_tarski(A_20),k2_enumset1(B_21,C_22,D_23,E_24)) = k3_enumset1(A_20,B_21,C_22,D_23,E_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_16,B_17,C_18,D_19] : k2_xboole_0(k1_tarski(A_16),k1_enumset1(B_17,C_18,D_19)) = k2_enumset1(A_16,B_17,C_18,D_19) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k1_tarski(A_13),k2_tarski(B_14,C_15)) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),k1_tarski(B_12)) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33,plain,(
    ! [A_30,B_31,C_32] : k2_xboole_0(k2_xboole_0(A_30,B_31),C_32) = k2_xboole_0(A_30,k2_xboole_0(B_31,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    ! [A_37,B_38,C_39] : k2_xboole_0(k1_tarski(A_37),k2_xboole_0(k1_tarski(B_38),C_39)) = k2_xboole_0(k2_tarski(A_37,B_38),C_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_33])).

tff(c_89,plain,(
    ! [A_37,A_13,B_14,C_15] : k2_xboole_0(k2_tarski(A_37,A_13),k2_tarski(B_14,C_15)) = k2_xboole_0(k1_tarski(A_37),k1_enumset1(A_13,B_14,C_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_68])).

tff(c_96,plain,(
    ! [A_37,A_13,B_14,C_15] : k2_xboole_0(k2_tarski(A_37,A_13),k2_tarski(B_14,C_15)) = k2_enumset1(A_37,A_13,B_14,C_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_89])).

tff(c_137,plain,(
    ! [A_52,B_53,C_54,C_55] : k2_xboole_0(k1_tarski(A_52),k2_xboole_0(k2_tarski(B_53,C_54),C_55)) = k2_xboole_0(k1_enumset1(A_52,B_53,C_54),C_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_33])).

tff(c_152,plain,(
    ! [A_13,A_37,B_14,C_15,A_52] : k2_xboole_0(k1_enumset1(A_52,A_37,A_13),k2_tarski(B_14,C_15)) = k2_xboole_0(k1_tarski(A_52),k2_enumset1(A_37,A_13,B_14,C_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_137])).

tff(c_159,plain,(
    ! [A_13,A_37,B_14,C_15,A_52] : k2_xboole_0(k1_enumset1(A_52,A_37,A_13),k2_tarski(B_14,C_15)) = k3_enumset1(A_52,A_37,A_13,B_14,C_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_152])).

tff(c_92,plain,(
    ! [A_37,A_11,B_12] : k2_xboole_0(k2_tarski(A_37,A_11),k1_tarski(B_12)) = k2_xboole_0(k1_tarski(A_37),k2_tarski(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_68])).

tff(c_113,plain,(
    ! [A_45,A_46,B_47] : k2_xboole_0(k2_tarski(A_45,A_46),k1_tarski(B_47)) = k1_enumset1(A_45,A_46,B_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_92])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_185,plain,(
    ! [A_65,A_66,B_67,C_68] : k2_xboole_0(k2_tarski(A_65,A_66),k2_xboole_0(k1_tarski(B_67),C_68)) = k2_xboole_0(k1_enumset1(A_65,A_66,B_67),C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_2])).

tff(c_212,plain,(
    ! [A_65,A_66,A_13,B_14,C_15] : k2_xboole_0(k1_enumset1(A_65,A_66,A_13),k2_tarski(B_14,C_15)) = k2_xboole_0(k2_tarski(A_65,A_66),k1_enumset1(A_13,B_14,C_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_185])).

tff(c_219,plain,(
    ! [A_65,A_66,A_13,B_14,C_15] : k2_xboole_0(k2_tarski(A_65,A_66),k1_enumset1(A_13,B_14,C_15)) = k3_enumset1(A_65,A_66,A_13,B_14,C_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_212])).

tff(c_125,plain,(
    ! [A_48,A_49,B_50,C_51] : k2_xboole_0(k2_tarski(A_48,A_49),k2_tarski(B_50,C_51)) = k2_enumset1(A_48,A_49,B_50,C_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_89])).

tff(c_288,plain,(
    ! [C_95,B_92,C_91,A_93,A_94] : k2_xboole_0(k2_tarski(A_93,A_94),k2_xboole_0(k2_tarski(B_92,C_91),C_95)) = k2_xboole_0(k2_enumset1(A_93,A_94,B_92,C_91),C_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_2])).

tff(c_309,plain,(
    ! [A_65,A_66,A_13,B_14,C_15,A_93,A_94] : k2_xboole_0(k2_enumset1(A_93,A_94,A_65,A_66),k1_enumset1(A_13,B_14,C_15)) = k2_xboole_0(k2_tarski(A_93,A_94),k3_enumset1(A_65,A_66,A_13,B_14,C_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_288])).

tff(c_322,plain,(
    ! [A_65,A_66,A_13,B_14,C_15,A_93,A_94] : k2_xboole_0(k2_tarski(A_93,A_94),k3_enumset1(A_65,A_66,A_13,B_14,C_15)) = k5_enumset1(A_93,A_94,A_65,A_66,A_13,B_14,C_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_309])).

tff(c_14,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k3_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_619,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:48:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.38  
% 2.57/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.38  %$ k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.57/1.38  
% 2.57/1.38  %Foreground sorts:
% 2.57/1.38  
% 2.57/1.38  
% 2.57/1.38  %Background operators:
% 2.57/1.38  
% 2.57/1.38  
% 2.57/1.38  %Foreground operators:
% 2.57/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.57/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.57/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.57/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.57/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.57/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.57/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.57/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.57/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.57/1.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.57/1.38  
% 2.88/1.40  tff(f_29, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_enumset1)).
% 2.88/1.40  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 2.88/1.40  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 2.88/1.40  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.88/1.40  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.88/1.40  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.88/1.40  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_tarski(A, B), k3_enumset1(C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_enumset1)).
% 2.88/1.40  tff(c_4, plain, (![B_5, D_7, A_4, G_10, E_8, C_6, F_9]: (k2_xboole_0(k2_enumset1(A_4, B_5, C_6, D_7), k1_enumset1(E_8, F_9, G_10))=k5_enumset1(A_4, B_5, C_6, D_7, E_8, F_9, G_10))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.88/1.40  tff(c_12, plain, (![C_22, D_23, A_20, B_21, E_24]: (k2_xboole_0(k1_tarski(A_20), k2_enumset1(B_21, C_22, D_23, E_24))=k3_enumset1(A_20, B_21, C_22, D_23, E_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.88/1.40  tff(c_10, plain, (![A_16, B_17, C_18, D_19]: (k2_xboole_0(k1_tarski(A_16), k1_enumset1(B_17, C_18, D_19))=k2_enumset1(A_16, B_17, C_18, D_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.88/1.40  tff(c_8, plain, (![A_13, B_14, C_15]: (k2_xboole_0(k1_tarski(A_13), k2_tarski(B_14, C_15))=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.88/1.40  tff(c_6, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), k1_tarski(B_12))=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.88/1.40  tff(c_33, plain, (![A_30, B_31, C_32]: (k2_xboole_0(k2_xboole_0(A_30, B_31), C_32)=k2_xboole_0(A_30, k2_xboole_0(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.88/1.40  tff(c_68, plain, (![A_37, B_38, C_39]: (k2_xboole_0(k1_tarski(A_37), k2_xboole_0(k1_tarski(B_38), C_39))=k2_xboole_0(k2_tarski(A_37, B_38), C_39))), inference(superposition, [status(thm), theory('equality')], [c_6, c_33])).
% 2.88/1.40  tff(c_89, plain, (![A_37, A_13, B_14, C_15]: (k2_xboole_0(k2_tarski(A_37, A_13), k2_tarski(B_14, C_15))=k2_xboole_0(k1_tarski(A_37), k1_enumset1(A_13, B_14, C_15)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_68])).
% 2.88/1.40  tff(c_96, plain, (![A_37, A_13, B_14, C_15]: (k2_xboole_0(k2_tarski(A_37, A_13), k2_tarski(B_14, C_15))=k2_enumset1(A_37, A_13, B_14, C_15))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_89])).
% 2.88/1.40  tff(c_137, plain, (![A_52, B_53, C_54, C_55]: (k2_xboole_0(k1_tarski(A_52), k2_xboole_0(k2_tarski(B_53, C_54), C_55))=k2_xboole_0(k1_enumset1(A_52, B_53, C_54), C_55))), inference(superposition, [status(thm), theory('equality')], [c_8, c_33])).
% 2.88/1.40  tff(c_152, plain, (![A_13, A_37, B_14, C_15, A_52]: (k2_xboole_0(k1_enumset1(A_52, A_37, A_13), k2_tarski(B_14, C_15))=k2_xboole_0(k1_tarski(A_52), k2_enumset1(A_37, A_13, B_14, C_15)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_137])).
% 2.88/1.40  tff(c_159, plain, (![A_13, A_37, B_14, C_15, A_52]: (k2_xboole_0(k1_enumset1(A_52, A_37, A_13), k2_tarski(B_14, C_15))=k3_enumset1(A_52, A_37, A_13, B_14, C_15))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_152])).
% 2.88/1.40  tff(c_92, plain, (![A_37, A_11, B_12]: (k2_xboole_0(k2_tarski(A_37, A_11), k1_tarski(B_12))=k2_xboole_0(k1_tarski(A_37), k2_tarski(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_68])).
% 2.88/1.40  tff(c_113, plain, (![A_45, A_46, B_47]: (k2_xboole_0(k2_tarski(A_45, A_46), k1_tarski(B_47))=k1_enumset1(A_45, A_46, B_47))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_92])).
% 2.88/1.40  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.88/1.40  tff(c_185, plain, (![A_65, A_66, B_67, C_68]: (k2_xboole_0(k2_tarski(A_65, A_66), k2_xboole_0(k1_tarski(B_67), C_68))=k2_xboole_0(k1_enumset1(A_65, A_66, B_67), C_68))), inference(superposition, [status(thm), theory('equality')], [c_113, c_2])).
% 2.88/1.40  tff(c_212, plain, (![A_65, A_66, A_13, B_14, C_15]: (k2_xboole_0(k1_enumset1(A_65, A_66, A_13), k2_tarski(B_14, C_15))=k2_xboole_0(k2_tarski(A_65, A_66), k1_enumset1(A_13, B_14, C_15)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_185])).
% 2.88/1.40  tff(c_219, plain, (![A_65, A_66, A_13, B_14, C_15]: (k2_xboole_0(k2_tarski(A_65, A_66), k1_enumset1(A_13, B_14, C_15))=k3_enumset1(A_65, A_66, A_13, B_14, C_15))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_212])).
% 2.88/1.40  tff(c_125, plain, (![A_48, A_49, B_50, C_51]: (k2_xboole_0(k2_tarski(A_48, A_49), k2_tarski(B_50, C_51))=k2_enumset1(A_48, A_49, B_50, C_51))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_89])).
% 2.88/1.40  tff(c_288, plain, (![C_95, B_92, C_91, A_93, A_94]: (k2_xboole_0(k2_tarski(A_93, A_94), k2_xboole_0(k2_tarski(B_92, C_91), C_95))=k2_xboole_0(k2_enumset1(A_93, A_94, B_92, C_91), C_95))), inference(superposition, [status(thm), theory('equality')], [c_125, c_2])).
% 2.88/1.40  tff(c_309, plain, (![A_65, A_66, A_13, B_14, C_15, A_93, A_94]: (k2_xboole_0(k2_enumset1(A_93, A_94, A_65, A_66), k1_enumset1(A_13, B_14, C_15))=k2_xboole_0(k2_tarski(A_93, A_94), k3_enumset1(A_65, A_66, A_13, B_14, C_15)))), inference(superposition, [status(thm), theory('equality')], [c_219, c_288])).
% 2.88/1.40  tff(c_322, plain, (![A_65, A_66, A_13, B_14, C_15, A_93, A_94]: (k2_xboole_0(k2_tarski(A_93, A_94), k3_enumset1(A_65, A_66, A_13, B_14, C_15))=k5_enumset1(A_93, A_94, A_65, A_66, A_13, B_14, C_15))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_309])).
% 2.88/1.40  tff(c_14, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k3_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.88/1.40  tff(c_619, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_322, c_14])).
% 2.88/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.40  
% 2.88/1.40  Inference rules
% 2.88/1.40  ----------------------
% 2.88/1.40  #Ref     : 0
% 2.88/1.40  #Sup     : 157
% 2.88/1.40  #Fact    : 0
% 2.88/1.40  #Define  : 0
% 2.88/1.40  #Split   : 0
% 2.88/1.40  #Chain   : 0
% 2.88/1.40  #Close   : 0
% 2.88/1.40  
% 2.88/1.40  Ordering : KBO
% 2.88/1.40  
% 2.88/1.40  Simplification rules
% 2.88/1.40  ----------------------
% 2.88/1.40  #Subsume      : 0
% 2.88/1.40  #Demod        : 90
% 2.88/1.40  #Tautology    : 79
% 2.88/1.40  #SimpNegUnit  : 0
% 2.88/1.40  #BackRed      : 1
% 2.88/1.40  
% 2.88/1.40  #Partial instantiations: 0
% 2.88/1.40  #Strategies tried      : 1
% 2.88/1.40  
% 2.88/1.40  Timing (in seconds)
% 2.88/1.40  ----------------------
% 2.88/1.40  Preprocessing        : 0.27
% 2.88/1.40  Parsing              : 0.15
% 2.88/1.40  CNF conversion       : 0.02
% 2.88/1.40  Main loop            : 0.37
% 2.88/1.40  Inferencing          : 0.16
% 2.88/1.40  Reduction            : 0.13
% 2.88/1.40  Demodulation         : 0.10
% 2.88/1.40  BG Simplification    : 0.03
% 2.88/1.40  Subsumption          : 0.04
% 2.88/1.40  Abstraction          : 0.03
% 2.88/1.40  MUC search           : 0.00
% 2.88/1.40  Cooper               : 0.00
% 2.88/1.40  Total                : 0.67
% 2.88/1.40  Index Insertion      : 0.00
% 2.88/1.40  Index Deletion       : 0.00
% 2.88/1.40  Index Matching       : 0.00
% 2.88/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
