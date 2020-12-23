%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:43 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   49 (  75 expanded)
%              Number of leaves         :   23 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   33 (  59 expanded)
%              Number of equality atoms :   32 (  58 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(c_4,plain,(
    ! [B_5,D_7,A_4,E_8,C_6,F_9] : k2_xboole_0(k1_enumset1(A_4,B_5,C_6),k1_enumset1(D_7,E_8,F_9)) = k4_enumset1(A_4,B_5,C_6,D_7,E_8,F_9) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_12,B_13,C_14] : k2_xboole_0(k1_tarski(A_12),k2_tarski(B_13,C_14)) = k1_enumset1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_15,B_16,C_17,D_18] : k2_xboole_0(k1_tarski(A_15),k1_enumset1(B_16,C_17,D_18)) = k2_enumset1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_10,B_11] : k2_xboole_0(k1_tarski(A_10),k1_tarski(B_11)) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33,plain,(
    ! [A_29,B_30,C_31] : k2_xboole_0(k2_xboole_0(A_29,B_30),C_31) = k2_xboole_0(A_29,k2_xboole_0(B_30,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    ! [A_36,B_37,C_38] : k2_xboole_0(k1_tarski(A_36),k2_xboole_0(k1_tarski(B_37),C_38)) = k2_xboole_0(k2_tarski(A_36,B_37),C_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_33])).

tff(c_92,plain,(
    ! [A_36,A_10,B_11] : k2_xboole_0(k2_tarski(A_36,A_10),k1_tarski(B_11)) = k2_xboole_0(k1_tarski(A_36),k2_tarski(A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_68])).

tff(c_97,plain,(
    ! [A_36,A_10,B_11] : k2_xboole_0(k2_tarski(A_36,A_10),k1_tarski(B_11)) = k1_enumset1(A_36,A_10,B_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_92])).

tff(c_137,plain,(
    ! [A_51,B_52,C_53,C_54] : k2_xboole_0(k1_tarski(A_51),k2_xboole_0(k2_tarski(B_52,C_53),C_54)) = k2_xboole_0(k1_enumset1(A_51,B_52,C_53),C_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_33])).

tff(c_155,plain,(
    ! [A_51,A_36,A_10,B_11] : k2_xboole_0(k1_enumset1(A_51,A_36,A_10),k1_tarski(B_11)) = k2_xboole_0(k1_tarski(A_51),k1_enumset1(A_36,A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_137])).

tff(c_161,plain,(
    ! [A_55,A_56,A_57,B_58] : k2_xboole_0(k1_enumset1(A_55,A_56,A_57),k1_tarski(B_58)) = k2_enumset1(A_55,A_56,A_57,B_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_155])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_327,plain,(
    ! [A_98,A_95,C_96,B_94,A_97] : k2_xboole_0(k1_enumset1(A_95,A_97,A_98),k2_xboole_0(k1_tarski(B_94),C_96)) = k2_xboole_0(k2_enumset1(A_95,A_97,A_98,B_94),C_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_2])).

tff(c_357,plain,(
    ! [A_98,A_95,C_14,A_12,B_13,A_97] : k2_xboole_0(k2_enumset1(A_95,A_97,A_98,A_12),k2_tarski(B_13,C_14)) = k2_xboole_0(k1_enumset1(A_95,A_97,A_98),k1_enumset1(A_12,B_13,C_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_327])).

tff(c_364,plain,(
    ! [A_98,A_95,C_14,A_12,B_13,A_97] : k2_xboole_0(k2_enumset1(A_95,A_97,A_98,A_12),k2_tarski(B_13,C_14)) = k4_enumset1(A_95,A_97,A_98,A_12,B_13,C_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_357])).

tff(c_12,plain,(
    ! [A_19,C_21,D_22,B_20,E_23] : k2_xboole_0(k1_tarski(A_19),k2_enumset1(B_20,C_21,D_22,E_23)) = k3_enumset1(A_19,B_20,C_21,D_22,E_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_89,plain,(
    ! [A_36,A_12,B_13,C_14] : k2_xboole_0(k2_tarski(A_36,A_12),k2_tarski(B_13,C_14)) = k2_xboole_0(k1_tarski(A_36),k1_enumset1(A_12,B_13,C_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_68])).

tff(c_96,plain,(
    ! [A_36,A_12,B_13,C_14] : k2_xboole_0(k2_tarski(A_36,A_12),k2_tarski(B_13,C_14)) = k2_enumset1(A_36,A_12,B_13,C_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_89])).

tff(c_152,plain,(
    ! [A_36,C_14,A_12,B_13,A_51] : k2_xboole_0(k1_enumset1(A_51,A_36,A_12),k2_tarski(B_13,C_14)) = k2_xboole_0(k1_tarski(A_51),k2_enumset1(A_36,A_12,B_13,C_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_137])).

tff(c_159,plain,(
    ! [A_36,C_14,A_12,B_13,A_51] : k2_xboole_0(k1_enumset1(A_51,A_36,A_12),k2_tarski(B_13,C_14)) = k3_enumset1(A_51,A_36,A_12,B_13,C_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_152])).

tff(c_56,plain,(
    ! [A_32,B_33,C_34,D_35] : k2_xboole_0(k1_tarski(A_32),k1_enumset1(B_33,C_34,D_35)) = k2_enumset1(A_32,B_33,C_34,D_35) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_248,plain,(
    ! [C_80,A_81,B_79,C_83,D_82] : k2_xboole_0(k1_tarski(A_81),k2_xboole_0(k1_enumset1(B_79,C_80,D_82),C_83)) = k2_xboole_0(k2_enumset1(A_81,B_79,C_80,D_82),C_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2])).

tff(c_269,plain,(
    ! [A_36,A_81,C_14,A_12,B_13,A_51] : k2_xboole_0(k2_enumset1(A_81,A_51,A_36,A_12),k2_tarski(B_13,C_14)) = k2_xboole_0(k1_tarski(A_81),k3_enumset1(A_51,A_36,A_12,B_13,C_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_248])).

tff(c_463,plain,(
    ! [A_36,A_81,C_14,A_12,B_13,A_51] : k2_xboole_0(k1_tarski(A_81),k3_enumset1(A_51,A_36,A_12,B_13,C_14)) = k4_enumset1(A_81,A_51,A_36,A_12,B_13,C_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_269])).

tff(c_14,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k3_enumset1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.53  
% 2.82/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.53  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.82/1.53  
% 2.82/1.53  %Foreground sorts:
% 2.82/1.53  
% 2.82/1.53  
% 2.82/1.53  %Background operators:
% 2.82/1.53  
% 2.82/1.53  
% 2.82/1.53  %Foreground operators:
% 2.82/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.82/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.82/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.82/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.82/1.53  tff('#skF_5', type, '#skF_5': $i).
% 2.82/1.53  tff('#skF_6', type, '#skF_6': $i).
% 2.82/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.82/1.53  tff('#skF_2', type, '#skF_2': $i).
% 2.82/1.53  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.53  tff('#skF_1', type, '#skF_1': $i).
% 2.82/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.82/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.53  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.82/1.53  
% 2.82/1.55  tff(f_29, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 2.82/1.55  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.82/1.55  tff(f_35, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 2.82/1.55  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.82/1.55  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.82/1.55  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 2.82/1.55  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 2.82/1.55  tff(c_4, plain, (![B_5, D_7, A_4, E_8, C_6, F_9]: (k2_xboole_0(k1_enumset1(A_4, B_5, C_6), k1_enumset1(D_7, E_8, F_9))=k4_enumset1(A_4, B_5, C_6, D_7, E_8, F_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.82/1.55  tff(c_8, plain, (![A_12, B_13, C_14]: (k2_xboole_0(k1_tarski(A_12), k2_tarski(B_13, C_14))=k1_enumset1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.82/1.55  tff(c_10, plain, (![A_15, B_16, C_17, D_18]: (k2_xboole_0(k1_tarski(A_15), k1_enumset1(B_16, C_17, D_18))=k2_enumset1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.82/1.55  tff(c_6, plain, (![A_10, B_11]: (k2_xboole_0(k1_tarski(A_10), k1_tarski(B_11))=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.82/1.55  tff(c_33, plain, (![A_29, B_30, C_31]: (k2_xboole_0(k2_xboole_0(A_29, B_30), C_31)=k2_xboole_0(A_29, k2_xboole_0(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.82/1.55  tff(c_68, plain, (![A_36, B_37, C_38]: (k2_xboole_0(k1_tarski(A_36), k2_xboole_0(k1_tarski(B_37), C_38))=k2_xboole_0(k2_tarski(A_36, B_37), C_38))), inference(superposition, [status(thm), theory('equality')], [c_6, c_33])).
% 2.82/1.55  tff(c_92, plain, (![A_36, A_10, B_11]: (k2_xboole_0(k2_tarski(A_36, A_10), k1_tarski(B_11))=k2_xboole_0(k1_tarski(A_36), k2_tarski(A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_68])).
% 2.82/1.55  tff(c_97, plain, (![A_36, A_10, B_11]: (k2_xboole_0(k2_tarski(A_36, A_10), k1_tarski(B_11))=k1_enumset1(A_36, A_10, B_11))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_92])).
% 2.82/1.55  tff(c_137, plain, (![A_51, B_52, C_53, C_54]: (k2_xboole_0(k1_tarski(A_51), k2_xboole_0(k2_tarski(B_52, C_53), C_54))=k2_xboole_0(k1_enumset1(A_51, B_52, C_53), C_54))), inference(superposition, [status(thm), theory('equality')], [c_8, c_33])).
% 2.82/1.55  tff(c_155, plain, (![A_51, A_36, A_10, B_11]: (k2_xboole_0(k1_enumset1(A_51, A_36, A_10), k1_tarski(B_11))=k2_xboole_0(k1_tarski(A_51), k1_enumset1(A_36, A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_137])).
% 2.82/1.55  tff(c_161, plain, (![A_55, A_56, A_57, B_58]: (k2_xboole_0(k1_enumset1(A_55, A_56, A_57), k1_tarski(B_58))=k2_enumset1(A_55, A_56, A_57, B_58))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_155])).
% 2.82/1.55  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.82/1.55  tff(c_327, plain, (![A_98, A_95, C_96, B_94, A_97]: (k2_xboole_0(k1_enumset1(A_95, A_97, A_98), k2_xboole_0(k1_tarski(B_94), C_96))=k2_xboole_0(k2_enumset1(A_95, A_97, A_98, B_94), C_96))), inference(superposition, [status(thm), theory('equality')], [c_161, c_2])).
% 2.82/1.55  tff(c_357, plain, (![A_98, A_95, C_14, A_12, B_13, A_97]: (k2_xboole_0(k2_enumset1(A_95, A_97, A_98, A_12), k2_tarski(B_13, C_14))=k2_xboole_0(k1_enumset1(A_95, A_97, A_98), k1_enumset1(A_12, B_13, C_14)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_327])).
% 2.82/1.55  tff(c_364, plain, (![A_98, A_95, C_14, A_12, B_13, A_97]: (k2_xboole_0(k2_enumset1(A_95, A_97, A_98, A_12), k2_tarski(B_13, C_14))=k4_enumset1(A_95, A_97, A_98, A_12, B_13, C_14))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_357])).
% 2.82/1.55  tff(c_12, plain, (![A_19, C_21, D_22, B_20, E_23]: (k2_xboole_0(k1_tarski(A_19), k2_enumset1(B_20, C_21, D_22, E_23))=k3_enumset1(A_19, B_20, C_21, D_22, E_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.82/1.55  tff(c_89, plain, (![A_36, A_12, B_13, C_14]: (k2_xboole_0(k2_tarski(A_36, A_12), k2_tarski(B_13, C_14))=k2_xboole_0(k1_tarski(A_36), k1_enumset1(A_12, B_13, C_14)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_68])).
% 2.82/1.55  tff(c_96, plain, (![A_36, A_12, B_13, C_14]: (k2_xboole_0(k2_tarski(A_36, A_12), k2_tarski(B_13, C_14))=k2_enumset1(A_36, A_12, B_13, C_14))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_89])).
% 2.82/1.55  tff(c_152, plain, (![A_36, C_14, A_12, B_13, A_51]: (k2_xboole_0(k1_enumset1(A_51, A_36, A_12), k2_tarski(B_13, C_14))=k2_xboole_0(k1_tarski(A_51), k2_enumset1(A_36, A_12, B_13, C_14)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_137])).
% 2.82/1.55  tff(c_159, plain, (![A_36, C_14, A_12, B_13, A_51]: (k2_xboole_0(k1_enumset1(A_51, A_36, A_12), k2_tarski(B_13, C_14))=k3_enumset1(A_51, A_36, A_12, B_13, C_14))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_152])).
% 2.82/1.55  tff(c_56, plain, (![A_32, B_33, C_34, D_35]: (k2_xboole_0(k1_tarski(A_32), k1_enumset1(B_33, C_34, D_35))=k2_enumset1(A_32, B_33, C_34, D_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.82/1.55  tff(c_248, plain, (![C_80, A_81, B_79, C_83, D_82]: (k2_xboole_0(k1_tarski(A_81), k2_xboole_0(k1_enumset1(B_79, C_80, D_82), C_83))=k2_xboole_0(k2_enumset1(A_81, B_79, C_80, D_82), C_83))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2])).
% 2.82/1.55  tff(c_269, plain, (![A_36, A_81, C_14, A_12, B_13, A_51]: (k2_xboole_0(k2_enumset1(A_81, A_51, A_36, A_12), k2_tarski(B_13, C_14))=k2_xboole_0(k1_tarski(A_81), k3_enumset1(A_51, A_36, A_12, B_13, C_14)))), inference(superposition, [status(thm), theory('equality')], [c_159, c_248])).
% 2.82/1.55  tff(c_463, plain, (![A_36, A_81, C_14, A_12, B_13, A_51]: (k2_xboole_0(k1_tarski(A_81), k3_enumset1(A_51, A_36, A_12, B_13, C_14))=k4_enumset1(A_81, A_51, A_36, A_12, B_13, C_14))), inference(demodulation, [status(thm), theory('equality')], [c_364, c_269])).
% 2.82/1.55  tff(c_14, plain, (k2_xboole_0(k1_tarski('#skF_1'), k3_enumset1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.82/1.55  tff(c_467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_463, c_14])).
% 2.82/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.55  
% 2.82/1.55  Inference rules
% 2.82/1.55  ----------------------
% 2.82/1.55  #Ref     : 0
% 2.82/1.55  #Sup     : 118
% 2.82/1.55  #Fact    : 0
% 2.82/1.55  #Define  : 0
% 2.82/1.55  #Split   : 0
% 2.82/1.55  #Chain   : 0
% 2.82/1.55  #Close   : 0
% 2.82/1.55  
% 2.82/1.55  Ordering : KBO
% 2.82/1.55  
% 2.82/1.55  Simplification rules
% 2.82/1.55  ----------------------
% 2.82/1.55  #Subsume      : 0
% 2.82/1.55  #Demod        : 59
% 2.82/1.55  #Tautology    : 62
% 2.82/1.55  #SimpNegUnit  : 0
% 2.82/1.55  #BackRed      : 2
% 2.82/1.55  
% 2.82/1.55  #Partial instantiations: 0
% 2.82/1.55  #Strategies tried      : 1
% 2.82/1.55  
% 2.82/1.55  Timing (in seconds)
% 2.82/1.55  ----------------------
% 2.82/1.55  Preprocessing        : 0.36
% 2.82/1.55  Parsing              : 0.20
% 2.82/1.55  CNF conversion       : 0.02
% 2.82/1.55  Main loop            : 0.36
% 2.82/1.55  Inferencing          : 0.17
% 2.82/1.55  Reduction            : 0.11
% 2.82/1.55  Demodulation         : 0.09
% 2.82/1.55  BG Simplification    : 0.03
% 2.82/1.55  Subsumption          : 0.04
% 2.82/1.55  Abstraction          : 0.03
% 2.82/1.55  MUC search           : 0.00
% 2.82/1.55  Cooper               : 0.00
% 2.82/1.55  Total                : 0.75
% 2.82/1.55  Index Insertion      : 0.00
% 2.82/1.55  Index Deletion       : 0.00
% 2.82/1.55  Index Matching       : 0.00
% 2.82/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
