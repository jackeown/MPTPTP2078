%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:56 EST 2020

% Result     : Theorem 4.26s
% Output     : CNFRefutation 4.26s
% Verified   : 
% Statistics : Number of formulae       :   49 (  54 expanded)
%              Number of leaves         :   30 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   27 (  32 expanded)
%              Number of equality atoms :   26 (  31 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

tff(c_10,plain,(
    ! [H_20,E_17,F_18,A_13,B_14,C_15,G_19,D_16] : k2_xboole_0(k2_enumset1(A_13,B_14,C_15,D_16),k2_enumset1(E_17,F_18,G_19,H_20)) = k6_enumset1(A_13,B_14,C_15,D_16,E_17,F_18,G_19,H_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39] : k2_xboole_0(k1_tarski(A_35),k3_enumset1(B_36,C_37,D_38,E_39,F_40)) = k4_enumset1(A_35,B_36,C_37,D_38,E_39,F_40) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_198,plain,(
    ! [A_81,C_79,B_80,D_83,E_82] : k2_xboole_0(k1_tarski(A_81),k2_enumset1(B_80,C_79,D_83,E_82)) = k3_enumset1(A_81,B_80,C_79,D_83,E_82) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_21,B_22] : k2_xboole_0(k1_tarski(A_21),k1_tarski(B_22)) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_64,plain,(
    ! [A_56,B_57,C_58] : k2_xboole_0(k2_xboole_0(A_56,B_57),C_58) = k2_xboole_0(A_56,k2_xboole_0(B_57,C_58)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [A_21,B_22,C_58] : k2_xboole_0(k1_tarski(A_21),k2_xboole_0(k1_tarski(B_22),C_58)) = k2_xboole_0(k2_tarski(A_21,B_22),C_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_64])).

tff(c_207,plain,(
    ! [A_21,A_81,C_79,B_80,D_83,E_82] : k2_xboole_0(k2_tarski(A_21,A_81),k2_enumset1(B_80,C_79,D_83,E_82)) = k2_xboole_0(k1_tarski(A_21),k3_enumset1(A_81,B_80,C_79,D_83,E_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_79])).

tff(c_783,plain,(
    ! [A_187,A_188,B_190,D_189,C_191,E_192] : k2_xboole_0(k2_tarski(A_187,A_188),k2_enumset1(B_190,C_191,D_189,E_192)) = k4_enumset1(A_187,A_188,B_190,C_191,D_189,E_192) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_207])).

tff(c_16,plain,(
    ! [A_26,B_27,C_28,D_29] : k2_xboole_0(k1_tarski(A_26),k1_enumset1(B_27,C_28,D_29)) = k2_enumset1(A_26,B_27,C_28,D_29) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k1_tarski(A_23),k2_tarski(B_24,C_25)) = k1_enumset1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_108,plain,(
    ! [A_66,B_67,C_68] : k2_xboole_0(k1_tarski(A_66),k2_xboole_0(k1_tarski(B_67),C_68)) = k2_xboole_0(k2_tarski(A_66,B_67),C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_64])).

tff(c_129,plain,(
    ! [A_66,A_23,B_24,C_25] : k2_xboole_0(k2_tarski(A_66,A_23),k2_tarski(B_24,C_25)) = k2_xboole_0(k1_tarski(A_66),k1_enumset1(A_23,B_24,C_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_108])).

tff(c_183,plain,(
    ! [A_75,A_76,B_77,C_78] : k2_xboole_0(k2_tarski(A_75,A_76),k2_tarski(B_77,C_78)) = k2_enumset1(A_75,A_76,B_77,C_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_129])).

tff(c_6,plain,(
    ! [A_8,B_9,C_10] : k2_xboole_0(k2_xboole_0(A_8,B_9),C_10) = k2_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_192,plain,(
    ! [B_77,A_76,C_78,C_10,A_75] : k2_xboole_0(k2_tarski(A_75,A_76),k2_xboole_0(k2_tarski(B_77,C_78),C_10)) = k2_xboole_0(k2_enumset1(A_75,A_76,B_77,C_78),C_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_6])).

tff(c_789,plain,(
    ! [A_76,A_187,A_188,B_190,D_189,C_191,E_192,A_75] : k2_xboole_0(k2_enumset1(A_75,A_76,A_187,A_188),k2_enumset1(B_190,C_191,D_189,E_192)) = k2_xboole_0(k2_tarski(A_75,A_76),k4_enumset1(A_187,A_188,B_190,C_191,D_189,E_192)) ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_192])).

tff(c_806,plain,(
    ! [A_76,A_187,A_188,B_190,D_189,C_191,E_192,A_75] : k2_xboole_0(k2_tarski(A_75,A_76),k4_enumset1(A_187,A_188,B_190,C_191,D_189,E_192)) = k6_enumset1(A_75,A_76,A_187,A_188,B_190,C_191,D_189,E_192) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_789])).

tff(c_24,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k4_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:21:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.26/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.73  
% 4.26/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.74  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 4.26/1.74  
% 4.26/1.74  %Foreground sorts:
% 4.26/1.74  
% 4.26/1.74  
% 4.26/1.74  %Background operators:
% 4.26/1.74  
% 4.26/1.74  
% 4.26/1.74  %Foreground operators:
% 4.26/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.26/1.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.26/1.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.26/1.74  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.26/1.74  tff('#skF_7', type, '#skF_7': $i).
% 4.26/1.74  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.26/1.74  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.26/1.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.26/1.74  tff('#skF_5', type, '#skF_5': $i).
% 4.26/1.74  tff('#skF_6', type, '#skF_6': $i).
% 4.26/1.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.26/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.26/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.26/1.74  tff('#skF_1', type, '#skF_1': $i).
% 4.26/1.74  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.26/1.74  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.26/1.74  tff('#skF_8', type, '#skF_8': $i).
% 4.26/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.26/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.26/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.26/1.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.26/1.74  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.26/1.74  
% 4.26/1.75  tff(f_35, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l75_enumset1)).
% 4.26/1.75  tff(f_45, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 4.26/1.75  tff(f_43, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 4.26/1.75  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 4.26/1.75  tff(f_31, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 4.26/1.75  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 4.26/1.75  tff(f_39, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 4.26/1.75  tff(f_50, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_enumset1)).
% 4.26/1.75  tff(c_10, plain, (![H_20, E_17, F_18, A_13, B_14, C_15, G_19, D_16]: (k2_xboole_0(k2_enumset1(A_13, B_14, C_15, D_16), k2_enumset1(E_17, F_18, G_19, H_20))=k6_enumset1(A_13, B_14, C_15, D_16, E_17, F_18, G_19, H_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.26/1.75  tff(c_20, plain, (![A_35, F_40, B_36, C_37, D_38, E_39]: (k2_xboole_0(k1_tarski(A_35), k3_enumset1(B_36, C_37, D_38, E_39, F_40))=k4_enumset1(A_35, B_36, C_37, D_38, E_39, F_40))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.26/1.75  tff(c_198, plain, (![A_81, C_79, B_80, D_83, E_82]: (k2_xboole_0(k1_tarski(A_81), k2_enumset1(B_80, C_79, D_83, E_82))=k3_enumset1(A_81, B_80, C_79, D_83, E_82))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.26/1.75  tff(c_12, plain, (![A_21, B_22]: (k2_xboole_0(k1_tarski(A_21), k1_tarski(B_22))=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.26/1.75  tff(c_64, plain, (![A_56, B_57, C_58]: (k2_xboole_0(k2_xboole_0(A_56, B_57), C_58)=k2_xboole_0(A_56, k2_xboole_0(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.26/1.75  tff(c_79, plain, (![A_21, B_22, C_58]: (k2_xboole_0(k1_tarski(A_21), k2_xboole_0(k1_tarski(B_22), C_58))=k2_xboole_0(k2_tarski(A_21, B_22), C_58))), inference(superposition, [status(thm), theory('equality')], [c_12, c_64])).
% 4.26/1.75  tff(c_207, plain, (![A_21, A_81, C_79, B_80, D_83, E_82]: (k2_xboole_0(k2_tarski(A_21, A_81), k2_enumset1(B_80, C_79, D_83, E_82))=k2_xboole_0(k1_tarski(A_21), k3_enumset1(A_81, B_80, C_79, D_83, E_82)))), inference(superposition, [status(thm), theory('equality')], [c_198, c_79])).
% 4.26/1.75  tff(c_783, plain, (![A_187, A_188, B_190, D_189, C_191, E_192]: (k2_xboole_0(k2_tarski(A_187, A_188), k2_enumset1(B_190, C_191, D_189, E_192))=k4_enumset1(A_187, A_188, B_190, C_191, D_189, E_192))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_207])).
% 4.26/1.75  tff(c_16, plain, (![A_26, B_27, C_28, D_29]: (k2_xboole_0(k1_tarski(A_26), k1_enumset1(B_27, C_28, D_29))=k2_enumset1(A_26, B_27, C_28, D_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.26/1.75  tff(c_14, plain, (![A_23, B_24, C_25]: (k2_xboole_0(k1_tarski(A_23), k2_tarski(B_24, C_25))=k1_enumset1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.26/1.75  tff(c_108, plain, (![A_66, B_67, C_68]: (k2_xboole_0(k1_tarski(A_66), k2_xboole_0(k1_tarski(B_67), C_68))=k2_xboole_0(k2_tarski(A_66, B_67), C_68))), inference(superposition, [status(thm), theory('equality')], [c_12, c_64])).
% 4.26/1.75  tff(c_129, plain, (![A_66, A_23, B_24, C_25]: (k2_xboole_0(k2_tarski(A_66, A_23), k2_tarski(B_24, C_25))=k2_xboole_0(k1_tarski(A_66), k1_enumset1(A_23, B_24, C_25)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_108])).
% 4.26/1.75  tff(c_183, plain, (![A_75, A_76, B_77, C_78]: (k2_xboole_0(k2_tarski(A_75, A_76), k2_tarski(B_77, C_78))=k2_enumset1(A_75, A_76, B_77, C_78))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_129])).
% 4.26/1.75  tff(c_6, plain, (![A_8, B_9, C_10]: (k2_xboole_0(k2_xboole_0(A_8, B_9), C_10)=k2_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.26/1.75  tff(c_192, plain, (![B_77, A_76, C_78, C_10, A_75]: (k2_xboole_0(k2_tarski(A_75, A_76), k2_xboole_0(k2_tarski(B_77, C_78), C_10))=k2_xboole_0(k2_enumset1(A_75, A_76, B_77, C_78), C_10))), inference(superposition, [status(thm), theory('equality')], [c_183, c_6])).
% 4.26/1.75  tff(c_789, plain, (![A_76, A_187, A_188, B_190, D_189, C_191, E_192, A_75]: (k2_xboole_0(k2_enumset1(A_75, A_76, A_187, A_188), k2_enumset1(B_190, C_191, D_189, E_192))=k2_xboole_0(k2_tarski(A_75, A_76), k4_enumset1(A_187, A_188, B_190, C_191, D_189, E_192)))), inference(superposition, [status(thm), theory('equality')], [c_783, c_192])).
% 4.26/1.75  tff(c_806, plain, (![A_76, A_187, A_188, B_190, D_189, C_191, E_192, A_75]: (k2_xboole_0(k2_tarski(A_75, A_76), k4_enumset1(A_187, A_188, B_190, C_191, D_189, E_192))=k6_enumset1(A_75, A_76, A_187, A_188, B_190, C_191, D_189, E_192))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_789])).
% 4.26/1.75  tff(c_24, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k4_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.26/1.75  tff(c_1545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_806, c_24])).
% 4.26/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.75  
% 4.26/1.75  Inference rules
% 4.26/1.75  ----------------------
% 4.26/1.75  #Ref     : 0
% 4.26/1.75  #Sup     : 395
% 4.26/1.75  #Fact    : 0
% 4.26/1.75  #Define  : 0
% 4.26/1.75  #Split   : 0
% 4.26/1.75  #Chain   : 0
% 4.26/1.75  #Close   : 0
% 4.26/1.75  
% 4.26/1.75  Ordering : KBO
% 4.26/1.75  
% 4.26/1.75  Simplification rules
% 4.26/1.75  ----------------------
% 4.26/1.75  #Subsume      : 0
% 4.26/1.75  #Demod        : 270
% 4.26/1.75  #Tautology    : 177
% 4.26/1.75  #SimpNegUnit  : 0
% 4.26/1.75  #BackRed      : 1
% 4.26/1.75  
% 4.26/1.75  #Partial instantiations: 0
% 4.26/1.75  #Strategies tried      : 1
% 4.26/1.75  
% 4.26/1.75  Timing (in seconds)
% 4.26/1.75  ----------------------
% 4.26/1.75  Preprocessing        : 0.29
% 4.26/1.75  Parsing              : 0.16
% 4.26/1.75  CNF conversion       : 0.02
% 4.26/1.75  Main loop            : 0.70
% 4.26/1.75  Inferencing          : 0.29
% 4.26/1.75  Reduction            : 0.26
% 4.26/1.75  Demodulation         : 0.22
% 4.26/1.75  BG Simplification    : 0.05
% 4.26/1.75  Subsumption          : 0.07
% 4.26/1.75  Abstraction          : 0.07
% 4.26/1.75  MUC search           : 0.00
% 4.26/1.75  Cooper               : 0.00
% 4.26/1.75  Total                : 1.02
% 4.26/1.75  Index Insertion      : 0.00
% 4.26/1.75  Index Deletion       : 0.00
% 4.26/1.75  Index Matching       : 0.00
% 4.26/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
