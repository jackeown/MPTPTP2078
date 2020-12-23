%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:46 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   47 (  57 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :   31 (  41 expanded)
%              Number of equality atoms :   30 (  40 expanded)
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

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(c_12,plain,(
    ! [E_22,D_21,F_23,A_18,C_20,B_19] : k2_xboole_0(k1_tarski(A_18),k3_enumset1(B_19,C_20,D_21,E_22,F_23)) = k4_enumset1(A_18,B_19,C_20,D_21,E_22,F_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] : k2_xboole_0(k1_tarski(A_13),k2_enumset1(B_14,C_15,D_16,E_17)) = k3_enumset1(A_13,B_14,C_15,D_16,E_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11,D_12] : k2_xboole_0(k1_tarski(A_9),k1_enumset1(B_10,C_11,D_12)) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k2_xboole_0(k1_tarski(A_6),k2_tarski(B_7,C_8)) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),k1_tarski(B_5)) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [A_26,B_27,C_28] : k2_xboole_0(k2_xboole_0(A_26,B_27),C_28) = k2_xboole_0(A_26,k2_xboole_0(B_27,C_28)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    ! [A_36,B_37,C_38] : k2_xboole_0(k1_tarski(A_36),k2_xboole_0(k1_tarski(B_37),C_38)) = k2_xboole_0(k2_tarski(A_36,B_37),C_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_24])).

tff(c_92,plain,(
    ! [A_36,A_4,B_5] : k2_xboole_0(k2_tarski(A_36,A_4),k1_tarski(B_5)) = k2_xboole_0(k1_tarski(A_36),k2_tarski(A_4,B_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_68])).

tff(c_97,plain,(
    ! [A_36,A_4,B_5] : k2_xboole_0(k2_tarski(A_36,A_4),k1_tarski(B_5)) = k1_enumset1(A_36,A_4,B_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_92])).

tff(c_44,plain,(
    ! [A_29,B_30,C_31] : k2_xboole_0(k1_tarski(A_29),k2_tarski(B_30,C_31)) = k1_enumset1(A_29,B_30,C_31) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_137,plain,(
    ! [A_51,B_52,C_53,C_54] : k2_xboole_0(k1_tarski(A_51),k2_xboole_0(k2_tarski(B_52,C_53),C_54)) = k2_xboole_0(k1_enumset1(A_51,B_52,C_53),C_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2])).

tff(c_155,plain,(
    ! [A_51,A_36,A_4,B_5] : k2_xboole_0(k1_enumset1(A_51,A_36,A_4),k1_tarski(B_5)) = k2_xboole_0(k1_tarski(A_51),k1_enumset1(A_36,A_4,B_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_137])).

tff(c_160,plain,(
    ! [A_51,A_36,A_4,B_5] : k2_xboole_0(k1_enumset1(A_51,A_36,A_4),k1_tarski(B_5)) = k2_enumset1(A_51,A_36,A_4,B_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_155])).

tff(c_56,plain,(
    ! [A_32,B_33,C_34,D_35] : k2_xboole_0(k1_tarski(A_32),k1_enumset1(B_33,C_34,D_35)) = k2_enumset1(A_32,B_33,C_34,D_35) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_254,plain,(
    ! [C_80,A_81,B_79,C_83,D_82] : k2_xboole_0(k1_tarski(A_81),k2_xboole_0(k1_enumset1(B_79,C_80,D_82),C_83)) = k2_xboole_0(k2_enumset1(A_81,B_79,C_80,D_82),C_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2])).

tff(c_275,plain,(
    ! [B_5,A_36,A_4,A_81,A_51] : k2_xboole_0(k2_enumset1(A_81,A_51,A_36,A_4),k1_tarski(B_5)) = k2_xboole_0(k1_tarski(A_81),k2_enumset1(A_51,A_36,A_4,B_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_254])).

tff(c_280,plain,(
    ! [B_5,A_36,A_4,A_81,A_51] : k2_xboole_0(k2_enumset1(A_81,A_51,A_36,A_4),k1_tarski(B_5)) = k3_enumset1(A_81,A_51,A_36,A_4,B_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_275])).

tff(c_98,plain,(
    ! [D_39,A_42,C_43,E_41,B_40] : k2_xboole_0(k1_tarski(A_42),k2_enumset1(B_40,C_43,D_39,E_41)) = k3_enumset1(A_42,B_40,C_43,D_39,E_41) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_400,plain,(
    ! [A_113,D_115,C_111,C_116,E_114,B_112] : k2_xboole_0(k1_tarski(A_113),k2_xboole_0(k2_enumset1(B_112,C_111,D_115,E_114),C_116)) = k2_xboole_0(k3_enumset1(A_113,B_112,C_111,D_115,E_114),C_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_2])).

tff(c_424,plain,(
    ! [A_113,B_5,A_36,A_4,A_81,A_51] : k2_xboole_0(k3_enumset1(A_113,A_81,A_51,A_36,A_4),k1_tarski(B_5)) = k2_xboole_0(k1_tarski(A_113),k3_enumset1(A_81,A_51,A_36,A_4,B_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_400])).

tff(c_428,plain,(
    ! [A_113,B_5,A_36,A_4,A_81,A_51] : k2_xboole_0(k3_enumset1(A_113,A_81,A_51,A_36,A_4),k1_tarski(B_5)) = k4_enumset1(A_113,A_81,A_51,A_36,A_4,B_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_424])).

tff(c_14,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_tarski('#skF_6')) != k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:13:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.32  
% 2.26/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.33  %$ k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.26/1.33  
% 2.26/1.33  %Foreground sorts:
% 2.26/1.33  
% 2.26/1.33  
% 2.26/1.33  %Background operators:
% 2.26/1.33  
% 2.26/1.33  
% 2.26/1.33  %Foreground operators:
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.26/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.26/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.26/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.26/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.26/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.26/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.26/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.26/1.33  
% 2.26/1.34  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 2.26/1.34  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 2.26/1.34  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 2.26/1.34  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 2.26/1.34  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.26/1.34  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.26/1.34  tff(f_40, negated_conjecture, ~(![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 2.26/1.34  tff(c_12, plain, (![E_22, D_21, F_23, A_18, C_20, B_19]: (k2_xboole_0(k1_tarski(A_18), k3_enumset1(B_19, C_20, D_21, E_22, F_23))=k4_enumset1(A_18, B_19, C_20, D_21, E_22, F_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.26/1.34  tff(c_10, plain, (![E_17, A_13, B_14, C_15, D_16]: (k2_xboole_0(k1_tarski(A_13), k2_enumset1(B_14, C_15, D_16, E_17))=k3_enumset1(A_13, B_14, C_15, D_16, E_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.26/1.34  tff(c_8, plain, (![A_9, B_10, C_11, D_12]: (k2_xboole_0(k1_tarski(A_9), k1_enumset1(B_10, C_11, D_12))=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.26/1.34  tff(c_6, plain, (![A_6, B_7, C_8]: (k2_xboole_0(k1_tarski(A_6), k2_tarski(B_7, C_8))=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.34  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(B_5))=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.26/1.34  tff(c_24, plain, (![A_26, B_27, C_28]: (k2_xboole_0(k2_xboole_0(A_26, B_27), C_28)=k2_xboole_0(A_26, k2_xboole_0(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.26/1.34  tff(c_68, plain, (![A_36, B_37, C_38]: (k2_xboole_0(k1_tarski(A_36), k2_xboole_0(k1_tarski(B_37), C_38))=k2_xboole_0(k2_tarski(A_36, B_37), C_38))), inference(superposition, [status(thm), theory('equality')], [c_4, c_24])).
% 2.26/1.34  tff(c_92, plain, (![A_36, A_4, B_5]: (k2_xboole_0(k2_tarski(A_36, A_4), k1_tarski(B_5))=k2_xboole_0(k1_tarski(A_36), k2_tarski(A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_68])).
% 2.26/1.34  tff(c_97, plain, (![A_36, A_4, B_5]: (k2_xboole_0(k2_tarski(A_36, A_4), k1_tarski(B_5))=k1_enumset1(A_36, A_4, B_5))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_92])).
% 2.26/1.34  tff(c_44, plain, (![A_29, B_30, C_31]: (k2_xboole_0(k1_tarski(A_29), k2_tarski(B_30, C_31))=k1_enumset1(A_29, B_30, C_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.34  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.26/1.34  tff(c_137, plain, (![A_51, B_52, C_53, C_54]: (k2_xboole_0(k1_tarski(A_51), k2_xboole_0(k2_tarski(B_52, C_53), C_54))=k2_xboole_0(k1_enumset1(A_51, B_52, C_53), C_54))), inference(superposition, [status(thm), theory('equality')], [c_44, c_2])).
% 2.26/1.34  tff(c_155, plain, (![A_51, A_36, A_4, B_5]: (k2_xboole_0(k1_enumset1(A_51, A_36, A_4), k1_tarski(B_5))=k2_xboole_0(k1_tarski(A_51), k1_enumset1(A_36, A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_137])).
% 2.26/1.34  tff(c_160, plain, (![A_51, A_36, A_4, B_5]: (k2_xboole_0(k1_enumset1(A_51, A_36, A_4), k1_tarski(B_5))=k2_enumset1(A_51, A_36, A_4, B_5))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_155])).
% 2.26/1.34  tff(c_56, plain, (![A_32, B_33, C_34, D_35]: (k2_xboole_0(k1_tarski(A_32), k1_enumset1(B_33, C_34, D_35))=k2_enumset1(A_32, B_33, C_34, D_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.26/1.34  tff(c_254, plain, (![C_80, A_81, B_79, C_83, D_82]: (k2_xboole_0(k1_tarski(A_81), k2_xboole_0(k1_enumset1(B_79, C_80, D_82), C_83))=k2_xboole_0(k2_enumset1(A_81, B_79, C_80, D_82), C_83))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2])).
% 2.26/1.34  tff(c_275, plain, (![B_5, A_36, A_4, A_81, A_51]: (k2_xboole_0(k2_enumset1(A_81, A_51, A_36, A_4), k1_tarski(B_5))=k2_xboole_0(k1_tarski(A_81), k2_enumset1(A_51, A_36, A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_160, c_254])).
% 2.26/1.34  tff(c_280, plain, (![B_5, A_36, A_4, A_81, A_51]: (k2_xboole_0(k2_enumset1(A_81, A_51, A_36, A_4), k1_tarski(B_5))=k3_enumset1(A_81, A_51, A_36, A_4, B_5))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_275])).
% 2.26/1.34  tff(c_98, plain, (![D_39, A_42, C_43, E_41, B_40]: (k2_xboole_0(k1_tarski(A_42), k2_enumset1(B_40, C_43, D_39, E_41))=k3_enumset1(A_42, B_40, C_43, D_39, E_41))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.26/1.34  tff(c_400, plain, (![A_113, D_115, C_111, C_116, E_114, B_112]: (k2_xboole_0(k1_tarski(A_113), k2_xboole_0(k2_enumset1(B_112, C_111, D_115, E_114), C_116))=k2_xboole_0(k3_enumset1(A_113, B_112, C_111, D_115, E_114), C_116))), inference(superposition, [status(thm), theory('equality')], [c_98, c_2])).
% 2.26/1.34  tff(c_424, plain, (![A_113, B_5, A_36, A_4, A_81, A_51]: (k2_xboole_0(k3_enumset1(A_113, A_81, A_51, A_36, A_4), k1_tarski(B_5))=k2_xboole_0(k1_tarski(A_113), k3_enumset1(A_81, A_51, A_36, A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_280, c_400])).
% 2.26/1.34  tff(c_428, plain, (![A_113, B_5, A_36, A_4, A_81, A_51]: (k2_xboole_0(k3_enumset1(A_113, A_81, A_51, A_36, A_4), k1_tarski(B_5))=k4_enumset1(A_113, A_81, A_51, A_36, A_4, B_5))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_424])).
% 2.26/1.34  tff(c_14, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_tarski('#skF_6'))!=k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.26/1.34  tff(c_453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_428, c_14])).
% 2.26/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/1.34  
% 2.26/1.34  Inference rules
% 2.26/1.34  ----------------------
% 2.26/1.34  #Ref     : 0
% 2.26/1.34  #Sup     : 115
% 2.26/1.34  #Fact    : 0
% 2.26/1.34  #Define  : 0
% 2.26/1.34  #Split   : 0
% 2.26/1.34  #Chain   : 0
% 2.26/1.34  #Close   : 0
% 2.26/1.34  
% 2.26/1.34  Ordering : KBO
% 2.26/1.34  
% 2.26/1.34  Simplification rules
% 2.26/1.34  ----------------------
% 2.26/1.34  #Subsume      : 0
% 2.26/1.34  #Demod        : 52
% 2.26/1.34  #Tautology    : 60
% 2.26/1.34  #SimpNegUnit  : 0
% 2.26/1.34  #BackRed      : 1
% 2.26/1.34  
% 2.26/1.34  #Partial instantiations: 0
% 2.26/1.34  #Strategies tried      : 1
% 2.26/1.34  
% 2.26/1.34  Timing (in seconds)
% 2.26/1.34  ----------------------
% 2.26/1.34  Preprocessing        : 0.26
% 2.26/1.34  Parsing              : 0.15
% 2.26/1.34  CNF conversion       : 0.02
% 2.26/1.34  Main loop            : 0.28
% 2.26/1.34  Inferencing          : 0.13
% 2.26/1.34  Reduction            : 0.08
% 2.26/1.34  Demodulation         : 0.07
% 2.26/1.34  BG Simplification    : 0.02
% 2.26/1.34  Subsumption          : 0.03
% 2.26/1.34  Abstraction          : 0.02
% 2.26/1.34  MUC search           : 0.00
% 2.26/1.34  Cooper               : 0.00
% 2.26/1.34  Total                : 0.57
% 2.26/1.34  Index Insertion      : 0.00
% 2.26/1.34  Index Deletion       : 0.00
% 2.26/1.34  Index Matching       : 0.00
% 2.26/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
