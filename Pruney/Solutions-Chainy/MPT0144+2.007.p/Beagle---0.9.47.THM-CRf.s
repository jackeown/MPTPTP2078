%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:52 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   48 (  70 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   28 (  50 expanded)
%              Number of equality atoms :   27 (  49 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_38,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_40,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_tarski(A,B),k1_enumset1(C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

tff(c_18,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,G_19,D_16] : k2_xboole_0(k2_enumset1(A_13,B_14,C_15,D_16),k1_enumset1(E_17,F_18,G_19)) = k5_enumset1(A_13,B_14,C_15,D_16,E_17,F_18,G_19) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k2_tarski(A_22,B_23),k1_tarski(C_24)) = k1_enumset1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [A_20,B_21] : k2_xboole_0(k1_tarski(A_20),k1_tarski(B_21)) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_55,plain,(
    ! [A_42,B_43,C_44] : k2_xboole_0(k2_xboole_0(A_42,B_43),C_44) = k2_xboole_0(A_42,k2_xboole_0(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_98,plain,(
    ! [A_55,B_56,C_57] : k2_xboole_0(k1_tarski(A_55),k2_xboole_0(k1_tarski(B_56),C_57)) = k2_xboole_0(k2_tarski(A_55,B_56),C_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_55])).

tff(c_116,plain,(
    ! [A_55,A_20,B_21] : k2_xboole_0(k2_tarski(A_55,A_20),k1_tarski(B_21)) = k2_xboole_0(k1_tarski(A_55),k2_tarski(A_20,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_98])).

tff(c_120,plain,(
    ! [A_55,A_20,B_21] : k2_xboole_0(k1_tarski(A_55),k2_tarski(A_20,B_21)) = k1_enumset1(A_55,A_20,B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_116])).

tff(c_26,plain,(
    ! [E_33,A_29,D_32,C_31,B_30] : k2_xboole_0(k2_tarski(A_29,B_30),k1_enumset1(C_31,D_32,E_33)) = k3_enumset1(A_29,B_30,C_31,D_32,E_33) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_154,plain,(
    ! [A_68,B_69,C_70,C_71] : k2_xboole_0(k2_tarski(A_68,B_69),k2_xboole_0(k1_tarski(C_70),C_71)) = k2_xboole_0(k1_enumset1(A_68,B_69,C_70),C_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_55])).

tff(c_166,plain,(
    ! [A_20,B_21,A_55,B_69,A_68] : k2_xboole_0(k1_enumset1(A_68,B_69,A_55),k2_tarski(A_20,B_21)) = k2_xboole_0(k2_tarski(A_68,B_69),k1_enumset1(A_55,A_20,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_154])).

tff(c_176,plain,(
    ! [A_20,B_21,A_55,B_69,A_68] : k2_xboole_0(k1_enumset1(A_68,B_69,A_55),k2_tarski(A_20,B_21)) = k3_enumset1(A_68,B_69,A_55,A_20,B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_166])).

tff(c_86,plain,(
    ! [A_51,B_52,C_53,D_54] : k2_xboole_0(k1_enumset1(A_51,B_52,C_53),k1_tarski(D_54)) = k2_enumset1(A_51,B_52,C_53,D_54) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7] : k2_xboole_0(k2_xboole_0(A_5,B_6),C_7) = k2_xboole_0(A_5,k2_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_310,plain,(
    ! [D_108,A_105,C_109,C_107,B_106] : k2_xboole_0(k1_enumset1(A_105,B_106,C_107),k2_xboole_0(k1_tarski(D_108),C_109)) = k2_xboole_0(k2_enumset1(A_105,B_106,C_107,D_108),C_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_4])).

tff(c_337,plain,(
    ! [A_105,A_20,B_21,C_107,B_106] : k2_xboole_0(k2_enumset1(A_105,B_106,C_107,A_20),k1_tarski(B_21)) = k2_xboole_0(k1_enumset1(A_105,B_106,C_107),k2_tarski(A_20,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_310])).

tff(c_343,plain,(
    ! [B_111,A_110,B_113,C_112,A_114] : k2_xboole_0(k2_enumset1(A_110,B_111,C_112,A_114),k1_tarski(B_113)) = k3_enumset1(A_110,B_111,C_112,A_114,B_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_337])).

tff(c_545,plain,(
    ! [C_158,C_159,A_161,A_157,B_160,B_162] : k2_xboole_0(k2_enumset1(A_157,B_160,C_158,A_161),k2_xboole_0(k1_tarski(B_162),C_159)) = k2_xboole_0(k3_enumset1(A_157,B_160,C_158,A_161,B_162),C_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_4])).

tff(c_569,plain,(
    ! [C_158,A_20,B_21,A_161,A_55,A_157,B_160] : k2_xboole_0(k3_enumset1(A_157,B_160,C_158,A_161,A_55),k2_tarski(A_20,B_21)) = k2_xboole_0(k2_enumset1(A_157,B_160,C_158,A_161),k1_enumset1(A_55,A_20,B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_545])).

tff(c_580,plain,(
    ! [C_158,A_20,B_21,A_161,A_55,A_157,B_160] : k2_xboole_0(k3_enumset1(A_157,B_160,C_158,A_161,A_55),k2_tarski(A_20,B_21)) = k5_enumset1(A_157,B_160,C_158,A_161,A_55,A_20,B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_569])).

tff(c_28,plain,(
    k2_xboole_0(k3_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k2_tarski('#skF_8','#skF_9')) != k5_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.32  % Computer   : n014.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % DateTime   : Tue Dec  1 20:08:37 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.45  
% 2.99/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.46  %$ r2_hidden > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 2.99/1.46  
% 2.99/1.46  %Foreground sorts:
% 2.99/1.46  
% 2.99/1.46  
% 2.99/1.46  %Background operators:
% 2.99/1.46  
% 2.99/1.46  
% 2.99/1.46  %Foreground operators:
% 2.99/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.99/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.99/1.46  tff('#skF_7', type, '#skF_7': $i).
% 2.99/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.99/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.99/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.99/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.99/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.99/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.46  tff('#skF_9', type, '#skF_9': $i).
% 2.99/1.46  tff('#skF_8', type, '#skF_8': $i).
% 2.99/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.99/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.99/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.99/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.99/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.99/1.46  
% 3.14/1.47  tff(f_38, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_enumset1)).
% 3.14/1.47  tff(f_42, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 3.14/1.47  tff(f_40, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.14/1.47  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.14/1.47  tff(f_46, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_tarski(A, B), k1_enumset1(C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_enumset1)).
% 3.14/1.47  tff(f_44, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 3.14/1.47  tff(f_49, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 3.14/1.47  tff(c_18, plain, (![E_17, F_18, A_13, B_14, C_15, G_19, D_16]: (k2_xboole_0(k2_enumset1(A_13, B_14, C_15, D_16), k1_enumset1(E_17, F_18, G_19))=k5_enumset1(A_13, B_14, C_15, D_16, E_17, F_18, G_19))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.14/1.47  tff(c_22, plain, (![A_22, B_23, C_24]: (k2_xboole_0(k2_tarski(A_22, B_23), k1_tarski(C_24))=k1_enumset1(A_22, B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.14/1.47  tff(c_20, plain, (![A_20, B_21]: (k2_xboole_0(k1_tarski(A_20), k1_tarski(B_21))=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.14/1.47  tff(c_55, plain, (![A_42, B_43, C_44]: (k2_xboole_0(k2_xboole_0(A_42, B_43), C_44)=k2_xboole_0(A_42, k2_xboole_0(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.14/1.47  tff(c_98, plain, (![A_55, B_56, C_57]: (k2_xboole_0(k1_tarski(A_55), k2_xboole_0(k1_tarski(B_56), C_57))=k2_xboole_0(k2_tarski(A_55, B_56), C_57))), inference(superposition, [status(thm), theory('equality')], [c_20, c_55])).
% 3.14/1.47  tff(c_116, plain, (![A_55, A_20, B_21]: (k2_xboole_0(k2_tarski(A_55, A_20), k1_tarski(B_21))=k2_xboole_0(k1_tarski(A_55), k2_tarski(A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_98])).
% 3.14/1.47  tff(c_120, plain, (![A_55, A_20, B_21]: (k2_xboole_0(k1_tarski(A_55), k2_tarski(A_20, B_21))=k1_enumset1(A_55, A_20, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_116])).
% 3.14/1.47  tff(c_26, plain, (![E_33, A_29, D_32, C_31, B_30]: (k2_xboole_0(k2_tarski(A_29, B_30), k1_enumset1(C_31, D_32, E_33))=k3_enumset1(A_29, B_30, C_31, D_32, E_33))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.14/1.47  tff(c_154, plain, (![A_68, B_69, C_70, C_71]: (k2_xboole_0(k2_tarski(A_68, B_69), k2_xboole_0(k1_tarski(C_70), C_71))=k2_xboole_0(k1_enumset1(A_68, B_69, C_70), C_71))), inference(superposition, [status(thm), theory('equality')], [c_22, c_55])).
% 3.14/1.47  tff(c_166, plain, (![A_20, B_21, A_55, B_69, A_68]: (k2_xboole_0(k1_enumset1(A_68, B_69, A_55), k2_tarski(A_20, B_21))=k2_xboole_0(k2_tarski(A_68, B_69), k1_enumset1(A_55, A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_120, c_154])).
% 3.14/1.47  tff(c_176, plain, (![A_20, B_21, A_55, B_69, A_68]: (k2_xboole_0(k1_enumset1(A_68, B_69, A_55), k2_tarski(A_20, B_21))=k3_enumset1(A_68, B_69, A_55, A_20, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_166])).
% 3.14/1.47  tff(c_86, plain, (![A_51, B_52, C_53, D_54]: (k2_xboole_0(k1_enumset1(A_51, B_52, C_53), k1_tarski(D_54))=k2_enumset1(A_51, B_52, C_53, D_54))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.14/1.47  tff(c_4, plain, (![A_5, B_6, C_7]: (k2_xboole_0(k2_xboole_0(A_5, B_6), C_7)=k2_xboole_0(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.14/1.47  tff(c_310, plain, (![D_108, A_105, C_109, C_107, B_106]: (k2_xboole_0(k1_enumset1(A_105, B_106, C_107), k2_xboole_0(k1_tarski(D_108), C_109))=k2_xboole_0(k2_enumset1(A_105, B_106, C_107, D_108), C_109))), inference(superposition, [status(thm), theory('equality')], [c_86, c_4])).
% 3.14/1.47  tff(c_337, plain, (![A_105, A_20, B_21, C_107, B_106]: (k2_xboole_0(k2_enumset1(A_105, B_106, C_107, A_20), k1_tarski(B_21))=k2_xboole_0(k1_enumset1(A_105, B_106, C_107), k2_tarski(A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_310])).
% 3.14/1.47  tff(c_343, plain, (![B_111, A_110, B_113, C_112, A_114]: (k2_xboole_0(k2_enumset1(A_110, B_111, C_112, A_114), k1_tarski(B_113))=k3_enumset1(A_110, B_111, C_112, A_114, B_113))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_337])).
% 3.14/1.47  tff(c_545, plain, (![C_158, C_159, A_161, A_157, B_160, B_162]: (k2_xboole_0(k2_enumset1(A_157, B_160, C_158, A_161), k2_xboole_0(k1_tarski(B_162), C_159))=k2_xboole_0(k3_enumset1(A_157, B_160, C_158, A_161, B_162), C_159))), inference(superposition, [status(thm), theory('equality')], [c_343, c_4])).
% 3.14/1.47  tff(c_569, plain, (![C_158, A_20, B_21, A_161, A_55, A_157, B_160]: (k2_xboole_0(k3_enumset1(A_157, B_160, C_158, A_161, A_55), k2_tarski(A_20, B_21))=k2_xboole_0(k2_enumset1(A_157, B_160, C_158, A_161), k1_enumset1(A_55, A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_120, c_545])).
% 3.14/1.47  tff(c_580, plain, (![C_158, A_20, B_21, A_161, A_55, A_157, B_160]: (k2_xboole_0(k3_enumset1(A_157, B_160, C_158, A_161, A_55), k2_tarski(A_20, B_21))=k5_enumset1(A_157, B_160, C_158, A_161, A_55, A_20, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_569])).
% 3.14/1.47  tff(c_28, plain, (k2_xboole_0(k3_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k2_tarski('#skF_8', '#skF_9'))!=k5_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.14/1.47  tff(c_778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_580, c_28])).
% 3.14/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.47  
% 3.14/1.47  Inference rules
% 3.14/1.47  ----------------------
% 3.14/1.47  #Ref     : 0
% 3.14/1.47  #Sup     : 189
% 3.14/1.47  #Fact    : 0
% 3.14/1.47  #Define  : 0
% 3.14/1.47  #Split   : 0
% 3.14/1.47  #Chain   : 0
% 3.14/1.47  #Close   : 0
% 3.14/1.47  
% 3.14/1.47  Ordering : KBO
% 3.14/1.47  
% 3.14/1.47  Simplification rules
% 3.14/1.47  ----------------------
% 3.14/1.47  #Subsume      : 0
% 3.14/1.47  #Demod        : 105
% 3.14/1.47  #Tautology    : 100
% 3.14/1.47  #SimpNegUnit  : 0
% 3.14/1.47  #BackRed      : 4
% 3.14/1.47  
% 3.14/1.47  #Partial instantiations: 0
% 3.14/1.47  #Strategies tried      : 1
% 3.14/1.47  
% 3.14/1.47  Timing (in seconds)
% 3.14/1.47  ----------------------
% 3.14/1.47  Preprocessing        : 0.29
% 3.14/1.47  Parsing              : 0.15
% 3.14/1.47  CNF conversion       : 0.02
% 3.14/1.47  Main loop            : 0.43
% 3.14/1.47  Inferencing          : 0.19
% 3.14/1.47  Reduction            : 0.14
% 3.14/1.47  Demodulation         : 0.11
% 3.14/1.47  BG Simplification    : 0.03
% 3.14/1.47  Subsumption          : 0.05
% 3.14/1.47  Abstraction          : 0.03
% 3.14/1.47  MUC search           : 0.00
% 3.14/1.47  Cooper               : 0.00
% 3.14/1.47  Total                : 0.74
% 3.14/1.47  Index Insertion      : 0.00
% 3.14/1.47  Index Deletion       : 0.00
% 3.14/1.47  Index Matching       : 0.00
% 3.14/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
