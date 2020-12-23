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
% DateTime   : Thu Dec  3 09:45:59 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   48 (  61 expanded)
%              Number of leaves         :   28 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   27 (  40 expanded)
%              Number of equality atoms :   26 (  39 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_38,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_40,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

tff(c_18,plain,(
    ! [H_20,E_17,F_18,A_13,B_14,C_15,G_19,D_16] : k2_xboole_0(k2_enumset1(A_13,B_14,C_15,D_16),k2_enumset1(E_17,F_18,G_19,H_20)) = k6_enumset1(A_13,B_14,C_15,D_16,E_17,F_18,G_19,H_20) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,(
    ! [A_26,B_27,C_28,D_29] : k2_xboole_0(k1_enumset1(A_26,B_27,C_28),k1_tarski(D_29)) = k2_enumset1(A_26,B_27,C_28,D_29) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_20,plain,(
    ! [A_21,B_22] : k2_xboole_0(k1_tarski(A_21),k1_tarski(B_22)) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_22,plain,(
    ! [A_23,B_24,C_25] : k2_xboole_0(k2_tarski(A_23,B_24),k1_tarski(C_25)) = k1_enumset1(A_23,B_24,C_25) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_55,plain,(
    ! [A_43,B_44,C_45] : k2_xboole_0(k2_xboole_0(A_43,B_44),C_45) = k2_xboole_0(A_43,k2_xboole_0(B_44,C_45)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_154,plain,(
    ! [A_69,B_70,C_71,C_72] : k2_xboole_0(k2_tarski(A_69,B_70),k2_xboole_0(k1_tarski(C_71),C_72)) = k2_xboole_0(k1_enumset1(A_69,B_70,C_71),C_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_55])).

tff(c_172,plain,(
    ! [A_69,B_70,A_21,B_22] : k2_xboole_0(k1_enumset1(A_69,B_70,A_21),k1_tarski(B_22)) = k2_xboole_0(k2_tarski(A_69,B_70),k2_tarski(A_21,B_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_154])).

tff(c_176,plain,(
    ! [A_69,B_70,A_21,B_22] : k2_xboole_0(k2_tarski(A_69,B_70),k2_tarski(A_21,B_22)) = k2_enumset1(A_69,B_70,A_21,B_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_172])).

tff(c_98,plain,(
    ! [A_56,B_57,C_58] : k2_xboole_0(k1_tarski(A_56),k2_xboole_0(k1_tarski(B_57),C_58)) = k2_xboole_0(k2_tarski(A_56,B_57),C_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_55])).

tff(c_116,plain,(
    ! [A_56,A_21,B_22] : k2_xboole_0(k2_tarski(A_56,A_21),k1_tarski(B_22)) = k2_xboole_0(k1_tarski(A_56),k2_tarski(A_21,B_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_98])).

tff(c_120,plain,(
    ! [A_56,A_21,B_22] : k2_xboole_0(k1_tarski(A_56),k2_tarski(A_21,B_22)) = k1_enumset1(A_56,A_21,B_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_116])).

tff(c_73,plain,(
    ! [A_21,B_22,C_45] : k2_xboole_0(k1_tarski(A_21),k2_xboole_0(k1_tarski(B_22),C_45)) = k2_xboole_0(k2_tarski(A_21,B_22),C_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_55])).

tff(c_142,plain,(
    ! [A_66,C_64,D_68,E_67,B_65] : k2_xboole_0(k2_enumset1(A_66,B_65,C_64,D_68),k1_tarski(E_67)) = k3_enumset1(A_66,B_65,C_64,D_68,E_67) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7] : k2_xboole_0(k2_xboole_0(A_5,B_6),C_7) = k2_xboole_0(A_5,k2_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_315,plain,(
    ! [A_111,B_108,C_109,D_110,C_112,E_107] : k2_xboole_0(k2_enumset1(A_111,B_108,C_109,D_110),k2_xboole_0(k1_tarski(E_107),C_112)) = k2_xboole_0(k3_enumset1(A_111,B_108,C_109,D_110,E_107),C_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_4])).

tff(c_746,plain,(
    ! [B_212,A_209,C_210,A_214,D_211,B_213,C_208] : k2_xboole_0(k3_enumset1(A_214,B_212,C_208,D_211,A_209),k2_xboole_0(k1_tarski(B_213),C_210)) = k2_xboole_0(k2_enumset1(A_214,B_212,C_208,D_211),k2_xboole_0(k2_tarski(A_209,B_213),C_210)) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_315])).

tff(c_773,plain,(
    ! [B_212,A_21,B_22,A_209,A_56,A_214,D_211,C_208] : k2_xboole_0(k2_enumset1(A_214,B_212,C_208,D_211),k2_xboole_0(k2_tarski(A_209,A_56),k2_tarski(A_21,B_22))) = k2_xboole_0(k3_enumset1(A_214,B_212,C_208,D_211,A_209),k1_enumset1(A_56,A_21,B_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_746])).

tff(c_787,plain,(
    ! [B_212,A_21,B_22,A_209,A_56,A_214,D_211,C_208] : k2_xboole_0(k3_enumset1(A_214,B_212,C_208,D_211,A_209),k1_enumset1(A_56,A_21,B_22)) = k6_enumset1(A_214,B_212,C_208,D_211,A_209,A_56,A_21,B_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_176,c_773])).

tff(c_28,plain,(
    k2_xboole_0(k3_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),k1_enumset1('#skF_8','#skF_9','#skF_10')) != k6_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:57:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.56  
% 3.22/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.56  %$ r2_hidden > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 3.22/1.56  
% 3.22/1.56  %Foreground sorts:
% 3.22/1.56  
% 3.22/1.56  
% 3.22/1.56  %Background operators:
% 3.22/1.56  
% 3.22/1.56  
% 3.22/1.56  %Foreground operators:
% 3.22/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.22/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.22/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.22/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.22/1.56  tff('#skF_10', type, '#skF_10': $i).
% 3.22/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.22/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.22/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.22/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.22/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.56  tff('#skF_9', type, '#skF_9': $i).
% 3.22/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.56  tff('#skF_8', type, '#skF_8': $i).
% 3.22/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.22/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.22/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.22/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.22/1.56  
% 3.22/1.57  tff(f_38, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 3.22/1.57  tff(f_44, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 3.22/1.57  tff(f_40, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.22/1.57  tff(f_42, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 3.22/1.57  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.22/1.57  tff(f_46, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_enumset1)).
% 3.22/1.57  tff(f_49, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 3.22/1.57  tff(c_18, plain, (![H_20, E_17, F_18, A_13, B_14, C_15, G_19, D_16]: (k2_xboole_0(k2_enumset1(A_13, B_14, C_15, D_16), k2_enumset1(E_17, F_18, G_19, H_20))=k6_enumset1(A_13, B_14, C_15, D_16, E_17, F_18, G_19, H_20))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.22/1.57  tff(c_24, plain, (![A_26, B_27, C_28, D_29]: (k2_xboole_0(k1_enumset1(A_26, B_27, C_28), k1_tarski(D_29))=k2_enumset1(A_26, B_27, C_28, D_29))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.22/1.57  tff(c_20, plain, (![A_21, B_22]: (k2_xboole_0(k1_tarski(A_21), k1_tarski(B_22))=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.22/1.57  tff(c_22, plain, (![A_23, B_24, C_25]: (k2_xboole_0(k2_tarski(A_23, B_24), k1_tarski(C_25))=k1_enumset1(A_23, B_24, C_25))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.22/1.57  tff(c_55, plain, (![A_43, B_44, C_45]: (k2_xboole_0(k2_xboole_0(A_43, B_44), C_45)=k2_xboole_0(A_43, k2_xboole_0(B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.22/1.57  tff(c_154, plain, (![A_69, B_70, C_71, C_72]: (k2_xboole_0(k2_tarski(A_69, B_70), k2_xboole_0(k1_tarski(C_71), C_72))=k2_xboole_0(k1_enumset1(A_69, B_70, C_71), C_72))), inference(superposition, [status(thm), theory('equality')], [c_22, c_55])).
% 3.22/1.57  tff(c_172, plain, (![A_69, B_70, A_21, B_22]: (k2_xboole_0(k1_enumset1(A_69, B_70, A_21), k1_tarski(B_22))=k2_xboole_0(k2_tarski(A_69, B_70), k2_tarski(A_21, B_22)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_154])).
% 3.22/1.57  tff(c_176, plain, (![A_69, B_70, A_21, B_22]: (k2_xboole_0(k2_tarski(A_69, B_70), k2_tarski(A_21, B_22))=k2_enumset1(A_69, B_70, A_21, B_22))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_172])).
% 3.22/1.57  tff(c_98, plain, (![A_56, B_57, C_58]: (k2_xboole_0(k1_tarski(A_56), k2_xboole_0(k1_tarski(B_57), C_58))=k2_xboole_0(k2_tarski(A_56, B_57), C_58))), inference(superposition, [status(thm), theory('equality')], [c_20, c_55])).
% 3.22/1.57  tff(c_116, plain, (![A_56, A_21, B_22]: (k2_xboole_0(k2_tarski(A_56, A_21), k1_tarski(B_22))=k2_xboole_0(k1_tarski(A_56), k2_tarski(A_21, B_22)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_98])).
% 3.22/1.57  tff(c_120, plain, (![A_56, A_21, B_22]: (k2_xboole_0(k1_tarski(A_56), k2_tarski(A_21, B_22))=k1_enumset1(A_56, A_21, B_22))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_116])).
% 3.22/1.57  tff(c_73, plain, (![A_21, B_22, C_45]: (k2_xboole_0(k1_tarski(A_21), k2_xboole_0(k1_tarski(B_22), C_45))=k2_xboole_0(k2_tarski(A_21, B_22), C_45))), inference(superposition, [status(thm), theory('equality')], [c_20, c_55])).
% 3.22/1.57  tff(c_142, plain, (![A_66, C_64, D_68, E_67, B_65]: (k2_xboole_0(k2_enumset1(A_66, B_65, C_64, D_68), k1_tarski(E_67))=k3_enumset1(A_66, B_65, C_64, D_68, E_67))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.22/1.57  tff(c_4, plain, (![A_5, B_6, C_7]: (k2_xboole_0(k2_xboole_0(A_5, B_6), C_7)=k2_xboole_0(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.22/1.57  tff(c_315, plain, (![A_111, B_108, C_109, D_110, C_112, E_107]: (k2_xboole_0(k2_enumset1(A_111, B_108, C_109, D_110), k2_xboole_0(k1_tarski(E_107), C_112))=k2_xboole_0(k3_enumset1(A_111, B_108, C_109, D_110, E_107), C_112))), inference(superposition, [status(thm), theory('equality')], [c_142, c_4])).
% 3.22/1.57  tff(c_746, plain, (![B_212, A_209, C_210, A_214, D_211, B_213, C_208]: (k2_xboole_0(k3_enumset1(A_214, B_212, C_208, D_211, A_209), k2_xboole_0(k1_tarski(B_213), C_210))=k2_xboole_0(k2_enumset1(A_214, B_212, C_208, D_211), k2_xboole_0(k2_tarski(A_209, B_213), C_210)))), inference(superposition, [status(thm), theory('equality')], [c_73, c_315])).
% 3.22/1.57  tff(c_773, plain, (![B_212, A_21, B_22, A_209, A_56, A_214, D_211, C_208]: (k2_xboole_0(k2_enumset1(A_214, B_212, C_208, D_211), k2_xboole_0(k2_tarski(A_209, A_56), k2_tarski(A_21, B_22)))=k2_xboole_0(k3_enumset1(A_214, B_212, C_208, D_211, A_209), k1_enumset1(A_56, A_21, B_22)))), inference(superposition, [status(thm), theory('equality')], [c_120, c_746])).
% 3.22/1.57  tff(c_787, plain, (![B_212, A_21, B_22, A_209, A_56, A_214, D_211, C_208]: (k2_xboole_0(k3_enumset1(A_214, B_212, C_208, D_211, A_209), k1_enumset1(A_56, A_21, B_22))=k6_enumset1(A_214, B_212, C_208, D_211, A_209, A_56, A_21, B_22))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_176, c_773])).
% 3.22/1.57  tff(c_28, plain, (k2_xboole_0(k3_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), k1_enumset1('#skF_8', '#skF_9', '#skF_10'))!=k6_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.22/1.57  tff(c_820, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_787, c_28])).
% 3.22/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.57  
% 3.22/1.57  Inference rules
% 3.22/1.57  ----------------------
% 3.22/1.57  #Ref     : 0
% 3.22/1.57  #Sup     : 197
% 3.22/1.57  #Fact    : 0
% 3.22/1.57  #Define  : 0
% 3.22/1.57  #Split   : 0
% 3.22/1.57  #Chain   : 0
% 3.22/1.57  #Close   : 0
% 3.22/1.57  
% 3.22/1.57  Ordering : KBO
% 3.22/1.57  
% 3.22/1.57  Simplification rules
% 3.22/1.57  ----------------------
% 3.22/1.57  #Subsume      : 0
% 3.22/1.57  #Demod        : 123
% 3.22/1.57  #Tautology    : 109
% 3.22/1.57  #SimpNegUnit  : 0
% 3.22/1.57  #BackRed      : 5
% 3.22/1.57  
% 3.22/1.57  #Partial instantiations: 0
% 3.22/1.57  #Strategies tried      : 1
% 3.22/1.57  
% 3.22/1.57  Timing (in seconds)
% 3.22/1.57  ----------------------
% 3.22/1.57  Preprocessing        : 0.31
% 3.22/1.57  Parsing              : 0.17
% 3.22/1.57  CNF conversion       : 0.02
% 3.22/1.57  Main loop            : 0.46
% 3.22/1.57  Inferencing          : 0.20
% 3.22/1.57  Reduction            : 0.16
% 3.22/1.57  Demodulation         : 0.13
% 3.22/1.57  BG Simplification    : 0.03
% 3.22/1.57  Subsumption          : 0.05
% 3.22/1.57  Abstraction          : 0.04
% 3.22/1.58  MUC search           : 0.00
% 3.22/1.58  Cooper               : 0.00
% 3.22/1.58  Total                : 0.80
% 3.22/1.58  Index Insertion      : 0.00
% 3.22/1.58  Index Deletion       : 0.00
% 3.22/1.58  Index Matching       : 0.00
% 3.22/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
