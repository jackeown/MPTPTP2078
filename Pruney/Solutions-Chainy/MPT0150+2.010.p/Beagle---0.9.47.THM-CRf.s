%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:00 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   44 (  45 expanded)
%              Number of leaves         :   29 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   22 (  23 expanded)
%              Number of equality atoms :   21 (  22 expanded)
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

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_enumset1(E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

tff(c_18,plain,(
    ! [F_41,G_42,D_39,A_36,E_40,H_43,C_38,B_37] : k2_xboole_0(k2_tarski(A_36,B_37),k4_enumset1(C_38,D_39,E_40,F_41,G_42,H_43)) = k6_enumset1(A_36,B_37,C_38,D_39,E_40,F_41,G_42,H_43) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_254,plain,(
    ! [C_108,D_112,F_110,A_107,B_113,E_109,G_111] : k2_xboole_0(k1_tarski(A_107),k4_enumset1(B_113,C_108,D_112,E_109,F_110,G_111)) = k5_enumset1(A_107,B_113,C_108,D_112,E_109,F_110,G_111) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),k1_tarski(B_7)) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_41,plain,(
    ! [A_56,B_57,C_58] : k2_xboole_0(k2_xboole_0(A_56,B_57),C_58) = k2_xboole_0(A_56,k2_xboole_0(B_57,C_58)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_56,plain,(
    ! [A_6,B_7,C_58] : k2_xboole_0(k1_tarski(A_6),k2_xboole_0(k1_tarski(B_7),C_58)) = k2_xboole_0(k2_tarski(A_6,B_7),C_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_41])).

tff(c_263,plain,(
    ! [C_108,D_112,F_110,A_107,B_113,E_109,G_111,A_6] : k2_xboole_0(k2_tarski(A_6,A_107),k4_enumset1(B_113,C_108,D_112,E_109,F_110,G_111)) = k2_xboole_0(k1_tarski(A_6),k5_enumset1(A_107,B_113,C_108,D_112,E_109,F_110,G_111)) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_56])).

tff(c_607,plain,(
    ! [C_108,D_112,F_110,A_107,B_113,E_109,G_111,A_6] : k2_xboole_0(k1_tarski(A_6),k5_enumset1(A_107,B_113,C_108,D_112,E_109,F_110,G_111)) = k6_enumset1(A_6,A_107,B_113,C_108,D_112,E_109,F_110,G_111) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_263])).

tff(c_16,plain,(
    ! [G_35,E_33,A_29,F_34,D_32,C_31,B_30] : k2_xboole_0(k2_enumset1(A_29,B_30,C_31,D_32),k1_enumset1(E_33,F_34,G_35)) = k5_enumset1(A_29,B_30,C_31,D_32,E_33,F_34,G_35) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_99,plain,(
    ! [B_67,A_66,C_65,D_68,E_69] : k2_xboole_0(k1_tarski(A_66),k2_enumset1(B_67,C_65,D_68,E_69)) = k3_enumset1(A_66,B_67,C_65,D_68,E_69) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_272,plain,(
    ! [C_114,A_116,D_115,B_119,C_117,E_118] : k2_xboole_0(k1_tarski(A_116),k2_xboole_0(k2_enumset1(B_119,C_114,D_115,E_118),C_117)) = k2_xboole_0(k3_enumset1(A_116,B_119,C_114,D_115,E_118),C_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_2])).

tff(c_290,plain,(
    ! [G_35,E_33,A_29,A_116,F_34,D_32,C_31,B_30] : k2_xboole_0(k3_enumset1(A_116,A_29,B_30,C_31,D_32),k1_enumset1(E_33,F_34,G_35)) = k2_xboole_0(k1_tarski(A_116),k5_enumset1(A_29,B_30,C_31,D_32,E_33,F_34,G_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_272])).

tff(c_629,plain,(
    ! [G_35,E_33,A_29,A_116,F_34,D_32,C_31,B_30] : k2_xboole_0(k3_enumset1(A_116,A_29,B_30,C_31,D_32),k1_enumset1(E_33,F_34,G_35)) = k6_enumset1(A_116,A_29,B_30,C_31,D_32,E_33,F_34,G_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_607,c_290])).

tff(c_22,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_enumset1('#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.49  
% 2.85/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.49  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.85/1.49  
% 2.85/1.49  %Foreground sorts:
% 2.85/1.49  
% 2.85/1.49  
% 2.85/1.49  %Background operators:
% 2.85/1.49  
% 2.85/1.49  
% 2.85/1.49  %Foreground operators:
% 2.85/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.85/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.85/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.85/1.49  tff('#skF_7', type, '#skF_7': $i).
% 2.85/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.85/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.85/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.85/1.49  tff('#skF_5', type, '#skF_5': $i).
% 2.85/1.49  tff('#skF_6', type, '#skF_6': $i).
% 2.85/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.85/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.85/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.85/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.85/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.85/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.85/1.49  tff('#skF_8', type, '#skF_8': $i).
% 2.85/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.85/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.85/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.85/1.49  
% 2.85/1.50  tff(f_43, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_enumset1)).
% 2.85/1.50  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 2.85/1.50  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.85/1.50  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.85/1.50  tff(f_41, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_enumset1(E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_enumset1)).
% 2.85/1.50  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 2.85/1.50  tff(f_48, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 2.85/1.50  tff(c_18, plain, (![F_41, G_42, D_39, A_36, E_40, H_43, C_38, B_37]: (k2_xboole_0(k2_tarski(A_36, B_37), k4_enumset1(C_38, D_39, E_40, F_41, G_42, H_43))=k6_enumset1(A_36, B_37, C_38, D_39, E_40, F_41, G_42, H_43))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.85/1.50  tff(c_254, plain, (![C_108, D_112, F_110, A_107, B_113, E_109, G_111]: (k2_xboole_0(k1_tarski(A_107), k4_enumset1(B_113, C_108, D_112, E_109, F_110, G_111))=k5_enumset1(A_107, B_113, C_108, D_112, E_109, F_110, G_111))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.85/1.50  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(B_7))=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.85/1.50  tff(c_41, plain, (![A_56, B_57, C_58]: (k2_xboole_0(k2_xboole_0(A_56, B_57), C_58)=k2_xboole_0(A_56, k2_xboole_0(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.85/1.50  tff(c_56, plain, (![A_6, B_7, C_58]: (k2_xboole_0(k1_tarski(A_6), k2_xboole_0(k1_tarski(B_7), C_58))=k2_xboole_0(k2_tarski(A_6, B_7), C_58))), inference(superposition, [status(thm), theory('equality')], [c_6, c_41])).
% 2.85/1.50  tff(c_263, plain, (![C_108, D_112, F_110, A_107, B_113, E_109, G_111, A_6]: (k2_xboole_0(k2_tarski(A_6, A_107), k4_enumset1(B_113, C_108, D_112, E_109, F_110, G_111))=k2_xboole_0(k1_tarski(A_6), k5_enumset1(A_107, B_113, C_108, D_112, E_109, F_110, G_111)))), inference(superposition, [status(thm), theory('equality')], [c_254, c_56])).
% 2.85/1.50  tff(c_607, plain, (![C_108, D_112, F_110, A_107, B_113, E_109, G_111, A_6]: (k2_xboole_0(k1_tarski(A_6), k5_enumset1(A_107, B_113, C_108, D_112, E_109, F_110, G_111))=k6_enumset1(A_6, A_107, B_113, C_108, D_112, E_109, F_110, G_111))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_263])).
% 2.85/1.50  tff(c_16, plain, (![G_35, E_33, A_29, F_34, D_32, C_31, B_30]: (k2_xboole_0(k2_enumset1(A_29, B_30, C_31, D_32), k1_enumset1(E_33, F_34, G_35))=k5_enumset1(A_29, B_30, C_31, D_32, E_33, F_34, G_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.85/1.50  tff(c_99, plain, (![B_67, A_66, C_65, D_68, E_69]: (k2_xboole_0(k1_tarski(A_66), k2_enumset1(B_67, C_65, D_68, E_69))=k3_enumset1(A_66, B_67, C_65, D_68, E_69))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.85/1.50  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.85/1.50  tff(c_272, plain, (![C_114, A_116, D_115, B_119, C_117, E_118]: (k2_xboole_0(k1_tarski(A_116), k2_xboole_0(k2_enumset1(B_119, C_114, D_115, E_118), C_117))=k2_xboole_0(k3_enumset1(A_116, B_119, C_114, D_115, E_118), C_117))), inference(superposition, [status(thm), theory('equality')], [c_99, c_2])).
% 2.85/1.50  tff(c_290, plain, (![G_35, E_33, A_29, A_116, F_34, D_32, C_31, B_30]: (k2_xboole_0(k3_enumset1(A_116, A_29, B_30, C_31, D_32), k1_enumset1(E_33, F_34, G_35))=k2_xboole_0(k1_tarski(A_116), k5_enumset1(A_29, B_30, C_31, D_32, E_33, F_34, G_35)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_272])).
% 2.85/1.50  tff(c_629, plain, (![G_35, E_33, A_29, A_116, F_34, D_32, C_31, B_30]: (k2_xboole_0(k3_enumset1(A_116, A_29, B_30, C_31, D_32), k1_enumset1(E_33, F_34, G_35))=k6_enumset1(A_116, A_29, B_30, C_31, D_32, E_33, F_34, G_35))), inference(demodulation, [status(thm), theory('equality')], [c_607, c_290])).
% 2.85/1.50  tff(c_22, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_enumset1('#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.85/1.50  tff(c_632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_629, c_22])).
% 2.85/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.50  
% 2.85/1.50  Inference rules
% 2.85/1.50  ----------------------
% 2.85/1.50  #Ref     : 0
% 2.85/1.50  #Sup     : 157
% 2.85/1.50  #Fact    : 0
% 2.85/1.50  #Define  : 0
% 2.85/1.50  #Split   : 0
% 2.85/1.50  #Chain   : 0
% 2.85/1.50  #Close   : 0
% 2.85/1.50  
% 2.85/1.50  Ordering : KBO
% 2.85/1.50  
% 2.85/1.50  Simplification rules
% 2.85/1.50  ----------------------
% 2.85/1.50  #Subsume      : 0
% 2.85/1.50  #Demod        : 96
% 2.85/1.50  #Tautology    : 90
% 2.85/1.50  #SimpNegUnit  : 0
% 2.85/1.50  #BackRed      : 1
% 2.85/1.50  
% 2.85/1.50  #Partial instantiations: 0
% 2.85/1.50  #Strategies tried      : 1
% 2.85/1.50  
% 2.85/1.50  Timing (in seconds)
% 2.85/1.50  ----------------------
% 2.85/1.50  Preprocessing        : 0.31
% 2.85/1.50  Parsing              : 0.18
% 2.85/1.50  CNF conversion       : 0.02
% 2.85/1.50  Main loop            : 0.36
% 2.85/1.50  Inferencing          : 0.16
% 2.85/1.50  Reduction            : 0.12
% 2.85/1.50  Demodulation         : 0.10
% 2.85/1.50  BG Simplification    : 0.03
% 2.85/1.50  Subsumption          : 0.04
% 2.85/1.50  Abstraction          : 0.03
% 2.85/1.50  MUC search           : 0.00
% 2.85/1.50  Cooper               : 0.00
% 2.85/1.50  Total                : 0.70
% 2.85/1.50  Index Insertion      : 0.00
% 2.85/1.50  Index Deletion       : 0.00
% 2.85/1.50  Index Matching       : 0.00
% 2.85/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
