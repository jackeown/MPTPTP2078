%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:58 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   44 (  45 expanded)
%              Number of leaves         :   29 (  30 expanded)
%              Depth                    :    7
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

tff(f_41,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_enumset1(A,B,C),k3_enumset1(D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_enumset1)).

tff(c_16,plain,(
    ! [G_35,H_36,E_33,A_29,F_34,D_32,C_31,B_30] : k2_xboole_0(k1_tarski(A_29),k5_enumset1(B_30,C_31,D_32,E_33,F_34,G_35,H_36)) = k6_enumset1(A_29,B_30,C_31,D_32,E_33,F_34,G_35,H_36) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [G_28,E_26,F_27,A_22,B_23,D_25,C_24] : k2_xboole_0(k1_tarski(A_22),k4_enumset1(B_23,C_24,D_25,E_26,F_27,G_28)) = k5_enumset1(A_22,B_23,C_24,D_25,E_26,F_27,G_28) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_204,plain,(
    ! [F_74,B_75,A_77,C_79,D_78,E_76] : k2_xboole_0(k1_tarski(A_77),k3_enumset1(B_75,C_79,D_78,E_76,F_74)) = k4_enumset1(A_77,B_75,C_79,D_78,E_76,F_74) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),k1_tarski(B_7)) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_37,plain,(
    ! [A_41,B_42,C_43] : k2_xboole_0(k2_xboole_0(A_41,B_42),C_43) = k2_xboole_0(A_41,k2_xboole_0(B_42,C_43)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    ! [A_6,B_7,C_43] : k2_xboole_0(k1_tarski(A_6),k2_xboole_0(k1_tarski(B_7),C_43)) = k2_xboole_0(k2_tarski(A_6,B_7),C_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_37])).

tff(c_213,plain,(
    ! [F_74,B_75,A_77,C_79,D_78,E_76,A_6] : k2_xboole_0(k2_tarski(A_6,A_77),k3_enumset1(B_75,C_79,D_78,E_76,F_74)) = k2_xboole_0(k1_tarski(A_6),k4_enumset1(A_77,B_75,C_79,D_78,E_76,F_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_52])).

tff(c_431,plain,(
    ! [B_140,D_138,A_139,C_141,A_136,E_142,F_137] : k2_xboole_0(k2_tarski(A_139,A_136),k3_enumset1(B_140,C_141,D_138,E_142,F_137)) = k5_enumset1(A_139,A_136,B_140,C_141,D_138,E_142,F_137) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_213])).

tff(c_57,plain,(
    ! [A_44,B_45,C_46] : k2_xboole_0(k1_tarski(A_44),k2_tarski(B_45,C_46)) = k1_enumset1(A_44,B_45,C_46) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_63,plain,(
    ! [A_44,B_45,C_46,C_3] : k2_xboole_0(k1_tarski(A_44),k2_xboole_0(k2_tarski(B_45,C_46),C_3)) = k2_xboole_0(k1_enumset1(A_44,B_45,C_46),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_2])).

tff(c_440,plain,(
    ! [B_140,D_138,A_139,C_141,A_44,A_136,E_142,F_137] : k2_xboole_0(k1_enumset1(A_44,A_139,A_136),k3_enumset1(B_140,C_141,D_138,E_142,F_137)) = k2_xboole_0(k1_tarski(A_44),k5_enumset1(A_139,A_136,B_140,C_141,D_138,E_142,F_137)) ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_63])).

tff(c_448,plain,(
    ! [B_140,D_138,A_139,C_141,A_44,A_136,E_142,F_137] : k2_xboole_0(k1_enumset1(A_44,A_139,A_136),k3_enumset1(B_140,C_141,D_138,E_142,F_137)) = k6_enumset1(A_44,A_139,A_136,B_140,C_141,D_138,E_142,F_137) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_440])).

tff(c_18,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k3_enumset1('#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:59:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.37  
% 2.51/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.38  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.51/1.38  
% 2.51/1.38  %Foreground sorts:
% 2.51/1.38  
% 2.51/1.38  
% 2.51/1.38  %Background operators:
% 2.51/1.38  
% 2.51/1.38  
% 2.51/1.38  %Foreground operators:
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.51/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.51/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.51/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.51/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.51/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.51/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.51/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.51/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.51/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.51/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.51/1.38  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.51/1.38  tff('#skF_8', type, '#skF_8': $i).
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.51/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.51/1.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.51/1.38  
% 2.86/1.39  tff(f_41, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 2.86/1.39  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 2.86/1.39  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 2.86/1.39  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.86/1.39  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.86/1.39  tff(f_33, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.86/1.39  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_enumset1(A, B, C), k3_enumset1(D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_enumset1)).
% 2.86/1.39  tff(c_16, plain, (![G_35, H_36, E_33, A_29, F_34, D_32, C_31, B_30]: (k2_xboole_0(k1_tarski(A_29), k5_enumset1(B_30, C_31, D_32, E_33, F_34, G_35, H_36))=k6_enumset1(A_29, B_30, C_31, D_32, E_33, F_34, G_35, H_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.86/1.39  tff(c_14, plain, (![G_28, E_26, F_27, A_22, B_23, D_25, C_24]: (k2_xboole_0(k1_tarski(A_22), k4_enumset1(B_23, C_24, D_25, E_26, F_27, G_28))=k5_enumset1(A_22, B_23, C_24, D_25, E_26, F_27, G_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.86/1.39  tff(c_204, plain, (![F_74, B_75, A_77, C_79, D_78, E_76]: (k2_xboole_0(k1_tarski(A_77), k3_enumset1(B_75, C_79, D_78, E_76, F_74))=k4_enumset1(A_77, B_75, C_79, D_78, E_76, F_74))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.86/1.39  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(B_7))=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.86/1.39  tff(c_37, plain, (![A_41, B_42, C_43]: (k2_xboole_0(k2_xboole_0(A_41, B_42), C_43)=k2_xboole_0(A_41, k2_xboole_0(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.86/1.39  tff(c_52, plain, (![A_6, B_7, C_43]: (k2_xboole_0(k1_tarski(A_6), k2_xboole_0(k1_tarski(B_7), C_43))=k2_xboole_0(k2_tarski(A_6, B_7), C_43))), inference(superposition, [status(thm), theory('equality')], [c_6, c_37])).
% 2.86/1.39  tff(c_213, plain, (![F_74, B_75, A_77, C_79, D_78, E_76, A_6]: (k2_xboole_0(k2_tarski(A_6, A_77), k3_enumset1(B_75, C_79, D_78, E_76, F_74))=k2_xboole_0(k1_tarski(A_6), k4_enumset1(A_77, B_75, C_79, D_78, E_76, F_74)))), inference(superposition, [status(thm), theory('equality')], [c_204, c_52])).
% 2.86/1.39  tff(c_431, plain, (![B_140, D_138, A_139, C_141, A_136, E_142, F_137]: (k2_xboole_0(k2_tarski(A_139, A_136), k3_enumset1(B_140, C_141, D_138, E_142, F_137))=k5_enumset1(A_139, A_136, B_140, C_141, D_138, E_142, F_137))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_213])).
% 2.86/1.39  tff(c_57, plain, (![A_44, B_45, C_46]: (k2_xboole_0(k1_tarski(A_44), k2_tarski(B_45, C_46))=k1_enumset1(A_44, B_45, C_46))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.86/1.39  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.86/1.39  tff(c_63, plain, (![A_44, B_45, C_46, C_3]: (k2_xboole_0(k1_tarski(A_44), k2_xboole_0(k2_tarski(B_45, C_46), C_3))=k2_xboole_0(k1_enumset1(A_44, B_45, C_46), C_3))), inference(superposition, [status(thm), theory('equality')], [c_57, c_2])).
% 2.86/1.39  tff(c_440, plain, (![B_140, D_138, A_139, C_141, A_44, A_136, E_142, F_137]: (k2_xboole_0(k1_enumset1(A_44, A_139, A_136), k3_enumset1(B_140, C_141, D_138, E_142, F_137))=k2_xboole_0(k1_tarski(A_44), k5_enumset1(A_139, A_136, B_140, C_141, D_138, E_142, F_137)))), inference(superposition, [status(thm), theory('equality')], [c_431, c_63])).
% 2.86/1.39  tff(c_448, plain, (![B_140, D_138, A_139, C_141, A_44, A_136, E_142, F_137]: (k2_xboole_0(k1_enumset1(A_44, A_139, A_136), k3_enumset1(B_140, C_141, D_138, E_142, F_137))=k6_enumset1(A_44, A_139, A_136, B_140, C_141, D_138, E_142, F_137))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_440])).
% 2.86/1.39  tff(c_18, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k3_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.86/1.39  tff(c_510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_448, c_18])).
% 2.86/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.39  
% 2.86/1.39  Inference rules
% 2.86/1.39  ----------------------
% 2.86/1.39  #Ref     : 0
% 2.86/1.39  #Sup     : 125
% 2.86/1.39  #Fact    : 0
% 2.86/1.39  #Define  : 0
% 2.86/1.39  #Split   : 0
% 2.86/1.39  #Chain   : 0
% 2.86/1.39  #Close   : 0
% 2.86/1.39  
% 2.86/1.39  Ordering : KBO
% 2.86/1.39  
% 2.86/1.39  Simplification rules
% 2.86/1.39  ----------------------
% 2.86/1.39  #Subsume      : 0
% 2.86/1.39  #Demod        : 85
% 2.86/1.39  #Tautology    : 74
% 2.86/1.39  #SimpNegUnit  : 0
% 2.86/1.39  #BackRed      : 1
% 2.86/1.39  
% 2.86/1.39  #Partial instantiations: 0
% 2.86/1.39  #Strategies tried      : 1
% 2.86/1.39  
% 2.86/1.39  Timing (in seconds)
% 2.86/1.39  ----------------------
% 2.86/1.39  Preprocessing        : 0.30
% 2.86/1.39  Parsing              : 0.16
% 2.86/1.39  CNF conversion       : 0.02
% 2.86/1.39  Main loop            : 0.33
% 2.86/1.39  Inferencing          : 0.15
% 2.86/1.39  Reduction            : 0.11
% 2.86/1.39  Demodulation         : 0.09
% 2.86/1.39  BG Simplification    : 0.02
% 2.86/1.39  Subsumption          : 0.04
% 2.86/1.39  Abstraction          : 0.03
% 2.86/1.39  MUC search           : 0.00
% 2.86/1.39  Cooper               : 0.00
% 2.86/1.39  Total                : 0.65
% 2.86/1.39  Index Insertion      : 0.00
% 2.86/1.39  Index Deletion       : 0.00
% 2.86/1.39  Index Matching       : 0.00
% 2.86/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
