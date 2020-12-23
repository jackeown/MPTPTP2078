%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:01 EST 2020

% Result     : Theorem 7.26s
% Output     : CNFRefutation 7.26s
% Verified   : 
% Statistics : Number of formulae       :   42 (  44 expanded)
%              Number of leaves         :   28 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(f_47,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

tff(c_22,plain,(
    ! [B_43,A_42,H_49,D_45,G_48,E_46,C_44,F_47] : k2_xboole_0(k1_tarski(A_42),k5_enumset1(B_43,C_44,D_45,E_46,F_47,G_48,H_49)) = k6_enumset1(A_42,B_43,C_44,D_45,E_46,F_47,G_48,H_49) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_35,F_40,B_36,C_37,D_38,E_39,G_41] : k2_xboole_0(k1_tarski(A_35),k4_enumset1(B_36,C_37,D_38,E_39,F_40,G_41)) = k5_enumset1(A_35,B_36,C_37,D_38,E_39,F_40,G_41) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [E_33,A_29,F_34,D_32,C_31,B_30] : k2_xboole_0(k2_enumset1(A_29,B_30,C_31,D_32),k2_tarski(E_33,F_34)) = k4_enumset1(A_29,B_30,C_31,D_32,E_33,F_34) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_112,plain,(
    ! [D_66,B_67,E_65,A_63,C_64] : k2_xboole_0(k1_tarski(A_63),k2_enumset1(B_67,C_64,D_66,E_65)) = k3_enumset1(A_63,B_67,C_64,D_66,E_65) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_8,B_9,C_10] : k2_xboole_0(k2_xboole_0(A_8,B_9),C_10) = k2_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_873,plain,(
    ! [C_137,B_138,C_134,E_136,D_139,A_135] : k2_xboole_0(k1_tarski(A_135),k2_xboole_0(k2_enumset1(B_138,C_134,D_139,E_136),C_137)) = k2_xboole_0(k3_enumset1(A_135,B_138,C_134,D_139,E_136),C_137) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_6])).

tff(c_915,plain,(
    ! [E_33,A_29,F_34,D_32,C_31,B_30,A_135] : k2_xboole_0(k3_enumset1(A_135,A_29,B_30,C_31,D_32),k2_tarski(E_33,F_34)) = k2_xboole_0(k1_tarski(A_135),k4_enumset1(A_29,B_30,C_31,D_32,E_33,F_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_873])).

tff(c_926,plain,(
    ! [E_33,A_29,F_34,D_32,C_31,B_30,A_135] : k2_xboole_0(k3_enumset1(A_135,A_29,B_30,C_31,D_32),k2_tarski(E_33,F_34)) = k5_enumset1(A_135,A_29,B_30,C_31,D_32,E_33,F_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_915])).

tff(c_315,plain,(
    ! [F_84,A_88,E_85,C_83,D_87,B_86] : k2_xboole_0(k1_tarski(A_88),k3_enumset1(B_86,C_83,D_87,E_85,F_84)) = k4_enumset1(A_88,B_86,C_83,D_87,E_85,F_84) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1263,plain,(
    ! [B_155,F_158,C_161,A_159,D_160,E_156,C_157] : k2_xboole_0(k1_tarski(A_159),k2_xboole_0(k3_enumset1(B_155,C_157,D_160,E_156,F_158),C_161)) = k2_xboole_0(k4_enumset1(A_159,B_155,C_157,D_160,E_156,F_158),C_161) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_6])).

tff(c_1305,plain,(
    ! [E_33,A_29,A_159,F_34,D_32,C_31,B_30,A_135] : k2_xboole_0(k4_enumset1(A_159,A_135,A_29,B_30,C_31,D_32),k2_tarski(E_33,F_34)) = k2_xboole_0(k1_tarski(A_159),k5_enumset1(A_135,A_29,B_30,C_31,D_32,E_33,F_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_926,c_1263])).

tff(c_1316,plain,(
    ! [E_33,A_29,A_159,F_34,D_32,C_31,B_30,A_135] : k2_xboole_0(k4_enumset1(A_159,A_135,A_29,B_30,C_31,D_32),k2_tarski(E_33,F_34)) = k6_enumset1(A_159,A_135,A_29,B_30,C_31,D_32,E_33,F_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1305])).

tff(c_24,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1316,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.26/2.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.26/2.46  
% 7.26/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.26/2.47  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 7.26/2.47  
% 7.26/2.47  %Foreground sorts:
% 7.26/2.47  
% 7.26/2.47  
% 7.26/2.47  %Background operators:
% 7.26/2.47  
% 7.26/2.47  
% 7.26/2.47  %Foreground operators:
% 7.26/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.26/2.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.26/2.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.26/2.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.26/2.47  tff('#skF_7', type, '#skF_7': $i).
% 7.26/2.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.26/2.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.26/2.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.26/2.47  tff('#skF_5', type, '#skF_5': $i).
% 7.26/2.47  tff('#skF_6', type, '#skF_6': $i).
% 7.26/2.47  tff('#skF_2', type, '#skF_2': $i).
% 7.26/2.47  tff('#skF_3', type, '#skF_3': $i).
% 7.26/2.47  tff('#skF_1', type, '#skF_1': $i).
% 7.26/2.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.26/2.47  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.26/2.47  tff('#skF_8', type, '#skF_8': $i).
% 7.26/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.26/2.47  tff('#skF_4', type, '#skF_4': $i).
% 7.26/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.26/2.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.26/2.47  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.26/2.47  
% 7.26/2.48  tff(f_47, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_enumset1)).
% 7.26/2.48  tff(f_45, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 7.26/2.48  tff(f_43, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 7.26/2.48  tff(f_39, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_enumset1)).
% 7.26/2.48  tff(f_31, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 7.26/2.48  tff(f_41, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_enumset1)).
% 7.26/2.48  tff(f_50, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_enumset1)).
% 7.26/2.48  tff(c_22, plain, (![B_43, A_42, H_49, D_45, G_48, E_46, C_44, F_47]: (k2_xboole_0(k1_tarski(A_42), k5_enumset1(B_43, C_44, D_45, E_46, F_47, G_48, H_49))=k6_enumset1(A_42, B_43, C_44, D_45, E_46, F_47, G_48, H_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.26/2.48  tff(c_20, plain, (![A_35, F_40, B_36, C_37, D_38, E_39, G_41]: (k2_xboole_0(k1_tarski(A_35), k4_enumset1(B_36, C_37, D_38, E_39, F_40, G_41))=k5_enumset1(A_35, B_36, C_37, D_38, E_39, F_40, G_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.26/2.48  tff(c_18, plain, (![E_33, A_29, F_34, D_32, C_31, B_30]: (k2_xboole_0(k2_enumset1(A_29, B_30, C_31, D_32), k2_tarski(E_33, F_34))=k4_enumset1(A_29, B_30, C_31, D_32, E_33, F_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.26/2.48  tff(c_112, plain, (![D_66, B_67, E_65, A_63, C_64]: (k2_xboole_0(k1_tarski(A_63), k2_enumset1(B_67, C_64, D_66, E_65))=k3_enumset1(A_63, B_67, C_64, D_66, E_65))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.26/2.48  tff(c_6, plain, (![A_8, B_9, C_10]: (k2_xboole_0(k2_xboole_0(A_8, B_9), C_10)=k2_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.26/2.48  tff(c_873, plain, (![C_137, B_138, C_134, E_136, D_139, A_135]: (k2_xboole_0(k1_tarski(A_135), k2_xboole_0(k2_enumset1(B_138, C_134, D_139, E_136), C_137))=k2_xboole_0(k3_enumset1(A_135, B_138, C_134, D_139, E_136), C_137))), inference(superposition, [status(thm), theory('equality')], [c_112, c_6])).
% 7.26/2.48  tff(c_915, plain, (![E_33, A_29, F_34, D_32, C_31, B_30, A_135]: (k2_xboole_0(k3_enumset1(A_135, A_29, B_30, C_31, D_32), k2_tarski(E_33, F_34))=k2_xboole_0(k1_tarski(A_135), k4_enumset1(A_29, B_30, C_31, D_32, E_33, F_34)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_873])).
% 7.26/2.48  tff(c_926, plain, (![E_33, A_29, F_34, D_32, C_31, B_30, A_135]: (k2_xboole_0(k3_enumset1(A_135, A_29, B_30, C_31, D_32), k2_tarski(E_33, F_34))=k5_enumset1(A_135, A_29, B_30, C_31, D_32, E_33, F_34))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_915])).
% 7.26/2.48  tff(c_315, plain, (![F_84, A_88, E_85, C_83, D_87, B_86]: (k2_xboole_0(k1_tarski(A_88), k3_enumset1(B_86, C_83, D_87, E_85, F_84))=k4_enumset1(A_88, B_86, C_83, D_87, E_85, F_84))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.26/2.48  tff(c_1263, plain, (![B_155, F_158, C_161, A_159, D_160, E_156, C_157]: (k2_xboole_0(k1_tarski(A_159), k2_xboole_0(k3_enumset1(B_155, C_157, D_160, E_156, F_158), C_161))=k2_xboole_0(k4_enumset1(A_159, B_155, C_157, D_160, E_156, F_158), C_161))), inference(superposition, [status(thm), theory('equality')], [c_315, c_6])).
% 7.26/2.48  tff(c_1305, plain, (![E_33, A_29, A_159, F_34, D_32, C_31, B_30, A_135]: (k2_xboole_0(k4_enumset1(A_159, A_135, A_29, B_30, C_31, D_32), k2_tarski(E_33, F_34))=k2_xboole_0(k1_tarski(A_159), k5_enumset1(A_135, A_29, B_30, C_31, D_32, E_33, F_34)))), inference(superposition, [status(thm), theory('equality')], [c_926, c_1263])).
% 7.26/2.48  tff(c_1316, plain, (![E_33, A_29, A_159, F_34, D_32, C_31, B_30, A_135]: (k2_xboole_0(k4_enumset1(A_159, A_135, A_29, B_30, C_31, D_32), k2_tarski(E_33, F_34))=k6_enumset1(A_159, A_135, A_29, B_30, C_31, D_32, E_33, F_34))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1305])).
% 7.26/2.48  tff(c_24, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.26/2.48  tff(c_4440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1316, c_24])).
% 7.26/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.26/2.48  
% 7.26/2.48  Inference rules
% 7.26/2.48  ----------------------
% 7.26/2.48  #Ref     : 0
% 7.26/2.48  #Sup     : 1098
% 7.26/2.48  #Fact    : 0
% 7.26/2.48  #Define  : 0
% 7.26/2.48  #Split   : 0
% 7.26/2.48  #Chain   : 0
% 7.26/2.48  #Close   : 0
% 7.26/2.48  
% 7.26/2.48  Ordering : KBO
% 7.26/2.48  
% 7.26/2.48  Simplification rules
% 7.26/2.48  ----------------------
% 7.26/2.48  #Subsume      : 1
% 7.26/2.48  #Demod        : 2000
% 7.26/2.48  #Tautology    : 426
% 7.26/2.48  #SimpNegUnit  : 0
% 7.26/2.48  #BackRed      : 1
% 7.26/2.48  
% 7.26/2.48  #Partial instantiations: 0
% 7.26/2.48  #Strategies tried      : 1
% 7.26/2.48  
% 7.26/2.48  Timing (in seconds)
% 7.26/2.48  ----------------------
% 7.26/2.48  Preprocessing        : 0.31
% 7.26/2.48  Parsing              : 0.18
% 7.26/2.48  CNF conversion       : 0.02
% 7.26/2.48  Main loop            : 1.41
% 7.26/2.48  Inferencing          : 0.50
% 7.26/2.48  Reduction            : 0.64
% 7.26/2.48  Demodulation         : 0.56
% 7.26/2.48  BG Simplification    : 0.09
% 7.26/2.48  Subsumption          : 0.14
% 7.26/2.48  Abstraction          : 0.15
% 7.26/2.48  MUC search           : 0.00
% 7.26/2.48  Cooper               : 0.00
% 7.26/2.48  Total                : 1.75
% 7.26/2.48  Index Insertion      : 0.00
% 7.26/2.48  Index Deletion       : 0.00
% 7.26/2.48  Index Matching       : 0.00
% 7.26/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
