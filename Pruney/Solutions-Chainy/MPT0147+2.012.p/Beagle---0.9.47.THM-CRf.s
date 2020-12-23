%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:57 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  52 expanded)
%              Number of leaves         :   28 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   25 (  32 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

tff(c_16,plain,(
    ! [A_31,C_33,B_32,H_38,F_36,E_35,G_37,D_34] : k2_xboole_0(k1_tarski(A_31),k5_enumset1(B_32,C_33,D_34,E_35,F_36,G_37,H_38)) = k6_enumset1(A_31,B_32,C_33,D_34,E_35,F_36,G_37,H_38) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_24,B_25,F_29,D_27,C_26,E_28,G_30] : k2_xboole_0(k1_enumset1(A_24,B_25,C_26),k2_enumset1(D_27,E_28,F_29,G_30)) = k5_enumset1(A_24,B_25,C_26,D_27,E_28,F_29,G_30) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [E_22,D_21,F_23,A_18,C_20,B_19] : k2_xboole_0(k1_tarski(A_18),k3_enumset1(B_19,C_20,D_21,E_22,F_23)) = k4_enumset1(A_18,B_19,C_20,D_21,E_22,F_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_102,plain,(
    ! [A_57,C_58,D_54,E_56,B_55] : k2_xboole_0(k1_tarski(A_57),k2_enumset1(B_55,C_58,D_54,E_56)) = k3_enumset1(A_57,B_55,C_58,D_54,E_56) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),k1_tarski(B_5)) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [A_44,B_45,C_46] : k2_xboole_0(k2_xboole_0(A_44,B_45),C_46) = k2_xboole_0(A_44,k2_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_55,plain,(
    ! [A_4,B_5,C_46] : k2_xboole_0(k1_tarski(A_4),k2_xboole_0(k1_tarski(B_5),C_46)) = k2_xboole_0(k2_tarski(A_4,B_5),C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_37])).

tff(c_108,plain,(
    ! [A_57,A_4,C_58,D_54,E_56,B_55] : k2_xboole_0(k2_tarski(A_4,A_57),k2_enumset1(B_55,C_58,D_54,E_56)) = k2_xboole_0(k1_tarski(A_4),k3_enumset1(A_57,B_55,C_58,D_54,E_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_55])).

tff(c_485,plain,(
    ! [C_155,B_156,A_158,E_153,A_157,D_154] : k2_xboole_0(k2_tarski(A_158,A_157),k2_enumset1(B_156,C_155,D_154,E_153)) = k4_enumset1(A_158,A_157,B_156,C_155,D_154,E_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_108])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k2_xboole_0(k1_tarski(A_6),k2_tarski(B_7,C_8)) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ! [A_6,B_7,C_8,C_46] : k2_xboole_0(k1_tarski(A_6),k2_xboole_0(k2_tarski(B_7,C_8),C_46)) = k2_xboole_0(k1_enumset1(A_6,B_7,C_8),C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_37])).

tff(c_494,plain,(
    ! [C_155,B_156,A_158,E_153,A_157,D_154,A_6] : k2_xboole_0(k1_enumset1(A_6,A_158,A_157),k2_enumset1(B_156,C_155,D_154,E_153)) = k2_xboole_0(k1_tarski(A_6),k4_enumset1(A_158,A_157,B_156,C_155,D_154,E_153)) ),
    inference(superposition,[status(thm),theory(equality)],[c_485,c_52])).

tff(c_540,plain,(
    ! [B_166,D_170,E_165,A_171,A_169,C_167,A_168] : k2_xboole_0(k1_tarski(A_171),k4_enumset1(A_168,A_169,B_166,C_167,D_170,E_165)) = k5_enumset1(A_171,A_168,A_169,B_166,C_167,D_170,E_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_494])).

tff(c_552,plain,(
    ! [B_166,D_170,E_165,A_4,A_171,A_169,C_167,A_168] : k2_xboole_0(k2_tarski(A_4,A_171),k4_enumset1(A_168,A_169,B_166,C_167,D_170,E_165)) = k2_xboole_0(k1_tarski(A_4),k5_enumset1(A_171,A_168,A_169,B_166,C_167,D_170,E_165)) ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_55])).

tff(c_560,plain,(
    ! [B_166,D_170,E_165,A_4,A_171,A_169,C_167,A_168] : k2_xboole_0(k2_tarski(A_4,A_171),k4_enumset1(A_168,A_169,B_166,C_167,D_170,E_165)) = k6_enumset1(A_4,A_171,A_168,A_169,B_166,C_167,D_170,E_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_552])).

tff(c_18,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k4_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_830,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:58:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.46  
% 2.84/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.46  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.84/1.46  
% 2.84/1.46  %Foreground sorts:
% 2.84/1.46  
% 2.84/1.46  
% 2.84/1.46  %Background operators:
% 2.84/1.46  
% 2.84/1.46  
% 2.84/1.46  %Foreground operators:
% 2.84/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.84/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.84/1.46  tff('#skF_7', type, '#skF_7': $i).
% 2.84/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.84/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.84/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.84/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.84/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.84/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.84/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.84/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.46  tff('#skF_8', type, '#skF_8': $i).
% 2.84/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.84/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.84/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.46  
% 3.21/1.47  tff(f_41, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 3.21/1.47  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 3.21/1.47  tff(f_37, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 3.21/1.47  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 3.21/1.47  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.21/1.47  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.21/1.47  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 3.21/1.47  tff(f_44, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_enumset1)).
% 3.21/1.47  tff(c_16, plain, (![A_31, C_33, B_32, H_38, F_36, E_35, G_37, D_34]: (k2_xboole_0(k1_tarski(A_31), k5_enumset1(B_32, C_33, D_34, E_35, F_36, G_37, H_38))=k6_enumset1(A_31, B_32, C_33, D_34, E_35, F_36, G_37, H_38))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.21/1.47  tff(c_14, plain, (![A_24, B_25, F_29, D_27, C_26, E_28, G_30]: (k2_xboole_0(k1_enumset1(A_24, B_25, C_26), k2_enumset1(D_27, E_28, F_29, G_30))=k5_enumset1(A_24, B_25, C_26, D_27, E_28, F_29, G_30))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.21/1.47  tff(c_12, plain, (![E_22, D_21, F_23, A_18, C_20, B_19]: (k2_xboole_0(k1_tarski(A_18), k3_enumset1(B_19, C_20, D_21, E_22, F_23))=k4_enumset1(A_18, B_19, C_20, D_21, E_22, F_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.21/1.47  tff(c_102, plain, (![A_57, C_58, D_54, E_56, B_55]: (k2_xboole_0(k1_tarski(A_57), k2_enumset1(B_55, C_58, D_54, E_56))=k3_enumset1(A_57, B_55, C_58, D_54, E_56))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.47  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(B_5))=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.21/1.47  tff(c_37, plain, (![A_44, B_45, C_46]: (k2_xboole_0(k2_xboole_0(A_44, B_45), C_46)=k2_xboole_0(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.21/1.47  tff(c_55, plain, (![A_4, B_5, C_46]: (k2_xboole_0(k1_tarski(A_4), k2_xboole_0(k1_tarski(B_5), C_46))=k2_xboole_0(k2_tarski(A_4, B_5), C_46))), inference(superposition, [status(thm), theory('equality')], [c_4, c_37])).
% 3.21/1.47  tff(c_108, plain, (![A_57, A_4, C_58, D_54, E_56, B_55]: (k2_xboole_0(k2_tarski(A_4, A_57), k2_enumset1(B_55, C_58, D_54, E_56))=k2_xboole_0(k1_tarski(A_4), k3_enumset1(A_57, B_55, C_58, D_54, E_56)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_55])).
% 3.21/1.47  tff(c_485, plain, (![C_155, B_156, A_158, E_153, A_157, D_154]: (k2_xboole_0(k2_tarski(A_158, A_157), k2_enumset1(B_156, C_155, D_154, E_153))=k4_enumset1(A_158, A_157, B_156, C_155, D_154, E_153))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_108])).
% 3.21/1.47  tff(c_6, plain, (![A_6, B_7, C_8]: (k2_xboole_0(k1_tarski(A_6), k2_tarski(B_7, C_8))=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.21/1.47  tff(c_52, plain, (![A_6, B_7, C_8, C_46]: (k2_xboole_0(k1_tarski(A_6), k2_xboole_0(k2_tarski(B_7, C_8), C_46))=k2_xboole_0(k1_enumset1(A_6, B_7, C_8), C_46))), inference(superposition, [status(thm), theory('equality')], [c_6, c_37])).
% 3.21/1.47  tff(c_494, plain, (![C_155, B_156, A_158, E_153, A_157, D_154, A_6]: (k2_xboole_0(k1_enumset1(A_6, A_158, A_157), k2_enumset1(B_156, C_155, D_154, E_153))=k2_xboole_0(k1_tarski(A_6), k4_enumset1(A_158, A_157, B_156, C_155, D_154, E_153)))), inference(superposition, [status(thm), theory('equality')], [c_485, c_52])).
% 3.21/1.47  tff(c_540, plain, (![B_166, D_170, E_165, A_171, A_169, C_167, A_168]: (k2_xboole_0(k1_tarski(A_171), k4_enumset1(A_168, A_169, B_166, C_167, D_170, E_165))=k5_enumset1(A_171, A_168, A_169, B_166, C_167, D_170, E_165))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_494])).
% 3.21/1.47  tff(c_552, plain, (![B_166, D_170, E_165, A_4, A_171, A_169, C_167, A_168]: (k2_xboole_0(k2_tarski(A_4, A_171), k4_enumset1(A_168, A_169, B_166, C_167, D_170, E_165))=k2_xboole_0(k1_tarski(A_4), k5_enumset1(A_171, A_168, A_169, B_166, C_167, D_170, E_165)))), inference(superposition, [status(thm), theory('equality')], [c_540, c_55])).
% 3.21/1.47  tff(c_560, plain, (![B_166, D_170, E_165, A_4, A_171, A_169, C_167, A_168]: (k2_xboole_0(k2_tarski(A_4, A_171), k4_enumset1(A_168, A_169, B_166, C_167, D_170, E_165))=k6_enumset1(A_4, A_171, A_168, A_169, B_166, C_167, D_170, E_165))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_552])).
% 3.21/1.47  tff(c_18, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k4_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.21/1.47  tff(c_830, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_560, c_18])).
% 3.21/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.47  
% 3.21/1.47  Inference rules
% 3.21/1.47  ----------------------
% 3.21/1.47  #Ref     : 0
% 3.21/1.47  #Sup     : 214
% 3.21/1.47  #Fact    : 0
% 3.21/1.47  #Define  : 0
% 3.21/1.47  #Split   : 0
% 3.21/1.47  #Chain   : 0
% 3.21/1.47  #Close   : 0
% 3.21/1.47  
% 3.21/1.47  Ordering : KBO
% 3.21/1.47  
% 3.21/1.47  Simplification rules
% 3.21/1.47  ----------------------
% 3.21/1.47  #Subsume      : 0
% 3.21/1.47  #Demod        : 110
% 3.21/1.47  #Tautology    : 108
% 3.21/1.47  #SimpNegUnit  : 0
% 3.21/1.47  #BackRed      : 1
% 3.21/1.47  
% 3.21/1.47  #Partial instantiations: 0
% 3.21/1.47  #Strategies tried      : 1
% 3.21/1.47  
% 3.21/1.47  Timing (in seconds)
% 3.21/1.47  ----------------------
% 3.21/1.48  Preprocessing        : 0.29
% 3.21/1.48  Parsing              : 0.16
% 3.21/1.48  CNF conversion       : 0.02
% 3.21/1.48  Main loop            : 0.42
% 3.21/1.48  Inferencing          : 0.20
% 3.21/1.48  Reduction            : 0.14
% 3.21/1.48  Demodulation         : 0.11
% 3.21/1.48  BG Simplification    : 0.03
% 3.21/1.48  Subsumption          : 0.04
% 3.21/1.48  Abstraction          : 0.04
% 3.21/1.48  MUC search           : 0.00
% 3.21/1.48  Cooper               : 0.00
% 3.21/1.48  Total                : 0.73
% 3.21/1.48  Index Insertion      : 0.00
% 3.21/1.48  Index Deletion       : 0.00
% 3.21/1.48  Index Matching       : 0.00
% 3.21/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
