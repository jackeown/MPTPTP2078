%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:00 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :   44 (  51 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   25 (  32 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

tff(c_18,plain,(
    ! [F_41,G_42,D_39,A_36,E_40,H_43,C_38,B_37] : k2_xboole_0(k3_enumset1(A_36,B_37,C_38,D_39,E_40),k1_enumset1(F_41,G_42,H_43)) = k6_enumset1(A_36,B_37,C_38,D_39,E_40,F_41,G_42,H_43) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_27,B_28,C_29] : k2_xboole_0(k1_tarski(A_27),k2_tarski(B_28,C_29)) = k1_enumset1(A_27,B_28,C_29) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,F_35] : k2_xboole_0(k1_enumset1(A_30,B_31,C_32),k1_enumset1(D_33,E_34,F_35)) = k4_enumset1(A_30,B_31,C_32,D_33,E_34,F_35) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_25,B_26] : k2_xboole_0(k1_tarski(A_25),k1_tarski(B_26)) = k2_tarski(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_40,plain,(
    ! [A_49,B_50,C_51] : k2_xboole_0(k2_xboole_0(A_49,B_50),C_51) = k2_xboole_0(A_49,k2_xboole_0(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    ! [A_56,B_57,C_58] : k2_xboole_0(k1_tarski(A_56),k2_xboole_0(k1_tarski(B_57),C_58)) = k2_xboole_0(k2_tarski(A_56,B_57),C_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_40])).

tff(c_96,plain,(
    ! [A_56,A_25,B_26] : k2_xboole_0(k2_tarski(A_56,A_25),k1_tarski(B_26)) = k2_xboole_0(k1_tarski(A_56),k2_tarski(A_25,B_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_75])).

tff(c_101,plain,(
    ! [A_56,A_25,B_26] : k2_xboole_0(k2_tarski(A_56,A_25),k1_tarski(B_26)) = k1_enumset1(A_56,A_25,B_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_96])).

tff(c_102,plain,(
    ! [B_59,E_61,A_60,D_62,C_63] : k2_xboole_0(k1_enumset1(A_60,B_59,C_63),k2_tarski(D_62,E_61)) = k3_enumset1(A_60,B_59,C_63,D_62,E_61) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7] : k2_xboole_0(k2_xboole_0(A_5,B_6),C_7) = k2_xboole_0(A_5,k2_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_410,plain,(
    ! [C_143,A_144,C_145,E_142,B_141,D_146] : k2_xboole_0(k1_enumset1(A_144,B_141,C_143),k2_xboole_0(k2_tarski(D_146,E_142),C_145)) = k2_xboole_0(k3_enumset1(A_144,B_141,C_143,D_146,E_142),C_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_4])).

tff(c_434,plain,(
    ! [C_143,A_25,A_56,A_144,B_141,B_26] : k2_xboole_0(k3_enumset1(A_144,B_141,C_143,A_56,A_25),k1_tarski(B_26)) = k2_xboole_0(k1_enumset1(A_144,B_141,C_143),k1_enumset1(A_56,A_25,B_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_410])).

tff(c_443,plain,(
    ! [B_150,B_152,A_148,C_149,A_147,A_151] : k2_xboole_0(k3_enumset1(A_148,B_152,C_149,A_151,A_147),k1_tarski(B_150)) = k4_enumset1(A_148,B_152,C_149,A_151,A_147,B_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_434])).

tff(c_691,plain,(
    ! [C_209,B_210,A_206,C_205,A_204,A_208,B_207] : k2_xboole_0(k3_enumset1(A_206,B_207,C_205,A_208,A_204),k2_xboole_0(k1_tarski(B_210),C_209)) = k2_xboole_0(k4_enumset1(A_206,B_207,C_205,A_208,A_204,B_210),C_209) ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_4])).

tff(c_724,plain,(
    ! [C_29,B_28,A_206,A_27,C_205,A_204,A_208,B_207] : k2_xboole_0(k4_enumset1(A_206,B_207,C_205,A_208,A_204,A_27),k2_tarski(B_28,C_29)) = k2_xboole_0(k3_enumset1(A_206,B_207,C_205,A_208,A_204),k1_enumset1(A_27,B_28,C_29)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_691])).

tff(c_731,plain,(
    ! [C_29,B_28,A_206,A_27,C_205,A_204,A_208,B_207] : k2_xboole_0(k4_enumset1(A_206,B_207,C_205,A_208,A_204,A_27),k2_tarski(B_28,C_29)) = k6_enumset1(A_206,B_207,C_205,A_208,A_204,A_27,B_28,C_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_724])).

tff(c_20,plain,(
    k2_xboole_0(k4_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_994,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:35:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.61  
% 3.31/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.61  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.31/1.61  
% 3.31/1.61  %Foreground sorts:
% 3.31/1.61  
% 3.31/1.61  
% 3.31/1.61  %Background operators:
% 3.31/1.61  
% 3.31/1.61  
% 3.31/1.61  %Foreground operators:
% 3.31/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.31/1.61  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.31/1.61  tff('#skF_7', type, '#skF_7': $i).
% 3.31/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.31/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.31/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.31/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.31/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.31/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.31/1.61  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.31/1.61  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.31/1.61  tff('#skF_8', type, '#skF_8': $i).
% 3.31/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.31/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.31/1.61  
% 3.66/1.62  tff(f_43, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 3.66/1.62  tff(f_39, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 3.66/1.62  tff(f_41, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_enumset1)).
% 3.66/1.62  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.66/1.62  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.66/1.62  tff(f_33, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 3.66/1.62  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 3.66/1.62  tff(c_18, plain, (![F_41, G_42, D_39, A_36, E_40, H_43, C_38, B_37]: (k2_xboole_0(k3_enumset1(A_36, B_37, C_38, D_39, E_40), k1_enumset1(F_41, G_42, H_43))=k6_enumset1(A_36, B_37, C_38, D_39, E_40, F_41, G_42, H_43))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.66/1.62  tff(c_14, plain, (![A_27, B_28, C_29]: (k2_xboole_0(k1_tarski(A_27), k2_tarski(B_28, C_29))=k1_enumset1(A_27, B_28, C_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.66/1.62  tff(c_16, plain, (![D_33, A_30, C_32, B_31, E_34, F_35]: (k2_xboole_0(k1_enumset1(A_30, B_31, C_32), k1_enumset1(D_33, E_34, F_35))=k4_enumset1(A_30, B_31, C_32, D_33, E_34, F_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.66/1.62  tff(c_12, plain, (![A_25, B_26]: (k2_xboole_0(k1_tarski(A_25), k1_tarski(B_26))=k2_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.66/1.62  tff(c_40, plain, (![A_49, B_50, C_51]: (k2_xboole_0(k2_xboole_0(A_49, B_50), C_51)=k2_xboole_0(A_49, k2_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.66/1.62  tff(c_75, plain, (![A_56, B_57, C_58]: (k2_xboole_0(k1_tarski(A_56), k2_xboole_0(k1_tarski(B_57), C_58))=k2_xboole_0(k2_tarski(A_56, B_57), C_58))), inference(superposition, [status(thm), theory('equality')], [c_12, c_40])).
% 3.66/1.62  tff(c_96, plain, (![A_56, A_25, B_26]: (k2_xboole_0(k2_tarski(A_56, A_25), k1_tarski(B_26))=k2_xboole_0(k1_tarski(A_56), k2_tarski(A_25, B_26)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_75])).
% 3.66/1.62  tff(c_101, plain, (![A_56, A_25, B_26]: (k2_xboole_0(k2_tarski(A_56, A_25), k1_tarski(B_26))=k1_enumset1(A_56, A_25, B_26))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_96])).
% 3.66/1.62  tff(c_102, plain, (![B_59, E_61, A_60, D_62, C_63]: (k2_xboole_0(k1_enumset1(A_60, B_59, C_63), k2_tarski(D_62, E_61))=k3_enumset1(A_60, B_59, C_63, D_62, E_61))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.66/1.62  tff(c_4, plain, (![A_5, B_6, C_7]: (k2_xboole_0(k2_xboole_0(A_5, B_6), C_7)=k2_xboole_0(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.66/1.62  tff(c_410, plain, (![C_143, A_144, C_145, E_142, B_141, D_146]: (k2_xboole_0(k1_enumset1(A_144, B_141, C_143), k2_xboole_0(k2_tarski(D_146, E_142), C_145))=k2_xboole_0(k3_enumset1(A_144, B_141, C_143, D_146, E_142), C_145))), inference(superposition, [status(thm), theory('equality')], [c_102, c_4])).
% 3.66/1.62  tff(c_434, plain, (![C_143, A_25, A_56, A_144, B_141, B_26]: (k2_xboole_0(k3_enumset1(A_144, B_141, C_143, A_56, A_25), k1_tarski(B_26))=k2_xboole_0(k1_enumset1(A_144, B_141, C_143), k1_enumset1(A_56, A_25, B_26)))), inference(superposition, [status(thm), theory('equality')], [c_101, c_410])).
% 3.66/1.62  tff(c_443, plain, (![B_150, B_152, A_148, C_149, A_147, A_151]: (k2_xboole_0(k3_enumset1(A_148, B_152, C_149, A_151, A_147), k1_tarski(B_150))=k4_enumset1(A_148, B_152, C_149, A_151, A_147, B_150))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_434])).
% 3.66/1.62  tff(c_691, plain, (![C_209, B_210, A_206, C_205, A_204, A_208, B_207]: (k2_xboole_0(k3_enumset1(A_206, B_207, C_205, A_208, A_204), k2_xboole_0(k1_tarski(B_210), C_209))=k2_xboole_0(k4_enumset1(A_206, B_207, C_205, A_208, A_204, B_210), C_209))), inference(superposition, [status(thm), theory('equality')], [c_443, c_4])).
% 3.66/1.62  tff(c_724, plain, (![C_29, B_28, A_206, A_27, C_205, A_204, A_208, B_207]: (k2_xboole_0(k4_enumset1(A_206, B_207, C_205, A_208, A_204, A_27), k2_tarski(B_28, C_29))=k2_xboole_0(k3_enumset1(A_206, B_207, C_205, A_208, A_204), k1_enumset1(A_27, B_28, C_29)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_691])).
% 3.66/1.62  tff(c_731, plain, (![C_29, B_28, A_206, A_27, C_205, A_204, A_208, B_207]: (k2_xboole_0(k4_enumset1(A_206, B_207, C_205, A_208, A_204, A_27), k2_tarski(B_28, C_29))=k6_enumset1(A_206, B_207, C_205, A_208, A_204, A_27, B_28, C_29))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_724])).
% 3.66/1.62  tff(c_20, plain, (k2_xboole_0(k4_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.66/1.62  tff(c_994, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_731, c_20])).
% 3.66/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.66/1.62  
% 3.66/1.62  Inference rules
% 3.66/1.62  ----------------------
% 3.66/1.62  #Ref     : 0
% 3.66/1.62  #Sup     : 251
% 3.66/1.62  #Fact    : 0
% 3.66/1.62  #Define  : 0
% 3.66/1.62  #Split   : 0
% 3.66/1.62  #Chain   : 0
% 3.66/1.62  #Close   : 0
% 3.66/1.62  
% 3.66/1.62  Ordering : KBO
% 3.66/1.62  
% 3.66/1.62  Simplification rules
% 3.66/1.62  ----------------------
% 3.66/1.62  #Subsume      : 0
% 3.66/1.62  #Demod        : 150
% 3.66/1.62  #Tautology    : 129
% 3.66/1.62  #SimpNegUnit  : 0
% 3.66/1.62  #BackRed      : 6
% 3.66/1.62  
% 3.66/1.62  #Partial instantiations: 0
% 3.66/1.62  #Strategies tried      : 1
% 3.66/1.62  
% 3.66/1.62  Timing (in seconds)
% 3.66/1.62  ----------------------
% 3.66/1.63  Preprocessing        : 0.31
% 3.66/1.63  Parsing              : 0.17
% 3.66/1.63  CNF conversion       : 0.02
% 3.66/1.63  Main loop            : 0.50
% 3.66/1.63  Inferencing          : 0.22
% 3.66/1.63  Reduction            : 0.18
% 3.66/1.63  Demodulation         : 0.14
% 3.66/1.63  BG Simplification    : 0.04
% 3.66/1.63  Subsumption          : 0.05
% 3.66/1.63  Abstraction          : 0.04
% 3.66/1.63  MUC search           : 0.00
% 3.66/1.63  Cooper               : 0.00
% 3.66/1.63  Total                : 0.84
% 3.66/1.63  Index Insertion      : 0.00
% 3.66/1.63  Index Deletion       : 0.00
% 3.66/1.63  Index Matching       : 0.00
% 3.66/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
