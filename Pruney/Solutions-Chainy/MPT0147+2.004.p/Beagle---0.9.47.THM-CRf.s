%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:56 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   53 (  70 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :   33 (  50 expanded)
%              Number of equality atoms :   32 (  49 expanded)
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

tff(f_47,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_tarski(A,B),k2_enumset1(C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

tff(c_22,plain,(
    ! [A_46,E_50,B_47,H_53,C_48,D_49,G_52,F_51] : k2_xboole_0(k1_tarski(A_46),k5_enumset1(B_47,C_48,D_49,E_50,F_51,G_52,H_53)) = k6_enumset1(A_46,B_47,C_48,D_49,E_50,F_51,G_52,H_53) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [E_43,G_45,F_44,D_42,A_39,C_41,B_40] : k2_xboole_0(k3_enumset1(A_39,B_40,C_41,D_42,E_43),k2_tarski(F_44,G_45)) = k5_enumset1(A_39,B_40,C_41,D_42,E_43,F_44,G_45) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [D_36,F_38,E_37,A_33,B_34,C_35] : k2_xboole_0(k2_tarski(A_33,B_34),k2_enumset1(C_35,D_36,E_37,F_38)) = k4_enumset1(A_33,B_34,C_35,D_36,E_37,F_38) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_24,B_25,C_26,D_27] : k2_xboole_0(k1_tarski(A_24),k1_enumset1(B_25,C_26,D_27)) = k2_enumset1(A_24,B_25,C_26,D_27) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_21,B_22,C_23] : k2_xboole_0(k1_tarski(A_21),k2_tarski(B_22,C_23)) = k1_enumset1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_19,B_20] : k2_xboole_0(k1_tarski(A_19),k1_tarski(B_20)) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    ! [A_59,B_60,C_61] : k2_xboole_0(k2_xboole_0(A_59,B_60),C_61) = k2_xboole_0(A_59,k2_xboole_0(B_60,C_61)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_79,plain,(
    ! [A_66,B_67,C_68] : k2_xboole_0(k1_tarski(A_66),k2_xboole_0(k1_tarski(B_67),C_68)) = k2_xboole_0(k2_tarski(A_66,B_67),C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_44])).

tff(c_100,plain,(
    ! [A_66,A_21,B_22,C_23] : k2_xboole_0(k2_tarski(A_66,A_21),k2_tarski(B_22,C_23)) = k2_xboole_0(k1_tarski(A_66),k1_enumset1(A_21,B_22,C_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_79])).

tff(c_107,plain,(
    ! [A_66,A_21,B_22,C_23] : k2_xboole_0(k2_tarski(A_66,A_21),k2_tarski(B_22,C_23)) = k2_enumset1(A_66,A_21,B_22,C_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_100])).

tff(c_136,plain,(
    ! [A_77,A_78,B_79,C_80] : k2_xboole_0(k2_tarski(A_77,A_78),k2_tarski(B_79,C_80)) = k2_enumset1(A_77,A_78,B_79,C_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_100])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7] : k2_xboole_0(k2_xboole_0(A_5,B_6),C_7) = k2_xboole_0(A_5,k2_xboole_0(B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_330,plain,(
    ! [A_133,A_132,B_136,C_134,C_135] : k2_xboole_0(k2_tarski(A_132,A_133),k2_xboole_0(k2_tarski(B_136,C_134),C_135)) = k2_xboole_0(k2_enumset1(A_132,A_133,B_136,C_134),C_135) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_4])).

tff(c_360,plain,(
    ! [A_21,B_22,C_23,A_133,A_66,A_132] : k2_xboole_0(k2_enumset1(A_132,A_133,A_66,A_21),k2_tarski(B_22,C_23)) = k2_xboole_0(k2_tarski(A_132,A_133),k2_enumset1(A_66,A_21,B_22,C_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_330])).

tff(c_367,plain,(
    ! [A_21,B_22,C_23,A_133,A_66,A_132] : k2_xboole_0(k2_enumset1(A_132,A_133,A_66,A_21),k2_tarski(B_22,C_23)) = k4_enumset1(A_132,A_133,A_66,A_21,B_22,C_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_360])).

tff(c_109,plain,(
    ! [D_73,A_70,B_72,E_69,C_71] : k2_xboole_0(k1_tarski(A_70),k2_enumset1(B_72,C_71,D_73,E_69)) = k3_enumset1(A_70,B_72,C_71,D_73,E_69) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_490,plain,(
    ! [C_171,E_173,D_168,A_169,C_172,B_170] : k2_xboole_0(k1_tarski(A_169),k2_xboole_0(k2_enumset1(B_170,C_172,D_168,E_173),C_171)) = k2_xboole_0(k3_enumset1(A_169,B_170,C_172,D_168,E_173),C_171) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_4])).

tff(c_511,plain,(
    ! [A_21,B_22,C_23,A_133,A_66,A_132,A_169] : k2_xboole_0(k3_enumset1(A_169,A_132,A_133,A_66,A_21),k2_tarski(B_22,C_23)) = k2_xboole_0(k1_tarski(A_169),k4_enumset1(A_132,A_133,A_66,A_21,B_22,C_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_490])).

tff(c_711,plain,(
    ! [B_219,A_218,A_213,C_217,A_214,A_216,A_215] : k2_xboole_0(k1_tarski(A_213),k4_enumset1(A_214,A_215,A_218,A_216,B_219,C_217)) = k5_enumset1(A_213,A_214,A_215,A_218,A_216,B_219,C_217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_511])).

tff(c_62,plain,(
    ! [A_19,B_20,C_61] : k2_xboole_0(k1_tarski(A_19),k2_xboole_0(k1_tarski(B_20),C_61)) = k2_xboole_0(k2_tarski(A_19,B_20),C_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_44])).

tff(c_726,plain,(
    ! [A_19,B_219,A_218,A_213,C_217,A_214,A_216,A_215] : k2_xboole_0(k2_tarski(A_19,A_213),k4_enumset1(A_214,A_215,A_218,A_216,B_219,C_217)) = k2_xboole_0(k1_tarski(A_19),k5_enumset1(A_213,A_214,A_215,A_218,A_216,B_219,C_217)) ),
    inference(superposition,[status(thm),theory(equality)],[c_711,c_62])).

tff(c_734,plain,(
    ! [A_19,B_219,A_218,A_213,C_217,A_214,A_216,A_215] : k2_xboole_0(k2_tarski(A_19,A_213),k4_enumset1(A_214,A_215,A_218,A_216,B_219,C_217)) = k6_enumset1(A_19,A_213,A_214,A_215,A_218,A_216,B_219,C_217) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_726])).

tff(c_24,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k4_enumset1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1049,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_734,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:49:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.54  
% 3.44/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.54  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.44/1.54  
% 3.44/1.54  %Foreground sorts:
% 3.44/1.54  
% 3.44/1.54  
% 3.44/1.54  %Background operators:
% 3.44/1.54  
% 3.44/1.54  
% 3.44/1.54  %Foreground operators:
% 3.44/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.44/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.44/1.54  tff('#skF_7', type, '#skF_7': $i).
% 3.44/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.44/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.44/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.44/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.44/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.44/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.44/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.44/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.44/1.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.54  tff('#skF_8', type, '#skF_8': $i).
% 3.44/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.44/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.44/1.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.54  
% 3.44/1.55  tff(f_47, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 3.44/1.55  tff(f_45, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 3.44/1.55  tff(f_43, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_tarski(A, B), k2_enumset1(C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_enumset1)).
% 3.44/1.55  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 3.44/1.55  tff(f_37, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 3.44/1.55  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.44/1.55  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.44/1.55  tff(f_41, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 3.44/1.55  tff(f_50, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_enumset1)).
% 3.44/1.55  tff(c_22, plain, (![A_46, E_50, B_47, H_53, C_48, D_49, G_52, F_51]: (k2_xboole_0(k1_tarski(A_46), k5_enumset1(B_47, C_48, D_49, E_50, F_51, G_52, H_53))=k6_enumset1(A_46, B_47, C_48, D_49, E_50, F_51, G_52, H_53))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.44/1.55  tff(c_20, plain, (![E_43, G_45, F_44, D_42, A_39, C_41, B_40]: (k2_xboole_0(k3_enumset1(A_39, B_40, C_41, D_42, E_43), k2_tarski(F_44, G_45))=k5_enumset1(A_39, B_40, C_41, D_42, E_43, F_44, G_45))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.44/1.55  tff(c_18, plain, (![D_36, F_38, E_37, A_33, B_34, C_35]: (k2_xboole_0(k2_tarski(A_33, B_34), k2_enumset1(C_35, D_36, E_37, F_38))=k4_enumset1(A_33, B_34, C_35, D_36, E_37, F_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.55  tff(c_14, plain, (![A_24, B_25, C_26, D_27]: (k2_xboole_0(k1_tarski(A_24), k1_enumset1(B_25, C_26, D_27))=k2_enumset1(A_24, B_25, C_26, D_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.44/1.55  tff(c_12, plain, (![A_21, B_22, C_23]: (k2_xboole_0(k1_tarski(A_21), k2_tarski(B_22, C_23))=k1_enumset1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.44/1.55  tff(c_10, plain, (![A_19, B_20]: (k2_xboole_0(k1_tarski(A_19), k1_tarski(B_20))=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.44/1.55  tff(c_44, plain, (![A_59, B_60, C_61]: (k2_xboole_0(k2_xboole_0(A_59, B_60), C_61)=k2_xboole_0(A_59, k2_xboole_0(B_60, C_61)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.44/1.55  tff(c_79, plain, (![A_66, B_67, C_68]: (k2_xboole_0(k1_tarski(A_66), k2_xboole_0(k1_tarski(B_67), C_68))=k2_xboole_0(k2_tarski(A_66, B_67), C_68))), inference(superposition, [status(thm), theory('equality')], [c_10, c_44])).
% 3.44/1.55  tff(c_100, plain, (![A_66, A_21, B_22, C_23]: (k2_xboole_0(k2_tarski(A_66, A_21), k2_tarski(B_22, C_23))=k2_xboole_0(k1_tarski(A_66), k1_enumset1(A_21, B_22, C_23)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_79])).
% 3.44/1.55  tff(c_107, plain, (![A_66, A_21, B_22, C_23]: (k2_xboole_0(k2_tarski(A_66, A_21), k2_tarski(B_22, C_23))=k2_enumset1(A_66, A_21, B_22, C_23))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_100])).
% 3.44/1.55  tff(c_136, plain, (![A_77, A_78, B_79, C_80]: (k2_xboole_0(k2_tarski(A_77, A_78), k2_tarski(B_79, C_80))=k2_enumset1(A_77, A_78, B_79, C_80))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_100])).
% 3.44/1.55  tff(c_4, plain, (![A_5, B_6, C_7]: (k2_xboole_0(k2_xboole_0(A_5, B_6), C_7)=k2_xboole_0(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.44/1.55  tff(c_330, plain, (![A_133, A_132, B_136, C_134, C_135]: (k2_xboole_0(k2_tarski(A_132, A_133), k2_xboole_0(k2_tarski(B_136, C_134), C_135))=k2_xboole_0(k2_enumset1(A_132, A_133, B_136, C_134), C_135))), inference(superposition, [status(thm), theory('equality')], [c_136, c_4])).
% 3.44/1.55  tff(c_360, plain, (![A_21, B_22, C_23, A_133, A_66, A_132]: (k2_xboole_0(k2_enumset1(A_132, A_133, A_66, A_21), k2_tarski(B_22, C_23))=k2_xboole_0(k2_tarski(A_132, A_133), k2_enumset1(A_66, A_21, B_22, C_23)))), inference(superposition, [status(thm), theory('equality')], [c_107, c_330])).
% 3.44/1.55  tff(c_367, plain, (![A_21, B_22, C_23, A_133, A_66, A_132]: (k2_xboole_0(k2_enumset1(A_132, A_133, A_66, A_21), k2_tarski(B_22, C_23))=k4_enumset1(A_132, A_133, A_66, A_21, B_22, C_23))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_360])).
% 3.44/1.55  tff(c_109, plain, (![D_73, A_70, B_72, E_69, C_71]: (k2_xboole_0(k1_tarski(A_70), k2_enumset1(B_72, C_71, D_73, E_69))=k3_enumset1(A_70, B_72, C_71, D_73, E_69))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.44/1.55  tff(c_490, plain, (![C_171, E_173, D_168, A_169, C_172, B_170]: (k2_xboole_0(k1_tarski(A_169), k2_xboole_0(k2_enumset1(B_170, C_172, D_168, E_173), C_171))=k2_xboole_0(k3_enumset1(A_169, B_170, C_172, D_168, E_173), C_171))), inference(superposition, [status(thm), theory('equality')], [c_109, c_4])).
% 3.44/1.55  tff(c_511, plain, (![A_21, B_22, C_23, A_133, A_66, A_132, A_169]: (k2_xboole_0(k3_enumset1(A_169, A_132, A_133, A_66, A_21), k2_tarski(B_22, C_23))=k2_xboole_0(k1_tarski(A_169), k4_enumset1(A_132, A_133, A_66, A_21, B_22, C_23)))), inference(superposition, [status(thm), theory('equality')], [c_367, c_490])).
% 3.44/1.55  tff(c_711, plain, (![B_219, A_218, A_213, C_217, A_214, A_216, A_215]: (k2_xboole_0(k1_tarski(A_213), k4_enumset1(A_214, A_215, A_218, A_216, B_219, C_217))=k5_enumset1(A_213, A_214, A_215, A_218, A_216, B_219, C_217))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_511])).
% 3.44/1.55  tff(c_62, plain, (![A_19, B_20, C_61]: (k2_xboole_0(k1_tarski(A_19), k2_xboole_0(k1_tarski(B_20), C_61))=k2_xboole_0(k2_tarski(A_19, B_20), C_61))), inference(superposition, [status(thm), theory('equality')], [c_10, c_44])).
% 3.44/1.55  tff(c_726, plain, (![A_19, B_219, A_218, A_213, C_217, A_214, A_216, A_215]: (k2_xboole_0(k2_tarski(A_19, A_213), k4_enumset1(A_214, A_215, A_218, A_216, B_219, C_217))=k2_xboole_0(k1_tarski(A_19), k5_enumset1(A_213, A_214, A_215, A_218, A_216, B_219, C_217)))), inference(superposition, [status(thm), theory('equality')], [c_711, c_62])).
% 3.44/1.55  tff(c_734, plain, (![A_19, B_219, A_218, A_213, C_217, A_214, A_216, A_215]: (k2_xboole_0(k2_tarski(A_19, A_213), k4_enumset1(A_214, A_215, A_218, A_216, B_219, C_217))=k6_enumset1(A_19, A_213, A_214, A_215, A_218, A_216, B_219, C_217))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_726])).
% 3.44/1.55  tff(c_24, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k4_enumset1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.44/1.55  tff(c_1049, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_734, c_24])).
% 3.44/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.55  
% 3.44/1.55  Inference rules
% 3.44/1.55  ----------------------
% 3.44/1.55  #Ref     : 0
% 3.44/1.55  #Sup     : 274
% 3.44/1.55  #Fact    : 0
% 3.44/1.55  #Define  : 0
% 3.44/1.55  #Split   : 0
% 3.44/1.55  #Chain   : 0
% 3.44/1.55  #Close   : 0
% 3.44/1.55  
% 3.44/1.55  Ordering : KBO
% 3.44/1.55  
% 3.44/1.55  Simplification rules
% 3.44/1.55  ----------------------
% 3.44/1.55  #Subsume      : 0
% 3.44/1.55  #Demod        : 147
% 3.44/1.55  #Tautology    : 135
% 3.44/1.55  #SimpNegUnit  : 0
% 3.44/1.55  #BackRed      : 1
% 3.44/1.55  
% 3.44/1.55  #Partial instantiations: 0
% 3.44/1.55  #Strategies tried      : 1
% 3.44/1.55  
% 3.44/1.55  Timing (in seconds)
% 3.44/1.55  ----------------------
% 3.44/1.55  Preprocessing        : 0.29
% 3.44/1.55  Parsing              : 0.17
% 3.44/1.55  CNF conversion       : 0.02
% 3.44/1.55  Main loop            : 0.48
% 3.44/1.55  Inferencing          : 0.21
% 3.44/1.55  Reduction            : 0.16
% 3.44/1.55  Demodulation         : 0.14
% 3.44/1.55  BG Simplification    : 0.04
% 3.44/1.55  Subsumption          : 0.05
% 3.44/1.55  Abstraction          : 0.04
% 3.44/1.55  MUC search           : 0.00
% 3.44/1.55  Cooper               : 0.00
% 3.44/1.55  Total                : 0.80
% 3.44/1.55  Index Insertion      : 0.00
% 3.44/1.55  Index Deletion       : 0.00
% 3.44/1.55  Index Matching       : 0.00
% 3.44/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
