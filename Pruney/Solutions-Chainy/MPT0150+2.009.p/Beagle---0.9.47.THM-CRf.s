%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:00 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   50 (  60 expanded)
%              Number of leaves         :   27 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :   31 (  41 expanded)
%              Number of equality atoms :   30 (  40 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_tarski(A),k5_enumset1(B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

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

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

tff(c_14,plain,(
    ! [A_25,G_31,F_30,E_29,H_32,C_27,D_28,B_26] : k2_xboole_0(k1_tarski(A_25),k5_enumset1(B_26,C_27,D_28,E_29,F_30,G_31,H_32)) = k6_enumset1(A_25,B_26,C_27,D_28,E_29,F_30,G_31,H_32) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [E_22,G_24,D_21,F_23,A_18,C_20,B_19] : k2_xboole_0(k1_enumset1(A_18,B_19,C_20),k2_enumset1(D_21,E_22,F_23,G_24)) = k5_enumset1(A_18,B_19,C_20,D_21,E_22,F_23,G_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11,D_12] : k2_xboole_0(k1_tarski(A_9),k1_enumset1(B_10,C_11,D_12)) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_6,B_7,C_8] : k2_xboole_0(k1_tarski(A_6),k2_tarski(B_7,C_8)) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),k1_tarski(B_5)) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ! [A_35,B_36,C_37] : k2_xboole_0(k2_xboole_0(A_35,B_36),C_37) = k2_xboole_0(A_35,k2_xboole_0(B_36,C_37)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_70,plain,(
    ! [A_45,B_46,C_47] : k2_xboole_0(k1_tarski(A_45),k2_xboole_0(k1_tarski(B_46),C_47)) = k2_xboole_0(k2_tarski(A_45,B_46),C_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_26])).

tff(c_94,plain,(
    ! [A_45,A_4,B_5] : k2_xboole_0(k2_tarski(A_45,A_4),k1_tarski(B_5)) = k2_xboole_0(k1_tarski(A_45),k2_tarski(A_4,B_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_70])).

tff(c_99,plain,(
    ! [A_45,A_4,B_5] : k2_xboole_0(k2_tarski(A_45,A_4),k1_tarski(B_5)) = k1_enumset1(A_45,A_4,B_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_94])).

tff(c_46,plain,(
    ! [A_38,B_39,C_40] : k2_xboole_0(k1_tarski(A_38),k2_tarski(B_39,C_40)) = k1_enumset1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_139,plain,(
    ! [A_60,B_61,C_62,C_63] : k2_xboole_0(k1_tarski(A_60),k2_xboole_0(k2_tarski(B_61,C_62),C_63)) = k2_xboole_0(k1_enumset1(A_60,B_61,C_62),C_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_2])).

tff(c_157,plain,(
    ! [A_60,A_45,A_4,B_5] : k2_xboole_0(k1_enumset1(A_60,A_45,A_4),k1_tarski(B_5)) = k2_xboole_0(k1_tarski(A_60),k1_enumset1(A_45,A_4,B_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_139])).

tff(c_163,plain,(
    ! [A_64,A_65,A_66,B_67] : k2_xboole_0(k1_enumset1(A_64,A_65,A_66),k1_tarski(B_67)) = k2_enumset1(A_64,A_65,A_66,B_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_157])).

tff(c_347,plain,(
    ! [A_113,A_112,C_114,A_115,B_116] : k2_xboole_0(k1_enumset1(A_115,A_113,A_112),k2_xboole_0(k1_tarski(B_116),C_114)) = k2_xboole_0(k2_enumset1(A_115,A_113,A_112,B_116),C_114) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_2])).

tff(c_377,plain,(
    ! [A_113,A_112,C_11,B_10,A_115,D_12,A_9] : k2_xboole_0(k2_enumset1(A_115,A_113,A_112,A_9),k1_enumset1(B_10,C_11,D_12)) = k2_xboole_0(k1_enumset1(A_115,A_113,A_112),k2_enumset1(A_9,B_10,C_11,D_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_347])).

tff(c_689,plain,(
    ! [A_195,A_191,D_192,C_190,A_194,B_189,A_193] : k2_xboole_0(k2_enumset1(A_194,A_191,A_195,A_193),k1_enumset1(B_189,C_190,D_192)) = k5_enumset1(A_194,A_191,A_195,A_193,B_189,C_190,D_192) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_377])).

tff(c_100,plain,(
    ! [B_49,E_50,D_48,C_52,A_51] : k2_xboole_0(k1_tarski(A_51),k2_enumset1(B_49,C_52,D_48,E_50)) = k3_enumset1(A_51,B_49,C_52,D_48,E_50) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_109,plain,(
    ! [B_49,E_50,D_48,C_3,C_52,A_51] : k2_xboole_0(k1_tarski(A_51),k2_xboole_0(k2_enumset1(B_49,C_52,D_48,E_50),C_3)) = k2_xboole_0(k3_enumset1(A_51,B_49,C_52,D_48,E_50),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_2])).

tff(c_698,plain,(
    ! [A_195,A_191,D_192,C_190,A_194,B_189,A_193,A_51] : k2_xboole_0(k3_enumset1(A_51,A_194,A_191,A_195,A_193),k1_enumset1(B_189,C_190,D_192)) = k2_xboole_0(k1_tarski(A_51),k5_enumset1(A_194,A_191,A_195,A_193,B_189,C_190,D_192)) ),
    inference(superposition,[status(thm),theory(equality)],[c_689,c_109])).

tff(c_706,plain,(
    ! [A_195,A_191,D_192,C_190,A_194,B_189,A_193,A_51] : k2_xboole_0(k3_enumset1(A_51,A_194,A_191,A_195,A_193),k1_enumset1(B_189,C_190,D_192)) = k6_enumset1(A_51,A_194,A_191,A_195,A_193,B_189,C_190,D_192) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_698])).

tff(c_16,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_enumset1('#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_773,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:30:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.48  
% 3.08/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.49  %$ k6_enumset1 > k5_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.08/1.49  
% 3.08/1.49  %Foreground sorts:
% 3.08/1.49  
% 3.08/1.49  
% 3.08/1.49  %Background operators:
% 3.08/1.49  
% 3.08/1.49  
% 3.08/1.49  %Foreground operators:
% 3.08/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.08/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.08/1.49  tff('#skF_7', type, '#skF_7': $i).
% 3.08/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.08/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.08/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.08/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.08/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.08/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.08/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.08/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.08/1.49  tff('#skF_8', type, '#skF_8': $i).
% 3.08/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.08/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.08/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.08/1.49  
% 3.08/1.50  tff(f_39, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_tarski(A), k5_enumset1(B, C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_enumset1)).
% 3.08/1.50  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 3.08/1.50  tff(f_33, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_enumset1)).
% 3.08/1.50  tff(f_31, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_enumset1)).
% 3.08/1.50  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.08/1.50  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.08/1.50  tff(f_35, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 3.08/1.50  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 3.08/1.50  tff(c_14, plain, (![A_25, G_31, F_30, E_29, H_32, C_27, D_28, B_26]: (k2_xboole_0(k1_tarski(A_25), k5_enumset1(B_26, C_27, D_28, E_29, F_30, G_31, H_32))=k6_enumset1(A_25, B_26, C_27, D_28, E_29, F_30, G_31, H_32))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.08/1.50  tff(c_12, plain, (![E_22, G_24, D_21, F_23, A_18, C_20, B_19]: (k2_xboole_0(k1_enumset1(A_18, B_19, C_20), k2_enumset1(D_21, E_22, F_23, G_24))=k5_enumset1(A_18, B_19, C_20, D_21, E_22, F_23, G_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.08/1.50  tff(c_8, plain, (![A_9, B_10, C_11, D_12]: (k2_xboole_0(k1_tarski(A_9), k1_enumset1(B_10, C_11, D_12))=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.08/1.50  tff(c_6, plain, (![A_6, B_7, C_8]: (k2_xboole_0(k1_tarski(A_6), k2_tarski(B_7, C_8))=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.08/1.50  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(B_5))=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.08/1.50  tff(c_26, plain, (![A_35, B_36, C_37]: (k2_xboole_0(k2_xboole_0(A_35, B_36), C_37)=k2_xboole_0(A_35, k2_xboole_0(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.08/1.50  tff(c_70, plain, (![A_45, B_46, C_47]: (k2_xboole_0(k1_tarski(A_45), k2_xboole_0(k1_tarski(B_46), C_47))=k2_xboole_0(k2_tarski(A_45, B_46), C_47))), inference(superposition, [status(thm), theory('equality')], [c_4, c_26])).
% 3.08/1.50  tff(c_94, plain, (![A_45, A_4, B_5]: (k2_xboole_0(k2_tarski(A_45, A_4), k1_tarski(B_5))=k2_xboole_0(k1_tarski(A_45), k2_tarski(A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_70])).
% 3.08/1.50  tff(c_99, plain, (![A_45, A_4, B_5]: (k2_xboole_0(k2_tarski(A_45, A_4), k1_tarski(B_5))=k1_enumset1(A_45, A_4, B_5))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_94])).
% 3.08/1.50  tff(c_46, plain, (![A_38, B_39, C_40]: (k2_xboole_0(k1_tarski(A_38), k2_tarski(B_39, C_40))=k1_enumset1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.08/1.50  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.08/1.50  tff(c_139, plain, (![A_60, B_61, C_62, C_63]: (k2_xboole_0(k1_tarski(A_60), k2_xboole_0(k2_tarski(B_61, C_62), C_63))=k2_xboole_0(k1_enumset1(A_60, B_61, C_62), C_63))), inference(superposition, [status(thm), theory('equality')], [c_46, c_2])).
% 3.08/1.50  tff(c_157, plain, (![A_60, A_45, A_4, B_5]: (k2_xboole_0(k1_enumset1(A_60, A_45, A_4), k1_tarski(B_5))=k2_xboole_0(k1_tarski(A_60), k1_enumset1(A_45, A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_99, c_139])).
% 3.08/1.50  tff(c_163, plain, (![A_64, A_65, A_66, B_67]: (k2_xboole_0(k1_enumset1(A_64, A_65, A_66), k1_tarski(B_67))=k2_enumset1(A_64, A_65, A_66, B_67))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_157])).
% 3.08/1.50  tff(c_347, plain, (![A_113, A_112, C_114, A_115, B_116]: (k2_xboole_0(k1_enumset1(A_115, A_113, A_112), k2_xboole_0(k1_tarski(B_116), C_114))=k2_xboole_0(k2_enumset1(A_115, A_113, A_112, B_116), C_114))), inference(superposition, [status(thm), theory('equality')], [c_163, c_2])).
% 3.08/1.50  tff(c_377, plain, (![A_113, A_112, C_11, B_10, A_115, D_12, A_9]: (k2_xboole_0(k2_enumset1(A_115, A_113, A_112, A_9), k1_enumset1(B_10, C_11, D_12))=k2_xboole_0(k1_enumset1(A_115, A_113, A_112), k2_enumset1(A_9, B_10, C_11, D_12)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_347])).
% 3.08/1.50  tff(c_689, plain, (![A_195, A_191, D_192, C_190, A_194, B_189, A_193]: (k2_xboole_0(k2_enumset1(A_194, A_191, A_195, A_193), k1_enumset1(B_189, C_190, D_192))=k5_enumset1(A_194, A_191, A_195, A_193, B_189, C_190, D_192))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_377])).
% 3.08/1.50  tff(c_100, plain, (![B_49, E_50, D_48, C_52, A_51]: (k2_xboole_0(k1_tarski(A_51), k2_enumset1(B_49, C_52, D_48, E_50))=k3_enumset1(A_51, B_49, C_52, D_48, E_50))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.08/1.50  tff(c_109, plain, (![B_49, E_50, D_48, C_3, C_52, A_51]: (k2_xboole_0(k1_tarski(A_51), k2_xboole_0(k2_enumset1(B_49, C_52, D_48, E_50), C_3))=k2_xboole_0(k3_enumset1(A_51, B_49, C_52, D_48, E_50), C_3))), inference(superposition, [status(thm), theory('equality')], [c_100, c_2])).
% 3.08/1.50  tff(c_698, plain, (![A_195, A_191, D_192, C_190, A_194, B_189, A_193, A_51]: (k2_xboole_0(k3_enumset1(A_51, A_194, A_191, A_195, A_193), k1_enumset1(B_189, C_190, D_192))=k2_xboole_0(k1_tarski(A_51), k5_enumset1(A_194, A_191, A_195, A_193, B_189, C_190, D_192)))), inference(superposition, [status(thm), theory('equality')], [c_689, c_109])).
% 3.08/1.50  tff(c_706, plain, (![A_195, A_191, D_192, C_190, A_194, B_189, A_193, A_51]: (k2_xboole_0(k3_enumset1(A_51, A_194, A_191, A_195, A_193), k1_enumset1(B_189, C_190, D_192))=k6_enumset1(A_51, A_194, A_191, A_195, A_193, B_189, C_190, D_192))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_698])).
% 3.08/1.50  tff(c_16, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_enumset1('#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.08/1.50  tff(c_773, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_706, c_16])).
% 3.08/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.50  
% 3.08/1.50  Inference rules
% 3.08/1.50  ----------------------
% 3.08/1.50  #Ref     : 0
% 3.08/1.50  #Sup     : 195
% 3.08/1.50  #Fact    : 0
% 3.08/1.50  #Define  : 0
% 3.08/1.50  #Split   : 0
% 3.08/1.50  #Chain   : 0
% 3.08/1.50  #Close   : 0
% 3.08/1.50  
% 3.08/1.50  Ordering : KBO
% 3.08/1.50  
% 3.08/1.50  Simplification rules
% 3.08/1.50  ----------------------
% 3.08/1.50  #Subsume      : 0
% 3.08/1.50  #Demod        : 121
% 3.08/1.50  #Tautology    : 109
% 3.08/1.50  #SimpNegUnit  : 0
% 3.08/1.50  #BackRed      : 1
% 3.08/1.50  
% 3.08/1.50  #Partial instantiations: 0
% 3.08/1.50  #Strategies tried      : 1
% 3.08/1.50  
% 3.08/1.50  Timing (in seconds)
% 3.08/1.50  ----------------------
% 3.08/1.50  Preprocessing        : 0.26
% 3.08/1.50  Parsing              : 0.15
% 3.08/1.50  CNF conversion       : 0.02
% 3.08/1.50  Main loop            : 0.41
% 3.08/1.50  Inferencing          : 0.19
% 3.08/1.50  Reduction            : 0.14
% 3.08/1.50  Demodulation         : 0.11
% 3.08/1.50  BG Simplification    : 0.03
% 3.08/1.50  Subsumption          : 0.04
% 3.08/1.50  Abstraction          : 0.03
% 3.08/1.50  MUC search           : 0.00
% 3.08/1.50  Cooper               : 0.00
% 3.08/1.50  Total                : 0.71
% 3.08/1.50  Index Insertion      : 0.00
% 3.08/1.50  Index Deletion       : 0.00
% 3.08/1.50  Index Matching       : 0.00
% 3.08/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
