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
% DateTime   : Thu Dec  3 09:45:49 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   46 (  53 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   25 (  32 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_tarski(A),k3_enumset1(B,C,D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_tarski(A),k2_enumset1(B,C,D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

tff(c_18,plain,(
    ! [C_30,G_34,E_32,D_31,B_29,F_33,A_28] : k2_xboole_0(k1_tarski(A_28),k4_enumset1(B_29,C_30,D_31,E_32,F_33,G_34)) = k5_enumset1(A_28,B_29,C_30,D_31,E_32,F_33,G_34) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [E_26,F_27,A_22,B_23,D_25,C_24] : k2_xboole_0(k1_tarski(A_22),k3_enumset1(B_23,C_24,D_25,E_26,F_27)) = k4_enumset1(A_22,B_23,C_24,D_25,E_26,F_27) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_146,plain,(
    ! [B_63,E_65,D_64,C_61,A_62] : k2_xboole_0(k1_tarski(A_62),k2_enumset1(B_63,C_61,D_64,E_65)) = k3_enumset1(A_62,B_63,C_61,D_64,E_65) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_12,B_13] : k2_xboole_0(k1_tarski(A_12),k1_tarski(B_13)) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    ! [A_41,B_42,C_43] : k2_xboole_0(k2_xboole_0(A_41,B_42),C_43) = k2_xboole_0(A_41,k2_xboole_0(B_42,C_43)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    ! [A_12,B_13,C_43] : k2_xboole_0(k1_tarski(A_12),k2_xboole_0(k1_tarski(B_13),C_43)) = k2_xboole_0(k2_tarski(A_12,B_13),C_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_48])).

tff(c_152,plain,(
    ! [B_63,E_65,D_64,C_61,A_12,A_62] : k2_xboole_0(k2_tarski(A_12,A_62),k2_enumset1(B_63,C_61,D_64,E_65)) = k2_xboole_0(k1_tarski(A_12),k3_enumset1(A_62,B_63,C_61,D_64,E_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_63])).

tff(c_476,plain,(
    ! [E_143,D_142,A_139,B_141,C_138,A_140] : k2_xboole_0(k2_tarski(A_139,A_140),k2_enumset1(B_141,C_138,D_142,E_143)) = k4_enumset1(A_139,A_140,B_141,C_138,D_142,E_143) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_152])).

tff(c_12,plain,(
    ! [A_14,B_15,C_16] : k2_xboole_0(k2_tarski(A_14,B_15),k1_tarski(C_16)) = k1_enumset1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_92,plain,(
    ! [A_51,B_52,C_53] : k2_xboole_0(k1_tarski(A_51),k2_xboole_0(k1_tarski(B_52),C_53)) = k2_xboole_0(k2_tarski(A_51,B_52),C_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_48])).

tff(c_110,plain,(
    ! [A_51,A_12,B_13] : k2_xboole_0(k2_tarski(A_51,A_12),k1_tarski(B_13)) = k2_xboole_0(k1_tarski(A_51),k2_tarski(A_12,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_92])).

tff(c_115,plain,(
    ! [A_54,A_55,B_56] : k2_xboole_0(k1_tarski(A_54),k2_tarski(A_55,B_56)) = k1_enumset1(A_54,A_55,B_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_110])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k2_xboole_0(A_3,B_4),C_5) = k2_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_124,plain,(
    ! [A_54,A_55,B_56,C_5] : k2_xboole_0(k1_tarski(A_54),k2_xboole_0(k2_tarski(A_55,B_56),C_5)) = k2_xboole_0(k1_enumset1(A_54,A_55,B_56),C_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_4])).

tff(c_485,plain,(
    ! [E_143,D_142,A_139,B_141,C_138,A_140,A_54] : k2_xboole_0(k1_enumset1(A_54,A_139,A_140),k2_enumset1(B_141,C_138,D_142,E_143)) = k2_xboole_0(k1_tarski(A_54),k4_enumset1(A_139,A_140,B_141,C_138,D_142,E_143)) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_124])).

tff(c_493,plain,(
    ! [E_143,D_142,A_139,B_141,C_138,A_140,A_54] : k2_xboole_0(k1_enumset1(A_54,A_139,A_140),k2_enumset1(B_141,C_138,D_142,E_143)) = k5_enumset1(A_54,A_139,A_140,B_141,C_138,D_142,E_143) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_485])).

tff(c_20,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k2_enumset1('#skF_4','#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_555,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:39:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.42  
% 2.79/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.42  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.79/1.42  
% 2.79/1.42  %Foreground sorts:
% 2.79/1.42  
% 2.79/1.42  
% 2.79/1.42  %Background operators:
% 2.79/1.42  
% 2.79/1.42  
% 2.79/1.42  %Foreground operators:
% 2.79/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.79/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.79/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.79/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.79/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.79/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.79/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.79/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.79/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.79/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.79/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.79/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.79/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.79/1.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.79/1.42  
% 2.79/1.43  tff(f_43, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_enumset1)).
% 2.79/1.43  tff(f_41, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_tarski(A), k3_enumset1(B, C, D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_enumset1)).
% 2.79/1.43  tff(f_39, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_tarski(A), k2_enumset1(B, C, D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 2.79/1.43  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.79/1.43  tff(f_29, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 2.79/1.43  tff(f_37, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_enumset1)).
% 2.79/1.43  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_enumset1)).
% 2.79/1.43  tff(c_18, plain, (![C_30, G_34, E_32, D_31, B_29, F_33, A_28]: (k2_xboole_0(k1_tarski(A_28), k4_enumset1(B_29, C_30, D_31, E_32, F_33, G_34))=k5_enumset1(A_28, B_29, C_30, D_31, E_32, F_33, G_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.79/1.43  tff(c_16, plain, (![E_26, F_27, A_22, B_23, D_25, C_24]: (k2_xboole_0(k1_tarski(A_22), k3_enumset1(B_23, C_24, D_25, E_26, F_27))=k4_enumset1(A_22, B_23, C_24, D_25, E_26, F_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.79/1.43  tff(c_146, plain, (![B_63, E_65, D_64, C_61, A_62]: (k2_xboole_0(k1_tarski(A_62), k2_enumset1(B_63, C_61, D_64, E_65))=k3_enumset1(A_62, B_63, C_61, D_64, E_65))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.79/1.43  tff(c_10, plain, (![A_12, B_13]: (k2_xboole_0(k1_tarski(A_12), k1_tarski(B_13))=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.79/1.43  tff(c_48, plain, (![A_41, B_42, C_43]: (k2_xboole_0(k2_xboole_0(A_41, B_42), C_43)=k2_xboole_0(A_41, k2_xboole_0(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.79/1.43  tff(c_63, plain, (![A_12, B_13, C_43]: (k2_xboole_0(k1_tarski(A_12), k2_xboole_0(k1_tarski(B_13), C_43))=k2_xboole_0(k2_tarski(A_12, B_13), C_43))), inference(superposition, [status(thm), theory('equality')], [c_10, c_48])).
% 2.79/1.43  tff(c_152, plain, (![B_63, E_65, D_64, C_61, A_12, A_62]: (k2_xboole_0(k2_tarski(A_12, A_62), k2_enumset1(B_63, C_61, D_64, E_65))=k2_xboole_0(k1_tarski(A_12), k3_enumset1(A_62, B_63, C_61, D_64, E_65)))), inference(superposition, [status(thm), theory('equality')], [c_146, c_63])).
% 2.79/1.43  tff(c_476, plain, (![E_143, D_142, A_139, B_141, C_138, A_140]: (k2_xboole_0(k2_tarski(A_139, A_140), k2_enumset1(B_141, C_138, D_142, E_143))=k4_enumset1(A_139, A_140, B_141, C_138, D_142, E_143))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_152])).
% 2.79/1.43  tff(c_12, plain, (![A_14, B_15, C_16]: (k2_xboole_0(k2_tarski(A_14, B_15), k1_tarski(C_16))=k1_enumset1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.79/1.43  tff(c_92, plain, (![A_51, B_52, C_53]: (k2_xboole_0(k1_tarski(A_51), k2_xboole_0(k1_tarski(B_52), C_53))=k2_xboole_0(k2_tarski(A_51, B_52), C_53))), inference(superposition, [status(thm), theory('equality')], [c_10, c_48])).
% 2.79/1.43  tff(c_110, plain, (![A_51, A_12, B_13]: (k2_xboole_0(k2_tarski(A_51, A_12), k1_tarski(B_13))=k2_xboole_0(k1_tarski(A_51), k2_tarski(A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_92])).
% 2.79/1.43  tff(c_115, plain, (![A_54, A_55, B_56]: (k2_xboole_0(k1_tarski(A_54), k2_tarski(A_55, B_56))=k1_enumset1(A_54, A_55, B_56))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_110])).
% 2.79/1.43  tff(c_4, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k2_xboole_0(A_3, B_4), C_5)=k2_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.79/1.43  tff(c_124, plain, (![A_54, A_55, B_56, C_5]: (k2_xboole_0(k1_tarski(A_54), k2_xboole_0(k2_tarski(A_55, B_56), C_5))=k2_xboole_0(k1_enumset1(A_54, A_55, B_56), C_5))), inference(superposition, [status(thm), theory('equality')], [c_115, c_4])).
% 2.79/1.43  tff(c_485, plain, (![E_143, D_142, A_139, B_141, C_138, A_140, A_54]: (k2_xboole_0(k1_enumset1(A_54, A_139, A_140), k2_enumset1(B_141, C_138, D_142, E_143))=k2_xboole_0(k1_tarski(A_54), k4_enumset1(A_139, A_140, B_141, C_138, D_142, E_143)))), inference(superposition, [status(thm), theory('equality')], [c_476, c_124])).
% 2.79/1.43  tff(c_493, plain, (![E_143, D_142, A_139, B_141, C_138, A_140, A_54]: (k2_xboole_0(k1_enumset1(A_54, A_139, A_140), k2_enumset1(B_141, C_138, D_142, E_143))=k5_enumset1(A_54, A_139, A_140, B_141, C_138, D_142, E_143))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_485])).
% 2.79/1.43  tff(c_20, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k2_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.79/1.43  tff(c_555, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_493, c_20])).
% 2.79/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.43  
% 2.79/1.43  Inference rules
% 2.79/1.43  ----------------------
% 2.79/1.43  #Ref     : 0
% 2.79/1.43  #Sup     : 137
% 2.79/1.43  #Fact    : 0
% 2.79/1.43  #Define  : 0
% 2.79/1.43  #Split   : 0
% 2.79/1.43  #Chain   : 0
% 2.79/1.43  #Close   : 0
% 2.79/1.43  
% 2.79/1.43  Ordering : KBO
% 2.79/1.43  
% 2.79/1.43  Simplification rules
% 2.79/1.43  ----------------------
% 2.79/1.43  #Subsume      : 0
% 2.79/1.43  #Demod        : 69
% 2.79/1.43  #Tautology    : 76
% 2.79/1.43  #SimpNegUnit  : 0
% 2.79/1.43  #BackRed      : 2
% 2.79/1.43  
% 2.79/1.43  #Partial instantiations: 0
% 2.79/1.43  #Strategies tried      : 1
% 2.79/1.43  
% 2.79/1.43  Timing (in seconds)
% 2.79/1.43  ----------------------
% 2.79/1.44  Preprocessing        : 0.29
% 2.79/1.44  Parsing              : 0.16
% 2.79/1.44  CNF conversion       : 0.02
% 2.79/1.44  Main loop            : 0.39
% 2.79/1.44  Inferencing          : 0.18
% 2.79/1.44  Reduction            : 0.12
% 2.79/1.44  Demodulation         : 0.10
% 2.79/1.44  BG Simplification    : 0.03
% 2.79/1.44  Subsumption          : 0.04
% 2.79/1.44  Abstraction          : 0.03
% 2.79/1.44  MUC search           : 0.00
% 2.79/1.44  Cooper               : 0.00
% 2.79/1.44  Total                : 0.70
% 2.79/1.44  Index Insertion      : 0.00
% 2.79/1.44  Index Deletion       : 0.00
% 2.79/1.44  Index Matching       : 0.00
% 2.79/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
