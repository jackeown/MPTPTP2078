%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:59 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   44 (  51 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    9
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
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k1_enumset1(A,B,C),k3_enumset1(D,E,F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_enumset1(F,G,H)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

tff(c_18,plain,(
    ! [C_39,B_38,A_37,D_40,F_42,G_43,E_41,H_44] : k2_xboole_0(k1_enumset1(A_37,B_38,C_39),k3_enumset1(D_40,E_41,F_42,G_43,H_44)) = k6_enumset1(A_37,B_38,C_39,D_40,E_41,F_42,G_43,H_44) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [E_12,D_11,A_8,C_10,B_9] : k2_xboole_0(k1_enumset1(A_8,B_9,C_10),k2_tarski(D_11,E_12)) = k3_enumset1(A_8,B_9,C_10,D_11,E_12) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_15,B_16,C_17] : k2_xboole_0(k2_tarski(A_15,B_16),k1_tarski(C_17)) = k1_enumset1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),k1_tarski(B_14)) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    ! [A_47,B_48,C_49] : k2_xboole_0(k2_xboole_0(A_47,B_48),C_49) = k2_xboole_0(A_47,k2_xboole_0(B_48,C_49)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_74,plain,(
    ! [A_57,B_58,C_59] : k2_xboole_0(k1_tarski(A_57),k2_xboole_0(k1_tarski(B_58),C_59)) = k2_xboole_0(k2_tarski(A_57,B_58),C_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_30])).

tff(c_92,plain,(
    ! [A_57,A_13,B_14] : k2_xboole_0(k2_tarski(A_57,A_13),k1_tarski(B_14)) = k2_xboole_0(k1_tarski(A_57),k2_tarski(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_74])).

tff(c_96,plain,(
    ! [A_57,A_13,B_14] : k2_xboole_0(k1_tarski(A_57),k2_tarski(A_13,B_14)) = k1_enumset1(A_57,A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_92])).

tff(c_50,plain,(
    ! [A_50,B_51,C_52] : k2_xboole_0(k2_tarski(A_50,B_51),k1_tarski(C_52)) = k1_enumset1(A_50,B_51,C_52) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_155,plain,(
    ! [A_77,B_78,C_79,C_80] : k2_xboole_0(k2_tarski(A_77,B_78),k2_xboole_0(k1_tarski(C_79),C_80)) = k2_xboole_0(k1_enumset1(A_77,B_78,C_79),C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2])).

tff(c_173,plain,(
    ! [A_57,B_78,A_77,A_13,B_14] : k2_xboole_0(k1_enumset1(A_77,B_78,A_57),k2_tarski(A_13,B_14)) = k2_xboole_0(k2_tarski(A_77,B_78),k1_enumset1(A_57,A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_155])).

tff(c_183,plain,(
    ! [A_57,B_78,A_77,A_13,B_14] : k2_xboole_0(k2_tarski(A_77,B_78),k1_enumset1(A_57,A_13,B_14)) = k3_enumset1(A_77,B_78,A_57,A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_173])).

tff(c_97,plain,(
    ! [E_61,B_62,A_60,C_63,D_64] : k2_xboole_0(k1_enumset1(A_60,B_62,C_63),k2_tarski(D_64,E_61)) = k3_enumset1(A_60,B_62,C_63,D_64,E_61) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_424,plain,(
    ! [C_143,C_147,D_144,E_142,A_146,B_145] : k2_xboole_0(k1_enumset1(A_146,B_145,C_143),k2_xboole_0(k2_tarski(D_144,E_142),C_147)) = k2_xboole_0(k3_enumset1(A_146,B_145,C_143,D_144,E_142),C_147) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_2])).

tff(c_448,plain,(
    ! [A_57,C_143,B_78,A_77,A_13,B_14,A_146,B_145] : k2_xboole_0(k3_enumset1(A_146,B_145,C_143,A_77,B_78),k1_enumset1(A_57,A_13,B_14)) = k2_xboole_0(k1_enumset1(A_146,B_145,C_143),k3_enumset1(A_77,B_78,A_57,A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_424])).

tff(c_461,plain,(
    ! [A_57,C_143,B_78,A_77,A_13,B_14,A_146,B_145] : k2_xboole_0(k3_enumset1(A_146,B_145,C_143,A_77,B_78),k1_enumset1(A_57,A_13,B_14)) = k6_enumset1(A_146,B_145,C_143,A_77,B_78,A_57,A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_448])).

tff(c_20,plain,(
    k2_xboole_0(k3_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5'),k1_enumset1('#skF_6','#skF_7','#skF_8')) != k6_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_948,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:54:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.50  
% 3.29/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.51  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.48/1.51  
% 3.48/1.51  %Foreground sorts:
% 3.48/1.51  
% 3.48/1.51  
% 3.48/1.51  %Background operators:
% 3.48/1.51  
% 3.48/1.51  
% 3.48/1.51  %Foreground operators:
% 3.48/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.48/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.48/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.48/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.48/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.48/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.48/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.48/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.48/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.48/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.48/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.48/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.48/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.48/1.51  tff('#skF_8', type, '#skF_8': $i).
% 3.48/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.48/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.48/1.51  
% 3.48/1.52  tff(f_43, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k1_enumset1(A, B, C), k3_enumset1(D, E, F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_enumset1)).
% 3.48/1.52  tff(f_31, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l57_enumset1)).
% 3.48/1.52  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 3.48/1.52  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.48/1.52  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 3.48/1.52  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_enumset1(F, G, H)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_enumset1)).
% 3.48/1.52  tff(c_18, plain, (![C_39, B_38, A_37, D_40, F_42, G_43, E_41, H_44]: (k2_xboole_0(k1_enumset1(A_37, B_38, C_39), k3_enumset1(D_40, E_41, F_42, G_43, H_44))=k6_enumset1(A_37, B_38, C_39, D_40, E_41, F_42, G_43, H_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.48/1.52  tff(c_6, plain, (![E_12, D_11, A_8, C_10, B_9]: (k2_xboole_0(k1_enumset1(A_8, B_9, C_10), k2_tarski(D_11, E_12))=k3_enumset1(A_8, B_9, C_10, D_11, E_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.48/1.52  tff(c_10, plain, (![A_15, B_16, C_17]: (k2_xboole_0(k2_tarski(A_15, B_16), k1_tarski(C_17))=k1_enumset1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.52  tff(c_8, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), k1_tarski(B_14))=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.48/1.52  tff(c_30, plain, (![A_47, B_48, C_49]: (k2_xboole_0(k2_xboole_0(A_47, B_48), C_49)=k2_xboole_0(A_47, k2_xboole_0(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.48/1.52  tff(c_74, plain, (![A_57, B_58, C_59]: (k2_xboole_0(k1_tarski(A_57), k2_xboole_0(k1_tarski(B_58), C_59))=k2_xboole_0(k2_tarski(A_57, B_58), C_59))), inference(superposition, [status(thm), theory('equality')], [c_8, c_30])).
% 3.48/1.52  tff(c_92, plain, (![A_57, A_13, B_14]: (k2_xboole_0(k2_tarski(A_57, A_13), k1_tarski(B_14))=k2_xboole_0(k1_tarski(A_57), k2_tarski(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_74])).
% 3.48/1.52  tff(c_96, plain, (![A_57, A_13, B_14]: (k2_xboole_0(k1_tarski(A_57), k2_tarski(A_13, B_14))=k1_enumset1(A_57, A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_92])).
% 3.48/1.52  tff(c_50, plain, (![A_50, B_51, C_52]: (k2_xboole_0(k2_tarski(A_50, B_51), k1_tarski(C_52))=k1_enumset1(A_50, B_51, C_52))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.52  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.48/1.52  tff(c_155, plain, (![A_77, B_78, C_79, C_80]: (k2_xboole_0(k2_tarski(A_77, B_78), k2_xboole_0(k1_tarski(C_79), C_80))=k2_xboole_0(k1_enumset1(A_77, B_78, C_79), C_80))), inference(superposition, [status(thm), theory('equality')], [c_50, c_2])).
% 3.48/1.52  tff(c_173, plain, (![A_57, B_78, A_77, A_13, B_14]: (k2_xboole_0(k1_enumset1(A_77, B_78, A_57), k2_tarski(A_13, B_14))=k2_xboole_0(k2_tarski(A_77, B_78), k1_enumset1(A_57, A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_155])).
% 3.48/1.52  tff(c_183, plain, (![A_57, B_78, A_77, A_13, B_14]: (k2_xboole_0(k2_tarski(A_77, B_78), k1_enumset1(A_57, A_13, B_14))=k3_enumset1(A_77, B_78, A_57, A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_173])).
% 3.48/1.52  tff(c_97, plain, (![E_61, B_62, A_60, C_63, D_64]: (k2_xboole_0(k1_enumset1(A_60, B_62, C_63), k2_tarski(D_64, E_61))=k3_enumset1(A_60, B_62, C_63, D_64, E_61))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.48/1.52  tff(c_424, plain, (![C_143, C_147, D_144, E_142, A_146, B_145]: (k2_xboole_0(k1_enumset1(A_146, B_145, C_143), k2_xboole_0(k2_tarski(D_144, E_142), C_147))=k2_xboole_0(k3_enumset1(A_146, B_145, C_143, D_144, E_142), C_147))), inference(superposition, [status(thm), theory('equality')], [c_97, c_2])).
% 3.48/1.52  tff(c_448, plain, (![A_57, C_143, B_78, A_77, A_13, B_14, A_146, B_145]: (k2_xboole_0(k3_enumset1(A_146, B_145, C_143, A_77, B_78), k1_enumset1(A_57, A_13, B_14))=k2_xboole_0(k1_enumset1(A_146, B_145, C_143), k3_enumset1(A_77, B_78, A_57, A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_183, c_424])).
% 3.48/1.52  tff(c_461, plain, (![A_57, C_143, B_78, A_77, A_13, B_14, A_146, B_145]: (k2_xboole_0(k3_enumset1(A_146, B_145, C_143, A_77, B_78), k1_enumset1(A_57, A_13, B_14))=k6_enumset1(A_146, B_145, C_143, A_77, B_78, A_57, A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_448])).
% 3.48/1.52  tff(c_20, plain, (k2_xboole_0(k3_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5'), k1_enumset1('#skF_6', '#skF_7', '#skF_8'))!=k6_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.48/1.52  tff(c_948, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_461, c_20])).
% 3.48/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.52  
% 3.48/1.52  Inference rules
% 3.48/1.52  ----------------------
% 3.48/1.52  #Ref     : 0
% 3.48/1.52  #Sup     : 241
% 3.48/1.52  #Fact    : 0
% 3.48/1.52  #Define  : 0
% 3.48/1.52  #Split   : 0
% 3.48/1.52  #Chain   : 0
% 3.48/1.52  #Close   : 0
% 3.48/1.52  
% 3.48/1.52  Ordering : KBO
% 3.48/1.52  
% 3.48/1.52  Simplification rules
% 3.48/1.52  ----------------------
% 3.48/1.52  #Subsume      : 0
% 3.48/1.52  #Demod        : 138
% 3.48/1.52  #Tautology    : 122
% 3.48/1.52  #SimpNegUnit  : 0
% 3.48/1.52  #BackRed      : 3
% 3.48/1.52  
% 3.48/1.52  #Partial instantiations: 0
% 3.48/1.52  #Strategies tried      : 1
% 3.48/1.52  
% 3.48/1.52  Timing (in seconds)
% 3.48/1.52  ----------------------
% 3.48/1.52  Preprocessing        : 0.29
% 3.48/1.52  Parsing              : 0.16
% 3.48/1.52  CNF conversion       : 0.02
% 3.48/1.52  Main loop            : 0.47
% 3.48/1.52  Inferencing          : 0.21
% 3.48/1.52  Reduction            : 0.16
% 3.48/1.52  Demodulation         : 0.13
% 3.48/1.52  BG Simplification    : 0.03
% 3.48/1.52  Subsumption          : 0.05
% 3.48/1.52  Abstraction          : 0.04
% 3.48/1.52  MUC search           : 0.00
% 3.48/1.52  Cooper               : 0.00
% 3.48/1.52  Total                : 0.79
% 3.48/1.52  Index Insertion      : 0.00
% 3.48/1.52  Index Deletion       : 0.00
% 3.48/1.52  Index Matching       : 0.00
% 3.48/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
