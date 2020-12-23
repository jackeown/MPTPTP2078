%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:50 EST 2020

% Result     : Theorem 4.23s
% Output     : CNFRefutation 4.23s
% Verified   : 
% Statistics : Number of formulae       :   44 (  54 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   24 (  34 expanded)
%              Number of equality atoms :   23 (  33 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_tarski(A),k4_enumset1(B,C,D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_tarski(A),k1_enumset1(B,C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k1_enumset1(A,B,C),k2_enumset1(D,E,F,G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

tff(c_18,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,G_36,F_35] : k2_xboole_0(k1_tarski(A_30),k4_enumset1(B_31,C_32,D_33,E_34,F_35,G_36)) = k5_enumset1(A_30,B_31,C_32,D_33,E_34,F_35,G_36) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [C_11,E_13,B_10,F_14,D_12,A_9] : k2_xboole_0(k1_enumset1(A_9,B_10,C_11),k1_enumset1(D_12,E_13,F_14)) = k4_enumset1(A_9,B_10,C_11,D_12,E_13,F_14) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_15,B_16] : k2_xboole_0(k1_tarski(A_15),k1_tarski(B_16)) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    ! [A_44,B_45,C_46] : k2_xboole_0(k2_xboole_0(A_44,B_45),C_46) = k2_xboole_0(A_44,k2_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_82,plain,(
    ! [A_15,B_16,C_46] : k2_xboole_0(k1_tarski(A_15),k2_xboole_0(k1_tarski(B_16),C_46)) = k2_xboole_0(k2_tarski(A_15,B_16),C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_67])).

tff(c_14,plain,(
    ! [A_20,B_21,C_22,D_23] : k2_xboole_0(k1_tarski(A_20),k1_enumset1(B_21,C_22,D_23)) = k2_enumset1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_111,plain,(
    ! [A_54,B_55,C_56] : k2_xboole_0(k1_tarski(A_54),k2_xboole_0(k1_tarski(B_55),C_56)) = k2_xboole_0(k2_tarski(A_54,B_55),C_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_67])).

tff(c_401,plain,(
    ! [D_109,A_110,B_108,A_107,C_106] : k2_xboole_0(k2_tarski(A_107,A_110),k1_enumset1(B_108,C_106,D_109)) = k2_xboole_0(k1_tarski(A_107),k2_enumset1(A_110,B_108,C_106,D_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_111])).

tff(c_87,plain,(
    ! [A_47,B_48,C_49] : k2_xboole_0(k1_tarski(A_47),k2_tarski(B_48,C_49)) = k1_enumset1(A_47,B_48,C_49) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k2_xboole_0(k2_xboole_0(A_1,B_2),C_3) = k2_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_93,plain,(
    ! [A_47,B_48,C_49,C_3] : k2_xboole_0(k1_tarski(A_47),k2_xboole_0(k2_tarski(B_48,C_49),C_3)) = k2_xboole_0(k1_enumset1(A_47,B_48,C_49),C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_2])).

tff(c_407,plain,(
    ! [D_109,A_47,A_110,B_108,A_107,C_106] : k2_xboole_0(k1_tarski(A_47),k2_xboole_0(k1_tarski(A_107),k2_enumset1(A_110,B_108,C_106,D_109))) = k2_xboole_0(k1_enumset1(A_47,A_107,A_110),k1_enumset1(B_108,C_106,D_109)) ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_93])).

tff(c_846,plain,(
    ! [A_141,A_138,A_137,B_139,C_142,D_140] : k2_xboole_0(k2_tarski(A_138,A_141),k2_enumset1(A_137,B_139,C_142,D_140)) = k4_enumset1(A_138,A_141,A_137,B_139,C_142,D_140) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_82,c_407])).

tff(c_867,plain,(
    ! [A_47,A_141,A_138,A_137,B_139,C_142,D_140] : k2_xboole_0(k1_enumset1(A_47,A_138,A_141),k2_enumset1(A_137,B_139,C_142,D_140)) = k2_xboole_0(k1_tarski(A_47),k4_enumset1(A_138,A_141,A_137,B_139,C_142,D_140)) ),
    inference(superposition,[status(thm),theory(equality)],[c_846,c_93])).

tff(c_877,plain,(
    ! [A_47,A_141,A_138,A_137,B_139,C_142,D_140] : k2_xboole_0(k1_enumset1(A_47,A_138,A_141),k2_enumset1(A_137,B_139,C_142,D_140)) = k5_enumset1(A_47,A_138,A_141,A_137,B_139,C_142,D_140) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_867])).

tff(c_20,plain,(
    k2_xboole_0(k1_enumset1('#skF_1','#skF_2','#skF_3'),k2_enumset1('#skF_4','#skF_5','#skF_6','#skF_7')) != k5_enumset1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:22:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.23/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.74  
% 4.23/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.74  %$ k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.23/1.74  
% 4.23/1.74  %Foreground sorts:
% 4.23/1.74  
% 4.23/1.74  
% 4.23/1.74  %Background operators:
% 4.23/1.74  
% 4.23/1.74  
% 4.23/1.74  %Foreground operators:
% 4.23/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.23/1.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.23/1.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.23/1.74  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.23/1.74  tff('#skF_7', type, '#skF_7': $i).
% 4.23/1.74  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.23/1.74  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.23/1.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.23/1.74  tff('#skF_5', type, '#skF_5': $i).
% 4.23/1.74  tff('#skF_6', type, '#skF_6': $i).
% 4.23/1.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.23/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.23/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.23/1.74  tff('#skF_1', type, '#skF_1': $i).
% 4.23/1.74  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.23/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.23/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.23/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.23/1.74  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.23/1.74  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.23/1.74  
% 4.23/1.75  tff(f_43, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_tarski(A), k4_enumset1(B, C, D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_enumset1)).
% 4.23/1.75  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l62_enumset1)).
% 4.23/1.75  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 4.23/1.75  tff(f_27, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 4.23/1.75  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_tarski(A), k1_enumset1(B, C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_enumset1)).
% 4.23/1.75  tff(f_37, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 4.23/1.75  tff(f_46, negated_conjecture, ~(![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k1_enumset1(A, B, C), k2_enumset1(D, E, F, G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_enumset1)).
% 4.23/1.75  tff(c_18, plain, (![D_33, A_30, C_32, B_31, E_34, G_36, F_35]: (k2_xboole_0(k1_tarski(A_30), k4_enumset1(B_31, C_32, D_33, E_34, F_35, G_36))=k5_enumset1(A_30, B_31, C_32, D_33, E_34, F_35, G_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.23/1.75  tff(c_8, plain, (![C_11, E_13, B_10, F_14, D_12, A_9]: (k2_xboole_0(k1_enumset1(A_9, B_10, C_11), k1_enumset1(D_12, E_13, F_14))=k4_enumset1(A_9, B_10, C_11, D_12, E_13, F_14))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.23/1.75  tff(c_10, plain, (![A_15, B_16]: (k2_xboole_0(k1_tarski(A_15), k1_tarski(B_16))=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.23/1.75  tff(c_67, plain, (![A_44, B_45, C_46]: (k2_xboole_0(k2_xboole_0(A_44, B_45), C_46)=k2_xboole_0(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.23/1.75  tff(c_82, plain, (![A_15, B_16, C_46]: (k2_xboole_0(k1_tarski(A_15), k2_xboole_0(k1_tarski(B_16), C_46))=k2_xboole_0(k2_tarski(A_15, B_16), C_46))), inference(superposition, [status(thm), theory('equality')], [c_10, c_67])).
% 4.23/1.75  tff(c_14, plain, (![A_20, B_21, C_22, D_23]: (k2_xboole_0(k1_tarski(A_20), k1_enumset1(B_21, C_22, D_23))=k2_enumset1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.23/1.75  tff(c_111, plain, (![A_54, B_55, C_56]: (k2_xboole_0(k1_tarski(A_54), k2_xboole_0(k1_tarski(B_55), C_56))=k2_xboole_0(k2_tarski(A_54, B_55), C_56))), inference(superposition, [status(thm), theory('equality')], [c_10, c_67])).
% 4.23/1.75  tff(c_401, plain, (![D_109, A_110, B_108, A_107, C_106]: (k2_xboole_0(k2_tarski(A_107, A_110), k1_enumset1(B_108, C_106, D_109))=k2_xboole_0(k1_tarski(A_107), k2_enumset1(A_110, B_108, C_106, D_109)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_111])).
% 4.23/1.75  tff(c_87, plain, (![A_47, B_48, C_49]: (k2_xboole_0(k1_tarski(A_47), k2_tarski(B_48, C_49))=k1_enumset1(A_47, B_48, C_49))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.23/1.75  tff(c_2, plain, (![A_1, B_2, C_3]: (k2_xboole_0(k2_xboole_0(A_1, B_2), C_3)=k2_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.23/1.75  tff(c_93, plain, (![A_47, B_48, C_49, C_3]: (k2_xboole_0(k1_tarski(A_47), k2_xboole_0(k2_tarski(B_48, C_49), C_3))=k2_xboole_0(k1_enumset1(A_47, B_48, C_49), C_3))), inference(superposition, [status(thm), theory('equality')], [c_87, c_2])).
% 4.23/1.75  tff(c_407, plain, (![D_109, A_47, A_110, B_108, A_107, C_106]: (k2_xboole_0(k1_tarski(A_47), k2_xboole_0(k1_tarski(A_107), k2_enumset1(A_110, B_108, C_106, D_109)))=k2_xboole_0(k1_enumset1(A_47, A_107, A_110), k1_enumset1(B_108, C_106, D_109)))), inference(superposition, [status(thm), theory('equality')], [c_401, c_93])).
% 4.23/1.75  tff(c_846, plain, (![A_141, A_138, A_137, B_139, C_142, D_140]: (k2_xboole_0(k2_tarski(A_138, A_141), k2_enumset1(A_137, B_139, C_142, D_140))=k4_enumset1(A_138, A_141, A_137, B_139, C_142, D_140))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_82, c_407])).
% 4.23/1.75  tff(c_867, plain, (![A_47, A_141, A_138, A_137, B_139, C_142, D_140]: (k2_xboole_0(k1_enumset1(A_47, A_138, A_141), k2_enumset1(A_137, B_139, C_142, D_140))=k2_xboole_0(k1_tarski(A_47), k4_enumset1(A_138, A_141, A_137, B_139, C_142, D_140)))), inference(superposition, [status(thm), theory('equality')], [c_846, c_93])).
% 4.23/1.75  tff(c_877, plain, (![A_47, A_141, A_138, A_137, B_139, C_142, D_140]: (k2_xboole_0(k1_enumset1(A_47, A_138, A_141), k2_enumset1(A_137, B_139, C_142, D_140))=k5_enumset1(A_47, A_138, A_141, A_137, B_139, C_142, D_140))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_867])).
% 4.23/1.75  tff(c_20, plain, (k2_xboole_0(k1_enumset1('#skF_1', '#skF_2', '#skF_3'), k2_enumset1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))!=k5_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.23/1.75  tff(c_1473, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_877, c_20])).
% 4.23/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.75  
% 4.23/1.75  Inference rules
% 4.23/1.75  ----------------------
% 4.23/1.75  #Ref     : 0
% 4.23/1.75  #Sup     : 368
% 4.23/1.75  #Fact    : 0
% 4.23/1.75  #Define  : 0
% 4.23/1.75  #Split   : 0
% 4.23/1.75  #Chain   : 0
% 4.23/1.75  #Close   : 0
% 4.23/1.75  
% 4.23/1.75  Ordering : KBO
% 4.23/1.75  
% 4.23/1.75  Simplification rules
% 4.23/1.75  ----------------------
% 4.23/1.75  #Subsume      : 0
% 4.23/1.75  #Demod        : 628
% 4.23/1.75  #Tautology    : 193
% 4.23/1.75  #SimpNegUnit  : 0
% 4.23/1.75  #BackRed      : 1
% 4.23/1.75  
% 4.23/1.75  #Partial instantiations: 0
% 4.23/1.75  #Strategies tried      : 1
% 4.23/1.75  
% 4.23/1.75  Timing (in seconds)
% 4.23/1.75  ----------------------
% 4.23/1.75  Preprocessing        : 0.30
% 4.23/1.75  Parsing              : 0.16
% 4.23/1.75  CNF conversion       : 0.02
% 4.23/1.75  Main loop            : 0.64
% 4.23/1.75  Inferencing          : 0.24
% 4.23/1.75  Reduction            : 0.27
% 4.23/1.75  Demodulation         : 0.23
% 4.23/1.75  BG Simplification    : 0.04
% 4.23/1.75  Subsumption          : 0.06
% 4.23/1.75  Abstraction          : 0.06
% 4.23/1.75  MUC search           : 0.00
% 4.23/1.75  Cooper               : 0.00
% 4.23/1.75  Total                : 0.97
% 4.23/1.75  Index Insertion      : 0.00
% 4.23/1.76  Index Deletion       : 0.00
% 4.23/1.76  Index Matching       : 0.00
% 4.23/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
