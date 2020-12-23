%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:21 EST 2020

% Result     : Theorem 5.85s
% Output     : CNFRefutation 5.85s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 156 expanded)
%              Number of leaves         :   32 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :   55 ( 139 expanded)
%              Number of equality atoms :   54 ( 138 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_28,plain,(
    ! [A_44,B_45,C_46] : k2_enumset1(A_44,A_44,B_45,C_46) = k1_enumset1(A_44,B_45,C_46) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_224,plain,(
    ! [B_73,D_74,C_75,A_76] : k2_enumset1(B_73,D_74,C_75,A_76) = k2_enumset1(A_76,B_73,C_75,D_74) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_259,plain,(
    ! [C_46,A_44,B_45] : k2_enumset1(C_46,A_44,B_45,A_44) = k1_enumset1(A_44,B_45,C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_224])).

tff(c_352,plain,(
    ! [D_83,C_84,B_85,A_86] : k2_enumset1(D_83,C_84,B_85,A_86) = k2_enumset1(A_86,B_85,C_84,D_83) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_415,plain,(
    ! [A_44,B_45,C_46] : k2_enumset1(A_44,B_45,A_44,C_46) = k1_enumset1(A_44,B_45,C_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_352])).

tff(c_30,plain,(
    ! [A_47,B_48,C_49,D_50] : k3_enumset1(A_47,A_47,B_48,C_49,D_50) = k2_enumset1(A_47,B_48,C_49,D_50) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_42,B_43] : k1_enumset1(A_42,A_42,B_43) = k2_tarski(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1394,plain,(
    ! [B_129,A_130,C_133,D_132,E_131] : k2_xboole_0(k1_enumset1(A_130,B_129,C_133),k2_tarski(D_132,E_131)) = k3_enumset1(A_130,B_129,C_133,D_132,E_131) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1418,plain,(
    ! [A_42,B_43,D_132,E_131] : k3_enumset1(A_42,A_42,B_43,D_132,E_131) = k2_xboole_0(k2_tarski(A_42,B_43),k2_tarski(D_132,E_131)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1394])).

tff(c_1424,plain,(
    ! [A_42,B_43,D_132,E_131] : k2_xboole_0(k2_tarski(A_42,B_43),k2_tarski(D_132,E_131)) = k2_enumset1(A_42,B_43,D_132,E_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1418])).

tff(c_24,plain,(
    ! [A_41] : k2_tarski(A_41,A_41) = k1_tarski(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1214,plain,(
    ! [A_117,B_118,C_119,D_120] : k2_xboole_0(k1_enumset1(A_117,B_118,C_119),k1_tarski(D_120)) = k2_enumset1(A_117,B_118,C_119,D_120) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1238,plain,(
    ! [A_42,B_43,D_120] : k2_xboole_0(k2_tarski(A_42,B_43),k1_tarski(D_120)) = k2_enumset1(A_42,A_42,B_43,D_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1214])).

tff(c_4178,plain,(
    ! [A_183,B_184,D_185] : k2_xboole_0(k2_tarski(A_183,B_184),k1_tarski(D_185)) = k1_enumset1(A_183,B_184,D_185) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1238])).

tff(c_4199,plain,(
    ! [A_41,D_185] : k2_xboole_0(k1_tarski(A_41),k1_tarski(D_185)) = k1_enumset1(A_41,A_41,D_185) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4178])).

tff(c_4203,plain,(
    ! [A_186,D_187] : k2_xboole_0(k1_tarski(A_186),k1_tarski(D_187)) = k2_tarski(A_186,D_187) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4199])).

tff(c_10,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_152,plain,(
    ! [A_70,B_71,C_72] : k5_xboole_0(k5_xboole_0(A_70,B_71),C_72) = k5_xboole_0(A_70,k5_xboole_0(B_71,C_72)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2529,plain,(
    ! [A_159,B_160,C_161] : k5_xboole_0(k5_xboole_0(A_159,B_160),C_161) = k5_xboole_0(B_160,k5_xboole_0(A_159,C_161)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_152])).

tff(c_8,plain,(
    ! [A_8,B_9] : k5_xboole_0(k5_xboole_0(A_8,B_9),k3_xboole_0(A_8,B_9)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2548,plain,(
    ! [B_160,A_159] : k5_xboole_0(B_160,k5_xboole_0(A_159,k3_xboole_0(A_159,B_160))) = k2_xboole_0(A_159,B_160) ),
    inference(superposition,[status(thm),theory(equality)],[c_2529,c_8])).

tff(c_2612,plain,(
    ! [B_160,A_159] : k2_xboole_0(B_160,A_159) = k2_xboole_0(A_159,B_160) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4,c_2548])).

tff(c_4224,plain,(
    ! [D_188,A_189] : k2_xboole_0(k1_tarski(D_188),k1_tarski(A_189)) = k2_tarski(A_189,D_188) ),
    inference(superposition,[status(thm),theory(equality)],[c_4203,c_2612])).

tff(c_4202,plain,(
    ! [A_41,D_185] : k2_xboole_0(k1_tarski(A_41),k1_tarski(D_185)) = k2_tarski(A_41,D_185) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4199])).

tff(c_4230,plain,(
    ! [D_188,A_189] : k2_tarski(D_188,A_189) = k2_tarski(A_189,D_188) ),
    inference(superposition,[status(thm),theory(equality)],[c_4224,c_4202])).

tff(c_396,plain,(
    ! [D_83,C_84,B_85] : k2_enumset1(D_83,C_84,B_85,B_85) = k1_enumset1(B_85,C_84,D_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_28])).

tff(c_540,plain,(
    ! [A_92,D_93,C_94,B_95] : k2_enumset1(A_92,D_93,C_94,B_95) = k2_enumset1(A_92,B_95,C_94,D_93) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_807,plain,(
    ! [D_105,B_106,C_107] : k2_enumset1(D_105,B_106,B_106,C_107) = k1_enumset1(B_106,C_107,D_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_540])).

tff(c_16,plain,(
    ! [B_22,D_24,C_23,A_21] : k2_enumset1(B_22,D_24,C_23,A_21) = k2_enumset1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_451,plain,(
    ! [D_87,C_88,B_89] : k2_enumset1(D_87,C_88,B_89,B_89) = k1_enumset1(B_89,C_88,D_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_28])).

tff(c_501,plain,(
    ! [B_22,D_24,A_21] : k2_enumset1(B_22,D_24,D_24,A_21) = k1_enumset1(D_24,B_22,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_451])).

tff(c_813,plain,(
    ! [B_106,D_105,C_107] : k1_enumset1(B_106,D_105,C_107) = k1_enumset1(B_106,C_107,D_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_807,c_501])).

tff(c_34,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_910,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_813,c_34])).

tff(c_2620,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_1'),k2_tarski('#skF_2','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2612,c_910])).

tff(c_4255,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),k2_tarski('#skF_1','#skF_2')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4230,c_4230,c_2620])).

tff(c_6069,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1424,c_4255])).

tff(c_6072,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_6069])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.85/2.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.85/2.25  
% 5.85/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.85/2.25  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 5.85/2.25  
% 5.85/2.25  %Foreground sorts:
% 5.85/2.25  
% 5.85/2.25  
% 5.85/2.25  %Background operators:
% 5.85/2.25  
% 5.85/2.25  
% 5.85/2.25  %Foreground operators:
% 5.85/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.85/2.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.85/2.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.85/2.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.85/2.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.85/2.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.85/2.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.85/2.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.85/2.25  tff('#skF_2', type, '#skF_2': $i).
% 5.85/2.25  tff('#skF_3', type, '#skF_3': $i).
% 5.85/2.25  tff('#skF_1', type, '#skF_1': $i).
% 5.85/2.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.85/2.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.85/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.85/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.85/2.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.85/2.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.85/2.25  
% 5.85/2.26  tff(f_53, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 5.85/2.26  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_enumset1)).
% 5.85/2.26  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 5.85/2.26  tff(f_55, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 5.85/2.26  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.85/2.26  tff(f_37, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 5.85/2.26  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.85/2.26  tff(f_45, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 5.85/2.26  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.85/2.26  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.85/2.26  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.85/2.26  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.85/2.26  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 5.85/2.26  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_enumset1)).
% 5.85/2.26  tff(f_60, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 5.85/2.26  tff(c_28, plain, (![A_44, B_45, C_46]: (k2_enumset1(A_44, A_44, B_45, C_46)=k1_enumset1(A_44, B_45, C_46))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.85/2.26  tff(c_224, plain, (![B_73, D_74, C_75, A_76]: (k2_enumset1(B_73, D_74, C_75, A_76)=k2_enumset1(A_76, B_73, C_75, D_74))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.85/2.26  tff(c_259, plain, (![C_46, A_44, B_45]: (k2_enumset1(C_46, A_44, B_45, A_44)=k1_enumset1(A_44, B_45, C_46))), inference(superposition, [status(thm), theory('equality')], [c_28, c_224])).
% 5.85/2.26  tff(c_352, plain, (![D_83, C_84, B_85, A_86]: (k2_enumset1(D_83, C_84, B_85, A_86)=k2_enumset1(A_86, B_85, C_84, D_83))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.85/2.26  tff(c_415, plain, (![A_44, B_45, C_46]: (k2_enumset1(A_44, B_45, A_44, C_46)=k1_enumset1(A_44, B_45, C_46))), inference(superposition, [status(thm), theory('equality')], [c_259, c_352])).
% 5.85/2.26  tff(c_30, plain, (![A_47, B_48, C_49, D_50]: (k3_enumset1(A_47, A_47, B_48, C_49, D_50)=k2_enumset1(A_47, B_48, C_49, D_50))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.85/2.26  tff(c_26, plain, (![A_42, B_43]: (k1_enumset1(A_42, A_42, B_43)=k2_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.85/2.26  tff(c_1394, plain, (![B_129, A_130, C_133, D_132, E_131]: (k2_xboole_0(k1_enumset1(A_130, B_129, C_133), k2_tarski(D_132, E_131))=k3_enumset1(A_130, B_129, C_133, D_132, E_131))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.85/2.26  tff(c_1418, plain, (![A_42, B_43, D_132, E_131]: (k3_enumset1(A_42, A_42, B_43, D_132, E_131)=k2_xboole_0(k2_tarski(A_42, B_43), k2_tarski(D_132, E_131)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1394])).
% 5.85/2.26  tff(c_1424, plain, (![A_42, B_43, D_132, E_131]: (k2_xboole_0(k2_tarski(A_42, B_43), k2_tarski(D_132, E_131))=k2_enumset1(A_42, B_43, D_132, E_131))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1418])).
% 5.85/2.26  tff(c_24, plain, (![A_41]: (k2_tarski(A_41, A_41)=k1_tarski(A_41))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.85/2.26  tff(c_1214, plain, (![A_117, B_118, C_119, D_120]: (k2_xboole_0(k1_enumset1(A_117, B_118, C_119), k1_tarski(D_120))=k2_enumset1(A_117, B_118, C_119, D_120))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.85/2.26  tff(c_1238, plain, (![A_42, B_43, D_120]: (k2_xboole_0(k2_tarski(A_42, B_43), k1_tarski(D_120))=k2_enumset1(A_42, A_42, B_43, D_120))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1214])).
% 5.85/2.26  tff(c_4178, plain, (![A_183, B_184, D_185]: (k2_xboole_0(k2_tarski(A_183, B_184), k1_tarski(D_185))=k1_enumset1(A_183, B_184, D_185))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1238])).
% 5.85/2.26  tff(c_4199, plain, (![A_41, D_185]: (k2_xboole_0(k1_tarski(A_41), k1_tarski(D_185))=k1_enumset1(A_41, A_41, D_185))), inference(superposition, [status(thm), theory('equality')], [c_24, c_4178])).
% 5.85/2.26  tff(c_4203, plain, (![A_186, D_187]: (k2_xboole_0(k1_tarski(A_186), k1_tarski(D_187))=k2_tarski(A_186, D_187))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4199])).
% 5.85/2.26  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.85/2.26  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.85/2.26  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.85/2.26  tff(c_152, plain, (![A_70, B_71, C_72]: (k5_xboole_0(k5_xboole_0(A_70, B_71), C_72)=k5_xboole_0(A_70, k5_xboole_0(B_71, C_72)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.85/2.26  tff(c_2529, plain, (![A_159, B_160, C_161]: (k5_xboole_0(k5_xboole_0(A_159, B_160), C_161)=k5_xboole_0(B_160, k5_xboole_0(A_159, C_161)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_152])).
% 5.85/2.26  tff(c_8, plain, (![A_8, B_9]: (k5_xboole_0(k5_xboole_0(A_8, B_9), k3_xboole_0(A_8, B_9))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.85/2.26  tff(c_2548, plain, (![B_160, A_159]: (k5_xboole_0(B_160, k5_xboole_0(A_159, k3_xboole_0(A_159, B_160)))=k2_xboole_0(A_159, B_160))), inference(superposition, [status(thm), theory('equality')], [c_2529, c_8])).
% 5.85/2.26  tff(c_2612, plain, (![B_160, A_159]: (k2_xboole_0(B_160, A_159)=k2_xboole_0(A_159, B_160))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4, c_2548])).
% 5.85/2.26  tff(c_4224, plain, (![D_188, A_189]: (k2_xboole_0(k1_tarski(D_188), k1_tarski(A_189))=k2_tarski(A_189, D_188))), inference(superposition, [status(thm), theory('equality')], [c_4203, c_2612])).
% 5.85/2.26  tff(c_4202, plain, (![A_41, D_185]: (k2_xboole_0(k1_tarski(A_41), k1_tarski(D_185))=k2_tarski(A_41, D_185))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4199])).
% 5.85/2.26  tff(c_4230, plain, (![D_188, A_189]: (k2_tarski(D_188, A_189)=k2_tarski(A_189, D_188))), inference(superposition, [status(thm), theory('equality')], [c_4224, c_4202])).
% 5.85/2.26  tff(c_396, plain, (![D_83, C_84, B_85]: (k2_enumset1(D_83, C_84, B_85, B_85)=k1_enumset1(B_85, C_84, D_83))), inference(superposition, [status(thm), theory('equality')], [c_352, c_28])).
% 5.85/2.26  tff(c_540, plain, (![A_92, D_93, C_94, B_95]: (k2_enumset1(A_92, D_93, C_94, B_95)=k2_enumset1(A_92, B_95, C_94, D_93))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.85/2.26  tff(c_807, plain, (![D_105, B_106, C_107]: (k2_enumset1(D_105, B_106, B_106, C_107)=k1_enumset1(B_106, C_107, D_105))), inference(superposition, [status(thm), theory('equality')], [c_396, c_540])).
% 5.85/2.26  tff(c_16, plain, (![B_22, D_24, C_23, A_21]: (k2_enumset1(B_22, D_24, C_23, A_21)=k2_enumset1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.85/2.26  tff(c_451, plain, (![D_87, C_88, B_89]: (k2_enumset1(D_87, C_88, B_89, B_89)=k1_enumset1(B_89, C_88, D_87))), inference(superposition, [status(thm), theory('equality')], [c_352, c_28])).
% 5.85/2.26  tff(c_501, plain, (![B_22, D_24, A_21]: (k2_enumset1(B_22, D_24, D_24, A_21)=k1_enumset1(D_24, B_22, A_21))), inference(superposition, [status(thm), theory('equality')], [c_16, c_451])).
% 5.85/2.26  tff(c_813, plain, (![B_106, D_105, C_107]: (k1_enumset1(B_106, D_105, C_107)=k1_enumset1(B_106, C_107, D_105))), inference(superposition, [status(thm), theory('equality')], [c_807, c_501])).
% 5.85/2.26  tff(c_34, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.85/2.26  tff(c_910, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_813, c_34])).
% 5.85/2.26  tff(c_2620, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_1'), k2_tarski('#skF_2', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2612, c_910])).
% 5.85/2.26  tff(c_4255, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), k2_tarski('#skF_1', '#skF_2'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4230, c_4230, c_2620])).
% 5.85/2.26  tff(c_6069, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1424, c_4255])).
% 5.85/2.26  tff(c_6072, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_415, c_6069])).
% 5.85/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.85/2.26  
% 5.85/2.26  Inference rules
% 5.85/2.26  ----------------------
% 5.85/2.26  #Ref     : 0
% 5.85/2.26  #Sup     : 1552
% 5.85/2.26  #Fact    : 0
% 5.85/2.26  #Define  : 0
% 5.85/2.26  #Split   : 0
% 5.85/2.26  #Chain   : 0
% 5.85/2.26  #Close   : 0
% 5.85/2.26  
% 5.85/2.26  Ordering : KBO
% 5.85/2.26  
% 5.85/2.26  Simplification rules
% 5.85/2.26  ----------------------
% 5.85/2.26  #Subsume      : 293
% 5.85/2.26  #Demod        : 830
% 5.85/2.26  #Tautology    : 828
% 5.85/2.26  #SimpNegUnit  : 0
% 5.85/2.26  #BackRed      : 5
% 5.85/2.26  
% 5.85/2.26  #Partial instantiations: 0
% 5.85/2.26  #Strategies tried      : 1
% 5.85/2.26  
% 5.85/2.26  Timing (in seconds)
% 5.85/2.26  ----------------------
% 5.85/2.27  Preprocessing        : 0.38
% 5.85/2.27  Parsing              : 0.22
% 5.85/2.27  CNF conversion       : 0.02
% 5.85/2.27  Main loop            : 1.09
% 5.85/2.27  Inferencing          : 0.32
% 5.85/2.27  Reduction            : 0.57
% 5.85/2.27  Demodulation         : 0.51
% 5.85/2.27  BG Simplification    : 0.04
% 5.85/2.27  Subsumption          : 0.12
% 5.85/2.27  Abstraction          : 0.06
% 5.85/2.27  MUC search           : 0.00
% 5.85/2.27  Cooper               : 0.00
% 5.85/2.27  Total                : 1.51
% 5.85/2.27  Index Insertion      : 0.00
% 5.85/2.27  Index Deletion       : 0.00
% 5.85/2.27  Index Matching       : 0.00
% 5.85/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
