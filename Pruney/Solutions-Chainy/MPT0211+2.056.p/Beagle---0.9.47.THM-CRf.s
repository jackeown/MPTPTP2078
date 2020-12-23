%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:22 EST 2020

% Result     : Theorem 13.70s
% Output     : CNFRefutation 13.79s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 183 expanded)
%              Number of leaves         :   33 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :   59 ( 166 expanded)
%              Number of equality atoms :   58 ( 165 expanded)
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

tff(f_39,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(B,D,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_tarski(E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,D,C,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_311,plain,(
    ! [B_82,D_83,C_84,A_85] : k2_enumset1(B_82,D_83,C_84,A_85) = k2_enumset1(A_85,B_82,C_84,D_83) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [A_46,B_47,C_48] : k2_enumset1(A_46,A_46,B_47,C_48) = k1_enumset1(A_46,B_47,C_48) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_505,plain,(
    ! [A_90,D_91,C_92] : k2_enumset1(A_90,D_91,C_92,D_91) = k1_enumset1(D_91,C_92,A_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_28])).

tff(c_16,plain,(
    ! [D_23,C_22,B_21,A_20] : k2_enumset1(D_23,C_22,B_21,A_20) = k2_enumset1(A_20,B_21,C_22,D_23) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_514,plain,(
    ! [D_91,C_92,A_90] : k2_enumset1(D_91,C_92,D_91,A_90) = k1_enumset1(D_91,C_92,A_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_16])).

tff(c_30,plain,(
    ! [A_49,B_50,C_51,D_52] : k3_enumset1(A_49,A_49,B_50,C_51,D_52) = k2_enumset1(A_49,B_50,C_51,D_52) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_44,B_45] : k1_enumset1(A_44,A_44,B_45) = k2_tarski(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [A_53,D_56,E_57,C_55,B_54] : k4_enumset1(A_53,A_53,B_54,C_55,D_56,E_57) = k3_enumset1(A_53,B_54,C_55,D_56,E_57) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1151,plain,(
    ! [F_129,D_126,E_130,A_128,B_127,C_131] : k2_xboole_0(k2_enumset1(A_128,B_127,C_131,D_126),k2_tarski(E_130,F_129)) = k4_enumset1(A_128,B_127,C_131,D_126,E_130,F_129) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1196,plain,(
    ! [A_46,F_129,B_47,E_130,C_48] : k4_enumset1(A_46,A_46,B_47,C_48,E_130,F_129) = k2_xboole_0(k1_enumset1(A_46,B_47,C_48),k2_tarski(E_130,F_129)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1151])).

tff(c_9461,plain,(
    ! [E_244,F_246,C_245,B_243,A_247] : k2_xboole_0(k1_enumset1(A_247,B_243,C_245),k2_tarski(E_244,F_246)) = k3_enumset1(A_247,B_243,C_245,E_244,F_246) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1196])).

tff(c_9497,plain,(
    ! [A_44,B_45,E_244,F_246] : k3_enumset1(A_44,A_44,B_45,E_244,F_246) = k2_xboole_0(k2_tarski(A_44,B_45),k2_tarski(E_244,F_246)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_9461])).

tff(c_9503,plain,(
    ! [A_44,B_45,E_244,F_246] : k2_xboole_0(k2_tarski(A_44,B_45),k2_tarski(E_244,F_246)) = k2_enumset1(A_44,B_45,E_244,F_246) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_9497])).

tff(c_24,plain,(
    ! [A_43] : k2_tarski(A_43,A_43) = k1_tarski(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_817,plain,(
    ! [D_116,A_115,B_113,C_112,E_114] : k2_xboole_0(k2_enumset1(A_115,B_113,C_112,D_116),k1_tarski(E_114)) = k3_enumset1(A_115,B_113,C_112,D_116,E_114) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_856,plain,(
    ! [A_46,B_47,C_48,E_114] : k3_enumset1(A_46,A_46,B_47,C_48,E_114) = k2_xboole_0(k1_enumset1(A_46,B_47,C_48),k1_tarski(E_114)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_817])).

tff(c_7279,plain,(
    ! [A_215,B_216,C_217,E_218] : k2_xboole_0(k1_enumset1(A_215,B_216,C_217),k1_tarski(E_218)) = k2_enumset1(A_215,B_216,C_217,E_218) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_856])).

tff(c_7315,plain,(
    ! [A_44,B_45,E_218] : k2_xboole_0(k2_tarski(A_44,B_45),k1_tarski(E_218)) = k2_enumset1(A_44,A_44,B_45,E_218) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_7279])).

tff(c_10482,plain,(
    ! [A_262,B_263,E_264] : k2_xboole_0(k2_tarski(A_262,B_263),k1_tarski(E_264)) = k1_enumset1(A_262,B_263,E_264) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_7315])).

tff(c_10503,plain,(
    ! [A_43,E_264] : k2_xboole_0(k1_tarski(A_43),k1_tarski(E_264)) = k1_enumset1(A_43,A_43,E_264) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_10482])).

tff(c_10507,plain,(
    ! [A_265,E_266] : k2_xboole_0(k1_tarski(A_265),k1_tarski(E_266)) = k2_tarski(A_265,E_266) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10503])).

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
    ! [A_72,B_73,C_74] : k5_xboole_0(k5_xboole_0(A_72,B_73),C_74) = k5_xboole_0(A_72,k5_xboole_0(B_73,C_74)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1646,plain,(
    ! [B_149,A_150,C_151] : k5_xboole_0(k5_xboole_0(B_149,A_150),C_151) = k5_xboole_0(A_150,k5_xboole_0(B_149,C_151)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_152])).

tff(c_8,plain,(
    ! [A_8,B_9] : k5_xboole_0(k5_xboole_0(A_8,B_9),k3_xboole_0(A_8,B_9)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1665,plain,(
    ! [A_150,B_149] : k5_xboole_0(A_150,k5_xboole_0(B_149,k3_xboole_0(B_149,A_150))) = k2_xboole_0(B_149,A_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_1646,c_8])).

tff(c_1729,plain,(
    ! [B_149,A_150] : k2_xboole_0(B_149,A_150) = k2_xboole_0(A_150,B_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4,c_1665])).

tff(c_10528,plain,(
    ! [E_267,A_268] : k2_xboole_0(k1_tarski(E_267),k1_tarski(A_268)) = k2_tarski(A_268,E_267) ),
    inference(superposition,[status(thm),theory(equality)],[c_10507,c_1729])).

tff(c_10506,plain,(
    ! [A_43,E_264] : k2_xboole_0(k1_tarski(A_43),k1_tarski(E_264)) = k2_tarski(A_43,E_264) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_10503])).

tff(c_10534,plain,(
    ! [E_267,A_268] : k2_tarski(E_267,A_268) = k2_tarski(A_268,E_267) ),
    inference(superposition,[status(thm),theory(equality)],[c_10528,c_10506])).

tff(c_224,plain,(
    ! [A_75,D_76,C_77,B_78] : k2_enumset1(A_75,D_76,C_77,B_78) = k2_enumset1(A_75,B_78,C_77,D_76) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_240,plain,(
    ! [B_78,D_76,C_77] : k2_enumset1(B_78,D_76,C_77,B_78) = k1_enumset1(B_78,C_77,D_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_28])).

tff(c_396,plain,(
    ! [D_86,C_87,B_88,A_89] : k2_enumset1(D_86,C_87,B_88,A_89) = k2_enumset1(A_89,B_88,C_87,D_86) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_968,plain,(
    ! [B_120,C_121,D_122] : k2_enumset1(B_120,C_121,D_122,B_120) = k1_enumset1(B_120,C_121,D_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_396])).

tff(c_1005,plain,(
    ! [B_120,D_122,C_121] : k1_enumset1(B_120,D_122,C_121) = k1_enumset1(B_120,C_121,D_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_968,c_240])).

tff(c_34,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1080,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1005,c_34])).

tff(c_1737,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_1'),k2_tarski('#skF_2','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1729,c_1080])).

tff(c_10559,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),k2_tarski('#skF_1','#skF_2')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10534,c_10534,c_1737])).

tff(c_26132,plain,(
    k2_enumset1('#skF_1','#skF_3','#skF_1','#skF_2') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9503,c_10559])).

tff(c_26135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_26132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.70/6.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.79/6.18  
% 13.79/6.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.79/6.18  %$ k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 13.79/6.18  
% 13.79/6.18  %Foreground sorts:
% 13.79/6.18  
% 13.79/6.18  
% 13.79/6.18  %Background operators:
% 13.79/6.18  
% 13.79/6.18  
% 13.79/6.18  %Foreground operators:
% 13.79/6.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.79/6.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.79/6.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.79/6.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.79/6.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.79/6.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.79/6.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.79/6.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.79/6.18  tff('#skF_2', type, '#skF_2': $i).
% 13.79/6.18  tff('#skF_3', type, '#skF_3': $i).
% 13.79/6.18  tff('#skF_1', type, '#skF_1': $i).
% 13.79/6.18  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.79/6.18  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.79/6.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.79/6.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.79/6.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.79/6.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.79/6.18  
% 13.79/6.20  tff(f_39, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(B, D, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_enumset1)).
% 13.79/6.20  tff(f_53, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 13.79/6.20  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 13.79/6.20  tff(f_55, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 13.79/6.20  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 13.79/6.20  tff(f_57, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 13.79/6.20  tff(f_45, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_tarski(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_enumset1)).
% 13.79/6.20  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 13.79/6.20  tff(f_43, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 13.79/6.20  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 13.79/6.20  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.79/6.20  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 13.79/6.20  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 13.79/6.20  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 13.79/6.20  tff(f_37, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, D, C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_enumset1)).
% 13.79/6.20  tff(f_60, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_enumset1)).
% 13.79/6.20  tff(c_311, plain, (![B_82, D_83, C_84, A_85]: (k2_enumset1(B_82, D_83, C_84, A_85)=k2_enumset1(A_85, B_82, C_84, D_83))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.79/6.20  tff(c_28, plain, (![A_46, B_47, C_48]: (k2_enumset1(A_46, A_46, B_47, C_48)=k1_enumset1(A_46, B_47, C_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.79/6.20  tff(c_505, plain, (![A_90, D_91, C_92]: (k2_enumset1(A_90, D_91, C_92, D_91)=k1_enumset1(D_91, C_92, A_90))), inference(superposition, [status(thm), theory('equality')], [c_311, c_28])).
% 13.79/6.20  tff(c_16, plain, (![D_23, C_22, B_21, A_20]: (k2_enumset1(D_23, C_22, B_21, A_20)=k2_enumset1(A_20, B_21, C_22, D_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.79/6.20  tff(c_514, plain, (![D_91, C_92, A_90]: (k2_enumset1(D_91, C_92, D_91, A_90)=k1_enumset1(D_91, C_92, A_90))), inference(superposition, [status(thm), theory('equality')], [c_505, c_16])).
% 13.79/6.20  tff(c_30, plain, (![A_49, B_50, C_51, D_52]: (k3_enumset1(A_49, A_49, B_50, C_51, D_52)=k2_enumset1(A_49, B_50, C_51, D_52))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.79/6.20  tff(c_26, plain, (![A_44, B_45]: (k1_enumset1(A_44, A_44, B_45)=k2_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.79/6.20  tff(c_32, plain, (![A_53, D_56, E_57, C_55, B_54]: (k4_enumset1(A_53, A_53, B_54, C_55, D_56, E_57)=k3_enumset1(A_53, B_54, C_55, D_56, E_57))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.79/6.20  tff(c_1151, plain, (![F_129, D_126, E_130, A_128, B_127, C_131]: (k2_xboole_0(k2_enumset1(A_128, B_127, C_131, D_126), k2_tarski(E_130, F_129))=k4_enumset1(A_128, B_127, C_131, D_126, E_130, F_129))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.79/6.20  tff(c_1196, plain, (![A_46, F_129, B_47, E_130, C_48]: (k4_enumset1(A_46, A_46, B_47, C_48, E_130, F_129)=k2_xboole_0(k1_enumset1(A_46, B_47, C_48), k2_tarski(E_130, F_129)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1151])).
% 13.79/6.20  tff(c_9461, plain, (![E_244, F_246, C_245, B_243, A_247]: (k2_xboole_0(k1_enumset1(A_247, B_243, C_245), k2_tarski(E_244, F_246))=k3_enumset1(A_247, B_243, C_245, E_244, F_246))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1196])).
% 13.79/6.20  tff(c_9497, plain, (![A_44, B_45, E_244, F_246]: (k3_enumset1(A_44, A_44, B_45, E_244, F_246)=k2_xboole_0(k2_tarski(A_44, B_45), k2_tarski(E_244, F_246)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_9461])).
% 13.79/6.20  tff(c_9503, plain, (![A_44, B_45, E_244, F_246]: (k2_xboole_0(k2_tarski(A_44, B_45), k2_tarski(E_244, F_246))=k2_enumset1(A_44, B_45, E_244, F_246))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_9497])).
% 13.79/6.20  tff(c_24, plain, (![A_43]: (k2_tarski(A_43, A_43)=k1_tarski(A_43))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.79/6.20  tff(c_817, plain, (![D_116, A_115, B_113, C_112, E_114]: (k2_xboole_0(k2_enumset1(A_115, B_113, C_112, D_116), k1_tarski(E_114))=k3_enumset1(A_115, B_113, C_112, D_116, E_114))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.79/6.20  tff(c_856, plain, (![A_46, B_47, C_48, E_114]: (k3_enumset1(A_46, A_46, B_47, C_48, E_114)=k2_xboole_0(k1_enumset1(A_46, B_47, C_48), k1_tarski(E_114)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_817])).
% 13.79/6.20  tff(c_7279, plain, (![A_215, B_216, C_217, E_218]: (k2_xboole_0(k1_enumset1(A_215, B_216, C_217), k1_tarski(E_218))=k2_enumset1(A_215, B_216, C_217, E_218))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_856])).
% 13.79/6.20  tff(c_7315, plain, (![A_44, B_45, E_218]: (k2_xboole_0(k2_tarski(A_44, B_45), k1_tarski(E_218))=k2_enumset1(A_44, A_44, B_45, E_218))), inference(superposition, [status(thm), theory('equality')], [c_26, c_7279])).
% 13.79/6.20  tff(c_10482, plain, (![A_262, B_263, E_264]: (k2_xboole_0(k2_tarski(A_262, B_263), k1_tarski(E_264))=k1_enumset1(A_262, B_263, E_264))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_7315])).
% 13.79/6.20  tff(c_10503, plain, (![A_43, E_264]: (k2_xboole_0(k1_tarski(A_43), k1_tarski(E_264))=k1_enumset1(A_43, A_43, E_264))), inference(superposition, [status(thm), theory('equality')], [c_24, c_10482])).
% 13.79/6.20  tff(c_10507, plain, (![A_265, E_266]: (k2_xboole_0(k1_tarski(A_265), k1_tarski(E_266))=k2_tarski(A_265, E_266))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10503])).
% 13.79/6.20  tff(c_10, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.79/6.20  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.79/6.20  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.79/6.20  tff(c_152, plain, (![A_72, B_73, C_74]: (k5_xboole_0(k5_xboole_0(A_72, B_73), C_74)=k5_xboole_0(A_72, k5_xboole_0(B_73, C_74)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.79/6.20  tff(c_1646, plain, (![B_149, A_150, C_151]: (k5_xboole_0(k5_xboole_0(B_149, A_150), C_151)=k5_xboole_0(A_150, k5_xboole_0(B_149, C_151)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_152])).
% 13.79/6.20  tff(c_8, plain, (![A_8, B_9]: (k5_xboole_0(k5_xboole_0(A_8, B_9), k3_xboole_0(A_8, B_9))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.79/6.20  tff(c_1665, plain, (![A_150, B_149]: (k5_xboole_0(A_150, k5_xboole_0(B_149, k3_xboole_0(B_149, A_150)))=k2_xboole_0(B_149, A_150))), inference(superposition, [status(thm), theory('equality')], [c_1646, c_8])).
% 13.79/6.20  tff(c_1729, plain, (![B_149, A_150]: (k2_xboole_0(B_149, A_150)=k2_xboole_0(A_150, B_149))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4, c_1665])).
% 13.79/6.20  tff(c_10528, plain, (![E_267, A_268]: (k2_xboole_0(k1_tarski(E_267), k1_tarski(A_268))=k2_tarski(A_268, E_267))), inference(superposition, [status(thm), theory('equality')], [c_10507, c_1729])).
% 13.79/6.20  tff(c_10506, plain, (![A_43, E_264]: (k2_xboole_0(k1_tarski(A_43), k1_tarski(E_264))=k2_tarski(A_43, E_264))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_10503])).
% 13.79/6.20  tff(c_10534, plain, (![E_267, A_268]: (k2_tarski(E_267, A_268)=k2_tarski(A_268, E_267))), inference(superposition, [status(thm), theory('equality')], [c_10528, c_10506])).
% 13.79/6.20  tff(c_224, plain, (![A_75, D_76, C_77, B_78]: (k2_enumset1(A_75, D_76, C_77, B_78)=k2_enumset1(A_75, B_78, C_77, D_76))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.79/6.20  tff(c_240, plain, (![B_78, D_76, C_77]: (k2_enumset1(B_78, D_76, C_77, B_78)=k1_enumset1(B_78, C_77, D_76))), inference(superposition, [status(thm), theory('equality')], [c_224, c_28])).
% 13.79/6.20  tff(c_396, plain, (![D_86, C_87, B_88, A_89]: (k2_enumset1(D_86, C_87, B_88, A_89)=k2_enumset1(A_89, B_88, C_87, D_86))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.79/6.20  tff(c_968, plain, (![B_120, C_121, D_122]: (k2_enumset1(B_120, C_121, D_122, B_120)=k1_enumset1(B_120, C_121, D_122))), inference(superposition, [status(thm), theory('equality')], [c_240, c_396])).
% 13.79/6.20  tff(c_1005, plain, (![B_120, D_122, C_121]: (k1_enumset1(B_120, D_122, C_121)=k1_enumset1(B_120, C_121, D_122))), inference(superposition, [status(thm), theory('equality')], [c_968, c_240])).
% 13.79/6.20  tff(c_34, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.79/6.20  tff(c_1080, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1005, c_34])).
% 13.79/6.20  tff(c_1737, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_1'), k2_tarski('#skF_2', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1729, c_1080])).
% 13.79/6.20  tff(c_10559, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), k2_tarski('#skF_1', '#skF_2'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10534, c_10534, c_1737])).
% 13.79/6.20  tff(c_26132, plain, (k2_enumset1('#skF_1', '#skF_3', '#skF_1', '#skF_2')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9503, c_10559])).
% 13.79/6.20  tff(c_26135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_514, c_26132])).
% 13.79/6.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.79/6.20  
% 13.79/6.20  Inference rules
% 13.79/6.20  ----------------------
% 13.79/6.20  #Ref     : 0
% 13.79/6.20  #Sup     : 6877
% 13.79/6.20  #Fact    : 0
% 13.79/6.20  #Define  : 0
% 13.79/6.20  #Split   : 0
% 13.79/6.20  #Chain   : 0
% 13.79/6.20  #Close   : 0
% 13.79/6.20  
% 13.79/6.20  Ordering : KBO
% 13.79/6.20  
% 13.79/6.20  Simplification rules
% 13.79/6.20  ----------------------
% 13.79/6.20  #Subsume      : 1652
% 13.79/6.20  #Demod        : 4267
% 13.79/6.20  #Tautology    : 2127
% 13.79/6.20  #SimpNegUnit  : 0
% 13.79/6.20  #BackRed      : 5
% 13.79/6.20  
% 13.79/6.20  #Partial instantiations: 0
% 13.79/6.20  #Strategies tried      : 1
% 13.79/6.20  
% 13.79/6.20  Timing (in seconds)
% 13.79/6.20  ----------------------
% 13.79/6.20  Preprocessing        : 0.31
% 13.79/6.20  Parsing              : 0.16
% 13.79/6.20  CNF conversion       : 0.02
% 13.79/6.20  Main loop            : 5.12
% 13.79/6.20  Inferencing          : 0.93
% 13.79/6.20  Reduction            : 3.38
% 13.79/6.20  Demodulation         : 3.20
% 13.79/6.20  BG Simplification    : 0.14
% 13.79/6.21  Subsumption          : 0.48
% 13.79/6.21  Abstraction          : 0.22
% 13.79/6.21  MUC search           : 0.00
% 13.79/6.21  Cooper               : 0.00
% 13.79/6.21  Total                : 5.46
% 13.79/6.21  Index Insertion      : 0.00
% 13.79/6.21  Index Deletion       : 0.00
% 13.79/6.21  Index Matching       : 0.00
% 13.79/6.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
