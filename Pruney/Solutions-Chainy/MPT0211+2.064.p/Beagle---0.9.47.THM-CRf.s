%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:23 EST 2020

% Result     : Theorem 5.24s
% Output     : CNFRefutation 5.37s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 220 expanded)
%              Number of leaves         :   28 (  86 expanded)
%              Depth                    :   18
%              Number of atoms          :   61 ( 203 expanded)
%              Number of equality atoms :   60 ( 202 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k1_enumset1(A,B,C),k2_tarski(D,E)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

tff(f_41,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k1_enumset1(A,B,C),k1_enumset1(D,E,F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(B,A),k2_tarski(C,A)) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

tff(c_28,plain,(
    ! [A_63,C_65,B_64] : k1_enumset1(A_63,C_65,B_64) = k1_enumset1(A_63,B_64,C_65) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [B_67,A_66,C_68] : k1_enumset1(B_67,A_66,C_68) = k1_enumset1(A_66,B_67,C_68) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_38,B_39,C_40] : k2_enumset1(A_38,A_38,B_39,C_40) = k1_enumset1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_41,B_42,C_43,D_44] : k3_enumset1(A_41,A_41,B_42,C_43,D_44) = k2_enumset1(A_41,B_42,C_43,D_44) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_3,D_6,C_5,E_7,B_4] : k2_xboole_0(k1_enumset1(A_3,B_4,C_5),k2_tarski(D_6,E_7)) = k3_enumset1(A_3,B_4,C_5,D_6,E_7) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_662,plain,(
    ! [C_126,D_127,B_125,A_123,E_124,F_122] : k2_xboole_0(k1_enumset1(A_123,B_125,C_126),k1_enumset1(D_127,E_124,F_122)) = k4_enumset1(A_123,B_125,C_126,D_127,E_124,F_122) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_734,plain,(
    ! [C_126,A_36,B_125,A_123,B_37] : k4_enumset1(A_123,B_125,C_126,A_36,A_36,B_37) = k2_xboole_0(k1_enumset1(A_123,B_125,C_126),k2_tarski(A_36,B_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_662])).

tff(c_1327,plain,(
    ! [A_174,B_178,C_177,A_175,B_176] : k4_enumset1(A_175,B_176,C_177,A_174,A_174,B_178) = k3_enumset1(A_175,B_176,C_177,A_174,B_178) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_734])).

tff(c_22,plain,(
    ! [D_48,C_47,A_45,B_46,E_49] : k4_enumset1(A_45,A_45,B_46,C_47,D_48,E_49) = k3_enumset1(A_45,B_46,C_47,D_48,E_49) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1334,plain,(
    ! [B_176,C_177,A_174,B_178] : k3_enumset1(B_176,C_177,A_174,A_174,B_178) = k3_enumset1(B_176,B_176,C_177,A_174,B_178) ),
    inference(superposition,[status(thm),theory(equality)],[c_1327,c_22])).

tff(c_1365,plain,(
    ! [B_187,C_188,A_189,B_190] : k3_enumset1(B_187,C_188,A_189,A_189,B_190) = k2_enumset1(B_187,C_188,A_189,B_190) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1334])).

tff(c_1441,plain,(
    ! [A_41,C_43,D_44] : k2_enumset1(A_41,C_43,C_43,D_44) = k2_enumset1(A_41,A_41,C_43,D_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1365])).

tff(c_1451,plain,(
    ! [A_41,C_43,D_44] : k2_enumset1(A_41,C_43,C_43,D_44) = k1_enumset1(A_41,C_43,D_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1441])).

tff(c_1343,plain,(
    ! [B_176,C_177,A_174,B_178] : k3_enumset1(B_176,C_177,A_174,A_174,B_178) = k2_enumset1(B_176,C_177,A_174,B_178) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1334])).

tff(c_568,plain,(
    ! [C_105,D_103,A_104,E_102,B_106] : k2_xboole_0(k1_enumset1(A_104,B_106,C_105),k2_tarski(D_103,E_102)) = k3_enumset1(A_104,B_106,C_105,D_103,E_102) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_607,plain,(
    ! [A_36,B_37,D_103,E_102] : k3_enumset1(A_36,A_36,B_37,D_103,E_102) = k2_xboole_0(k2_tarski(A_36,B_37),k2_tarski(D_103,E_102)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_568])).

tff(c_613,plain,(
    ! [A_36,B_37,D_103,E_102] : k2_xboole_0(k2_tarski(A_36,B_37),k2_tarski(D_103,E_102)) = k2_enumset1(A_36,B_37,D_103,E_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_607])).

tff(c_137,plain,(
    ! [B_77,A_78,C_79] : k1_enumset1(B_77,A_78,C_79) = k1_enumset1(A_78,B_77,C_79) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_52,plain,(
    ! [A_72,C_73,B_74] : k1_enumset1(A_72,C_73,B_74) = k1_enumset1(A_72,B_74,C_73) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_68,plain,(
    ! [B_74,C_73] : k1_enumset1(B_74,C_73,B_74) = k2_tarski(B_74,C_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_16])).

tff(c_157,plain,(
    ! [A_78,C_79] : k1_enumset1(A_78,C_79,C_79) = k2_tarski(C_79,A_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_68])).

tff(c_14,plain,(
    ! [A_35] : k2_tarski(A_35,A_35) = k1_tarski(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_615,plain,(
    ! [A_107,B_108,D_109,E_110] : k2_xboole_0(k2_tarski(A_107,B_108),k2_tarski(D_109,E_110)) = k2_enumset1(A_107,B_108,D_109,E_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_607])).

tff(c_624,plain,(
    ! [A_35,D_109,E_110] : k2_xboole_0(k1_tarski(A_35),k2_tarski(D_109,E_110)) = k2_enumset1(A_35,A_35,D_109,E_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_615])).

tff(c_640,plain,(
    ! [A_117,D_118,E_119] : k2_xboole_0(k1_tarski(A_117),k2_tarski(D_118,E_119)) = k1_enumset1(A_117,D_118,E_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_624])).

tff(c_649,plain,(
    ! [A_117,A_35] : k2_xboole_0(k1_tarski(A_117),k1_tarski(A_35)) = k1_enumset1(A_117,A_35,A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_640])).

tff(c_652,plain,(
    ! [A_117,A_35] : k2_xboole_0(k1_tarski(A_117),k1_tarski(A_35)) = k2_tarski(A_35,A_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_649])).

tff(c_799,plain,(
    ! [A_133,B_134,C_135,A_136] : k3_enumset1(A_133,B_134,C_135,A_136,A_136) = k2_xboole_0(k1_enumset1(A_133,B_134,C_135),k1_tarski(A_136)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_568])).

tff(c_859,plain,(
    ! [B_137,C_138,A_139] : k3_enumset1(B_137,C_138,B_137,A_139,A_139) = k2_xboole_0(k2_tarski(B_137,C_138),k1_tarski(A_139)) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_799])).

tff(c_895,plain,(
    ! [A_35,A_139] : k3_enumset1(A_35,A_35,A_35,A_139,A_139) = k2_xboole_0(k1_tarski(A_35),k1_tarski(A_139)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_859])).

tff(c_904,plain,(
    ! [A_35,A_139] : k3_enumset1(A_35,A_35,A_35,A_139,A_139) = k2_tarski(A_139,A_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_895])).

tff(c_1394,plain,(
    ! [B_190] : k2_enumset1(B_190,B_190,B_190,B_190) = k2_tarski(B_190,B_190) ),
    inference(superposition,[status(thm),theory(equality)],[c_1365,c_904])).

tff(c_1445,plain,(
    ! [B_190] : k2_enumset1(B_190,B_190,B_190,B_190) = k1_tarski(B_190) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1394])).

tff(c_941,plain,(
    ! [D_144,F_143,C_145,E_142,B_146,A_147] : k2_xboole_0(k3_enumset1(A_147,B_146,C_145,D_144,E_142),k1_tarski(F_143)) = k4_enumset1(A_147,B_146,C_145,D_144,E_142,F_143) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_959,plain,(
    ! [D_44,C_43,A_41,F_143,B_42] : k4_enumset1(A_41,A_41,B_42,C_43,D_44,F_143) = k2_xboole_0(k2_enumset1(A_41,B_42,C_43,D_44),k1_tarski(F_143)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_941])).

tff(c_2964,plain,(
    ! [D_238,F_235,C_237,B_239,A_236] : k2_xboole_0(k2_enumset1(A_236,B_239,C_237,D_238),k1_tarski(F_235)) = k3_enumset1(A_236,B_239,C_237,D_238,F_235) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_959])).

tff(c_2982,plain,(
    ! [B_190,F_235] : k3_enumset1(B_190,B_190,B_190,B_190,F_235) = k2_xboole_0(k1_tarski(B_190),k1_tarski(F_235)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1445,c_2964])).

tff(c_2997,plain,(
    ! [B_240,F_241] : k3_enumset1(B_240,B_240,B_240,B_240,F_241) = k2_tarski(F_241,B_240) ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_2982])).

tff(c_3147,plain,(
    ! [B_242,F_243] : k2_enumset1(B_242,B_242,B_242,F_243) = k2_tarski(F_243,B_242) ),
    inference(superposition,[status(thm),theory(equality)],[c_2997,c_1343])).

tff(c_3164,plain,(
    ! [B_242,F_243] : k1_enumset1(B_242,B_242,F_243) = k2_tarski(F_243,B_242) ),
    inference(superposition,[status(thm),theory(equality)],[c_3147,c_1451])).

tff(c_731,plain,(
    ! [D_127,A_36,E_124,F_122,B_37] : k4_enumset1(A_36,A_36,B_37,D_127,E_124,F_122) = k2_xboole_0(k2_tarski(A_36,B_37),k1_enumset1(D_127,E_124,F_122)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_662])).

tff(c_3579,plain,(
    ! [F_250,A_251,E_254,B_253,D_252] : k2_xboole_0(k2_tarski(A_251,B_253),k1_enumset1(D_252,E_254,F_250)) = k3_enumset1(A_251,B_253,D_252,E_254,F_250) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_731])).

tff(c_3597,plain,(
    ! [A_251,B_253,B_242,F_243] : k3_enumset1(A_251,B_253,B_242,B_242,F_243) = k2_xboole_0(k2_tarski(A_251,B_253),k2_tarski(F_243,B_242)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3164,c_3579])).

tff(c_3640,plain,(
    ! [A_251,B_253,F_243,B_242] : k2_enumset1(A_251,B_253,F_243,B_242) = k2_enumset1(A_251,B_253,B_242,F_243) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1343,c_613,c_3597])).

tff(c_32,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_33,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_1'),k2_tarski('#skF_3','#skF_1')) != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_614,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_3','#skF_1') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_33])).

tff(c_4632,plain,(
    k2_enumset1('#skF_2','#skF_1','#skF_1','#skF_3') != k1_enumset1('#skF_1','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3640,c_614])).

tff(c_4635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_1451,c_4632])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.24/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.24/1.99  
% 5.24/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.24/2.00  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 5.24/2.00  
% 5.24/2.00  %Foreground sorts:
% 5.24/2.00  
% 5.24/2.00  
% 5.24/2.00  %Background operators:
% 5.24/2.00  
% 5.24/2.00  
% 5.24/2.00  %Foreground operators:
% 5.24/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.24/2.00  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.24/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.24/2.00  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.24/2.00  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.24/2.00  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.24/2.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.24/2.00  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.24/2.00  tff('#skF_2', type, '#skF_2': $i).
% 5.24/2.00  tff('#skF_3', type, '#skF_3': $i).
% 5.24/2.00  tff('#skF_1', type, '#skF_1': $i).
% 5.24/2.00  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.24/2.00  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.24/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.24/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.24/2.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.24/2.00  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.24/2.00  
% 5.37/2.01  tff(f_53, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_enumset1)).
% 5.37/2.01  tff(f_55, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_enumset1)).
% 5.37/2.01  tff(f_43, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 5.37/2.01  tff(f_45, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 5.37/2.01  tff(f_29, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k1_enumset1(A, B, C), k2_tarski(D, E)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l57_enumset1)).
% 5.37/2.01  tff(f_41, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.37/2.01  tff(f_31, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k1_enumset1(A, B, C), k1_enumset1(D, E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l62_enumset1)).
% 5.37/2.01  tff(f_47, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 5.37/2.01  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.37/2.01  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 5.37/2.01  tff(f_58, negated_conjecture, ~(![A, B, C]: (k2_xboole_0(k2_tarski(B, A), k2_tarski(C, A)) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_enumset1)).
% 5.37/2.01  tff(c_28, plain, (![A_63, C_65, B_64]: (k1_enumset1(A_63, C_65, B_64)=k1_enumset1(A_63, B_64, C_65))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.37/2.01  tff(c_30, plain, (![B_67, A_66, C_68]: (k1_enumset1(B_67, A_66, C_68)=k1_enumset1(A_66, B_67, C_68))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.37/2.01  tff(c_18, plain, (![A_38, B_39, C_40]: (k2_enumset1(A_38, A_38, B_39, C_40)=k1_enumset1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.37/2.01  tff(c_20, plain, (![A_41, B_42, C_43, D_44]: (k3_enumset1(A_41, A_41, B_42, C_43, D_44)=k2_enumset1(A_41, B_42, C_43, D_44))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.37/2.01  tff(c_4, plain, (![A_3, D_6, C_5, E_7, B_4]: (k2_xboole_0(k1_enumset1(A_3, B_4, C_5), k2_tarski(D_6, E_7))=k3_enumset1(A_3, B_4, C_5, D_6, E_7))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.37/2.01  tff(c_16, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.37/2.01  tff(c_662, plain, (![C_126, D_127, B_125, A_123, E_124, F_122]: (k2_xboole_0(k1_enumset1(A_123, B_125, C_126), k1_enumset1(D_127, E_124, F_122))=k4_enumset1(A_123, B_125, C_126, D_127, E_124, F_122))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.37/2.01  tff(c_734, plain, (![C_126, A_36, B_125, A_123, B_37]: (k4_enumset1(A_123, B_125, C_126, A_36, A_36, B_37)=k2_xboole_0(k1_enumset1(A_123, B_125, C_126), k2_tarski(A_36, B_37)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_662])).
% 5.37/2.01  tff(c_1327, plain, (![A_174, B_178, C_177, A_175, B_176]: (k4_enumset1(A_175, B_176, C_177, A_174, A_174, B_178)=k3_enumset1(A_175, B_176, C_177, A_174, B_178))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_734])).
% 5.37/2.01  tff(c_22, plain, (![D_48, C_47, A_45, B_46, E_49]: (k4_enumset1(A_45, A_45, B_46, C_47, D_48, E_49)=k3_enumset1(A_45, B_46, C_47, D_48, E_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.37/2.01  tff(c_1334, plain, (![B_176, C_177, A_174, B_178]: (k3_enumset1(B_176, C_177, A_174, A_174, B_178)=k3_enumset1(B_176, B_176, C_177, A_174, B_178))), inference(superposition, [status(thm), theory('equality')], [c_1327, c_22])).
% 5.37/2.01  tff(c_1365, plain, (![B_187, C_188, A_189, B_190]: (k3_enumset1(B_187, C_188, A_189, A_189, B_190)=k2_enumset1(B_187, C_188, A_189, B_190))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1334])).
% 5.37/2.01  tff(c_1441, plain, (![A_41, C_43, D_44]: (k2_enumset1(A_41, C_43, C_43, D_44)=k2_enumset1(A_41, A_41, C_43, D_44))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1365])).
% 5.37/2.01  tff(c_1451, plain, (![A_41, C_43, D_44]: (k2_enumset1(A_41, C_43, C_43, D_44)=k1_enumset1(A_41, C_43, D_44))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1441])).
% 5.37/2.01  tff(c_1343, plain, (![B_176, C_177, A_174, B_178]: (k3_enumset1(B_176, C_177, A_174, A_174, B_178)=k2_enumset1(B_176, C_177, A_174, B_178))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1334])).
% 5.37/2.01  tff(c_568, plain, (![C_105, D_103, A_104, E_102, B_106]: (k2_xboole_0(k1_enumset1(A_104, B_106, C_105), k2_tarski(D_103, E_102))=k3_enumset1(A_104, B_106, C_105, D_103, E_102))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.37/2.01  tff(c_607, plain, (![A_36, B_37, D_103, E_102]: (k3_enumset1(A_36, A_36, B_37, D_103, E_102)=k2_xboole_0(k2_tarski(A_36, B_37), k2_tarski(D_103, E_102)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_568])).
% 5.37/2.01  tff(c_613, plain, (![A_36, B_37, D_103, E_102]: (k2_xboole_0(k2_tarski(A_36, B_37), k2_tarski(D_103, E_102))=k2_enumset1(A_36, B_37, D_103, E_102))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_607])).
% 5.37/2.01  tff(c_137, plain, (![B_77, A_78, C_79]: (k1_enumset1(B_77, A_78, C_79)=k1_enumset1(A_78, B_77, C_79))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.37/2.01  tff(c_52, plain, (![A_72, C_73, B_74]: (k1_enumset1(A_72, C_73, B_74)=k1_enumset1(A_72, B_74, C_73))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.37/2.01  tff(c_68, plain, (![B_74, C_73]: (k1_enumset1(B_74, C_73, B_74)=k2_tarski(B_74, C_73))), inference(superposition, [status(thm), theory('equality')], [c_52, c_16])).
% 5.37/2.01  tff(c_157, plain, (![A_78, C_79]: (k1_enumset1(A_78, C_79, C_79)=k2_tarski(C_79, A_78))), inference(superposition, [status(thm), theory('equality')], [c_137, c_68])).
% 5.37/2.01  tff(c_14, plain, (![A_35]: (k2_tarski(A_35, A_35)=k1_tarski(A_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.37/2.01  tff(c_615, plain, (![A_107, B_108, D_109, E_110]: (k2_xboole_0(k2_tarski(A_107, B_108), k2_tarski(D_109, E_110))=k2_enumset1(A_107, B_108, D_109, E_110))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_607])).
% 5.37/2.01  tff(c_624, plain, (![A_35, D_109, E_110]: (k2_xboole_0(k1_tarski(A_35), k2_tarski(D_109, E_110))=k2_enumset1(A_35, A_35, D_109, E_110))), inference(superposition, [status(thm), theory('equality')], [c_14, c_615])).
% 5.37/2.01  tff(c_640, plain, (![A_117, D_118, E_119]: (k2_xboole_0(k1_tarski(A_117), k2_tarski(D_118, E_119))=k1_enumset1(A_117, D_118, E_119))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_624])).
% 5.37/2.01  tff(c_649, plain, (![A_117, A_35]: (k2_xboole_0(k1_tarski(A_117), k1_tarski(A_35))=k1_enumset1(A_117, A_35, A_35))), inference(superposition, [status(thm), theory('equality')], [c_14, c_640])).
% 5.37/2.01  tff(c_652, plain, (![A_117, A_35]: (k2_xboole_0(k1_tarski(A_117), k1_tarski(A_35))=k2_tarski(A_35, A_117))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_649])).
% 5.37/2.01  tff(c_799, plain, (![A_133, B_134, C_135, A_136]: (k3_enumset1(A_133, B_134, C_135, A_136, A_136)=k2_xboole_0(k1_enumset1(A_133, B_134, C_135), k1_tarski(A_136)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_568])).
% 5.37/2.01  tff(c_859, plain, (![B_137, C_138, A_139]: (k3_enumset1(B_137, C_138, B_137, A_139, A_139)=k2_xboole_0(k2_tarski(B_137, C_138), k1_tarski(A_139)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_799])).
% 5.37/2.01  tff(c_895, plain, (![A_35, A_139]: (k3_enumset1(A_35, A_35, A_35, A_139, A_139)=k2_xboole_0(k1_tarski(A_35), k1_tarski(A_139)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_859])).
% 5.37/2.01  tff(c_904, plain, (![A_35, A_139]: (k3_enumset1(A_35, A_35, A_35, A_139, A_139)=k2_tarski(A_139, A_35))), inference(demodulation, [status(thm), theory('equality')], [c_652, c_895])).
% 5.37/2.01  tff(c_1394, plain, (![B_190]: (k2_enumset1(B_190, B_190, B_190, B_190)=k2_tarski(B_190, B_190))), inference(superposition, [status(thm), theory('equality')], [c_1365, c_904])).
% 5.37/2.01  tff(c_1445, plain, (![B_190]: (k2_enumset1(B_190, B_190, B_190, B_190)=k1_tarski(B_190))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1394])).
% 5.37/2.01  tff(c_941, plain, (![D_144, F_143, C_145, E_142, B_146, A_147]: (k2_xboole_0(k3_enumset1(A_147, B_146, C_145, D_144, E_142), k1_tarski(F_143))=k4_enumset1(A_147, B_146, C_145, D_144, E_142, F_143))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.37/2.01  tff(c_959, plain, (![D_44, C_43, A_41, F_143, B_42]: (k4_enumset1(A_41, A_41, B_42, C_43, D_44, F_143)=k2_xboole_0(k2_enumset1(A_41, B_42, C_43, D_44), k1_tarski(F_143)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_941])).
% 5.37/2.01  tff(c_2964, plain, (![D_238, F_235, C_237, B_239, A_236]: (k2_xboole_0(k2_enumset1(A_236, B_239, C_237, D_238), k1_tarski(F_235))=k3_enumset1(A_236, B_239, C_237, D_238, F_235))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_959])).
% 5.37/2.01  tff(c_2982, plain, (![B_190, F_235]: (k3_enumset1(B_190, B_190, B_190, B_190, F_235)=k2_xboole_0(k1_tarski(B_190), k1_tarski(F_235)))), inference(superposition, [status(thm), theory('equality')], [c_1445, c_2964])).
% 5.37/2.01  tff(c_2997, plain, (![B_240, F_241]: (k3_enumset1(B_240, B_240, B_240, B_240, F_241)=k2_tarski(F_241, B_240))), inference(demodulation, [status(thm), theory('equality')], [c_652, c_2982])).
% 5.37/2.01  tff(c_3147, plain, (![B_242, F_243]: (k2_enumset1(B_242, B_242, B_242, F_243)=k2_tarski(F_243, B_242))), inference(superposition, [status(thm), theory('equality')], [c_2997, c_1343])).
% 5.37/2.01  tff(c_3164, plain, (![B_242, F_243]: (k1_enumset1(B_242, B_242, F_243)=k2_tarski(F_243, B_242))), inference(superposition, [status(thm), theory('equality')], [c_3147, c_1451])).
% 5.37/2.01  tff(c_731, plain, (![D_127, A_36, E_124, F_122, B_37]: (k4_enumset1(A_36, A_36, B_37, D_127, E_124, F_122)=k2_xboole_0(k2_tarski(A_36, B_37), k1_enumset1(D_127, E_124, F_122)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_662])).
% 5.37/2.01  tff(c_3579, plain, (![F_250, A_251, E_254, B_253, D_252]: (k2_xboole_0(k2_tarski(A_251, B_253), k1_enumset1(D_252, E_254, F_250))=k3_enumset1(A_251, B_253, D_252, E_254, F_250))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_731])).
% 5.37/2.01  tff(c_3597, plain, (![A_251, B_253, B_242, F_243]: (k3_enumset1(A_251, B_253, B_242, B_242, F_243)=k2_xboole_0(k2_tarski(A_251, B_253), k2_tarski(F_243, B_242)))), inference(superposition, [status(thm), theory('equality')], [c_3164, c_3579])).
% 5.37/2.01  tff(c_3640, plain, (![A_251, B_253, F_243, B_242]: (k2_enumset1(A_251, B_253, F_243, B_242)=k2_enumset1(A_251, B_253, B_242, F_243))), inference(demodulation, [status(thm), theory('equality')], [c_1343, c_613, c_3597])).
% 5.37/2.01  tff(c_32, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.37/2.01  tff(c_33, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_1'), k2_tarski('#skF_3', '#skF_1'))!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 5.37/2.01  tff(c_614, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_3', '#skF_1')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_613, c_33])).
% 5.37/2.01  tff(c_4632, plain, (k2_enumset1('#skF_2', '#skF_1', '#skF_1', '#skF_3')!=k1_enumset1('#skF_1', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3640, c_614])).
% 5.37/2.01  tff(c_4635, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_1451, c_4632])).
% 5.37/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.37/2.01  
% 5.37/2.01  Inference rules
% 5.37/2.01  ----------------------
% 5.37/2.01  #Ref     : 0
% 5.37/2.01  #Sup     : 1104
% 5.37/2.02  #Fact    : 0
% 5.37/2.02  #Define  : 0
% 5.37/2.02  #Split   : 0
% 5.37/2.02  #Chain   : 0
% 5.37/2.02  #Close   : 0
% 5.37/2.02  
% 5.37/2.02  Ordering : KBO
% 5.37/2.02  
% 5.37/2.02  Simplification rules
% 5.37/2.02  ----------------------
% 5.37/2.02  #Subsume      : 94
% 5.37/2.02  #Demod        : 1043
% 5.37/2.02  #Tautology    : 704
% 5.37/2.02  #SimpNegUnit  : 0
% 5.37/2.02  #BackRed      : 2
% 5.37/2.02  
% 5.37/2.02  #Partial instantiations: 0
% 5.37/2.02  #Strategies tried      : 1
% 5.37/2.02  
% 5.37/2.02  Timing (in seconds)
% 5.37/2.02  ----------------------
% 5.37/2.02  Preprocessing        : 0.33
% 5.37/2.02  Parsing              : 0.17
% 5.37/2.02  CNF conversion       : 0.02
% 5.37/2.02  Main loop            : 0.89
% 5.37/2.02  Inferencing          : 0.30
% 5.37/2.02  Reduction            : 0.41
% 5.37/2.02  Demodulation         : 0.36
% 5.37/2.02  BG Simplification    : 0.04
% 5.37/2.02  Subsumption          : 0.10
% 5.37/2.02  Abstraction          : 0.06
% 5.37/2.02  MUC search           : 0.00
% 5.37/2.02  Cooper               : 0.00
% 5.37/2.02  Total                : 1.25
% 5.37/2.02  Index Insertion      : 0.00
% 5.37/2.02  Index Deletion       : 0.00
% 5.37/2.02  Index Matching       : 0.00
% 5.37/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
