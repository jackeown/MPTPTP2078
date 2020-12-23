%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:46:47 EST 2020

% Result     : Theorem 13.86s
% Output     : CNFRefutation 14.00s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 242 expanded)
%              Number of leaves         :   31 (  95 expanded)
%              Depth                    :   13
%              Number of atoms          :   48 ( 223 expanded)
%              Number of equality atoms :   47 ( 222 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_53,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,A,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E,F] : k4_enumset1(A,B,C,D,E,F) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k1_tarski(F)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k3_enumset1(A,B,C,D,E),k2_tarski(F,G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_43,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_enumset1(A,B,C,D),k2_enumset1(E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k2_tarski(A,B),k4_enumset1(C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(A,C,B,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

tff(c_28,plain,(
    ! [B_63,A_62,C_64] : k1_enumset1(B_63,A_62,C_64) = k1_enumset1(A_62,B_63,C_64) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [A_44,B_45,C_46] : k2_enumset1(A_44,A_44,B_45,C_46) = k1_enumset1(A_44,B_45,C_46) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_47,B_48,C_49,D_50] : k3_enumset1(A_47,A_47,B_48,C_49,D_50) = k2_enumset1(A_47,B_48,C_49,D_50) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [B_52,E_55,C_53,D_54,A_51] : k4_enumset1(A_51,A_51,B_52,C_53,D_54,E_55) = k3_enumset1(A_51,B_52,C_53,D_54,E_55) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8,plain,(
    ! [E_17,F_18,A_13,B_14,C_15,D_16] : k2_xboole_0(k3_enumset1(A_13,B_14,C_15,D_16,E_17),k1_tarski(F_18)) = k4_enumset1(A_13,B_14,C_15,D_16,E_17,F_18) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_41] : k2_tarski(A_41,A_41) = k1_tarski(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_285,plain,(
    ! [C_132,B_129,A_130,E_133,F_131,G_134,D_128] : k2_xboole_0(k3_enumset1(A_130,B_129,C_132,D_128,E_133),k2_tarski(F_131,G_134)) = k5_enumset1(A_130,B_129,C_132,D_128,E_133,F_131,G_134) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_297,plain,(
    ! [C_132,B_129,A_130,E_133,A_41,D_128] : k5_enumset1(A_130,B_129,C_132,D_128,E_133,A_41,A_41) = k2_xboole_0(k3_enumset1(A_130,B_129,C_132,D_128,E_133),k1_tarski(A_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_285])).

tff(c_398,plain,(
    ! [C_154,A_155,D_158,E_156,B_157,A_153] : k5_enumset1(A_153,B_157,C_154,D_158,E_156,A_155,A_155) = k4_enumset1(A_153,B_157,C_154,D_158,E_156,A_155) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_297])).

tff(c_26,plain,(
    ! [D_59,A_56,B_57,F_61,C_58,E_60] : k5_enumset1(A_56,A_56,B_57,C_58,D_59,E_60,F_61) = k4_enumset1(A_56,B_57,C_58,D_59,E_60,F_61) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_405,plain,(
    ! [C_154,A_155,D_158,E_156,B_157] : k4_enumset1(B_157,C_154,D_158,E_156,A_155,A_155) = k4_enumset1(B_157,B_157,C_154,D_158,E_156,A_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_26])).

tff(c_417,plain,(
    ! [B_161,D_162,C_159,A_160,E_163] : k4_enumset1(B_161,C_159,D_162,E_163,A_160,A_160) = k3_enumset1(B_161,C_159,D_162,E_163,A_160) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_405])).

tff(c_427,plain,(
    ! [C_159,D_162,E_163,A_160] : k3_enumset1(C_159,D_162,E_163,A_160,A_160) = k3_enumset1(C_159,C_159,D_162,E_163,A_160) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_24])).

tff(c_440,plain,(
    ! [C_164,D_165,E_166,A_167] : k3_enumset1(C_164,D_165,E_166,A_167,A_167) = k2_enumset1(C_164,D_165,E_166,A_167) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_427])).

tff(c_462,plain,(
    ! [D_165,E_166,A_167] : k2_enumset1(D_165,E_166,A_167,A_167) = k2_enumset1(D_165,D_165,E_166,A_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_22])).

tff(c_481,plain,(
    ! [D_165,E_166,A_167] : k2_enumset1(D_165,E_166,A_167,A_167) = k1_enumset1(D_165,E_166,A_167) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_462])).

tff(c_437,plain,(
    ! [C_159,D_162,E_163,A_160] : k3_enumset1(C_159,D_162,E_163,A_160,A_160) = k2_enumset1(C_159,D_162,E_163,A_160) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_427])).

tff(c_414,plain,(
    ! [C_154,A_155,D_158,E_156,B_157] : k4_enumset1(B_157,C_154,D_158,E_156,A_155,A_155) = k3_enumset1(B_157,C_154,D_158,E_156,A_155) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_405])).

tff(c_294,plain,(
    ! [A_47,F_131,D_50,G_134,C_49,B_48] : k5_enumset1(A_47,A_47,B_48,C_49,D_50,F_131,G_134) = k2_xboole_0(k2_enumset1(A_47,B_48,C_49,D_50),k2_tarski(F_131,G_134)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_285])).

tff(c_300,plain,(
    ! [A_47,F_131,D_50,G_134,C_49,B_48] : k2_xboole_0(k2_enumset1(A_47,B_48,C_49,D_50),k2_tarski(F_131,G_134)) = k4_enumset1(A_47,B_48,C_49,D_50,F_131,G_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_294])).

tff(c_18,plain,(
    ! [A_42,B_43] : k1_enumset1(A_42,A_42,B_43) = k2_tarski(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_484,plain,(
    ! [D_168,E_175,B_171,C_172,G_170,H_174,F_169,A_173] : k2_xboole_0(k2_enumset1(A_173,B_171,C_172,D_168),k2_enumset1(E_175,F_169,G_170,H_174)) = k6_enumset1(A_173,B_171,C_172,D_168,E_175,F_169,G_170,H_174) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1582,plain,(
    ! [C_255,D_256,A_254,C_258,B_260,A_259,B_257] : k6_enumset1(A_254,B_260,C_258,D_256,A_259,A_259,B_257,C_255) = k2_xboole_0(k2_enumset1(A_254,B_260,C_258,D_256),k1_enumset1(A_259,B_257,C_255)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_484])).

tff(c_1638,plain,(
    ! [B_43,D_256,A_42,A_254,C_258,B_260] : k6_enumset1(A_254,B_260,C_258,D_256,A_42,A_42,A_42,B_43) = k2_xboole_0(k2_enumset1(A_254,B_260,C_258,D_256),k2_tarski(A_42,B_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1582])).

tff(c_3612,plain,(
    ! [B_330,D_333,A_332,C_335,B_331,A_334] : k6_enumset1(A_334,B_331,C_335,D_333,A_332,A_332,A_332,B_330) = k4_enumset1(A_334,B_331,C_335,D_333,A_332,B_330) ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_1638])).

tff(c_382,plain,(
    ! [G_151,D_149,C_147,A_145,H_150,B_152,F_148,E_146] : k2_xboole_0(k2_tarski(A_145,B_152),k4_enumset1(C_147,D_149,E_146,F_148,G_151,H_150)) = k6_enumset1(A_145,B_152,C_147,D_149,E_146,F_148,G_151,H_150) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_394,plain,(
    ! [G_151,D_149,C_147,H_150,A_41,F_148,E_146] : k6_enumset1(A_41,A_41,C_147,D_149,E_146,F_148,G_151,H_150) = k2_xboole_0(k1_tarski(A_41),k4_enumset1(C_147,D_149,E_146,F_148,G_151,H_150)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_382])).

tff(c_3619,plain,(
    ! [B_330,D_333,A_332,C_335,B_331] : k4_enumset1(B_331,B_331,C_335,D_333,A_332,B_330) = k2_xboole_0(k1_tarski(B_331),k4_enumset1(C_335,D_333,A_332,A_332,A_332,B_330)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3612,c_394])).

tff(c_36718,plain,(
    ! [B_761,A_760,B_759,D_762,C_758] : k2_xboole_0(k1_tarski(B_761),k4_enumset1(C_758,D_762,A_760,A_760,A_760,B_759)) = k3_enumset1(B_761,C_758,D_762,A_760,B_759) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3619])).

tff(c_36927,plain,(
    ! [B_761,B_157,C_154,A_155] : k2_xboole_0(k1_tarski(B_761),k3_enumset1(B_157,C_154,A_155,A_155,A_155)) = k3_enumset1(B_761,B_157,C_154,A_155,A_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_36718])).

tff(c_71002,plain,(
    ! [B_1014,B_1015,C_1016,A_1017] : k2_xboole_0(k1_tarski(B_1014),k1_enumset1(B_1015,C_1016,A_1017)) = k2_enumset1(B_1014,B_1015,C_1016,A_1017) ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_437,c_437,c_36927])).

tff(c_72755,plain,(
    ! [B_1026,B_1027,A_1028,C_1029] : k2_xboole_0(k1_tarski(B_1026),k1_enumset1(B_1027,A_1028,C_1029)) = k2_enumset1(B_1026,A_1028,B_1027,C_1029) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_71002])).

tff(c_36983,plain,(
    ! [B_761,B_157,C_154,A_155] : k2_xboole_0(k1_tarski(B_761),k1_enumset1(B_157,C_154,A_155)) = k2_enumset1(B_761,B_157,C_154,A_155) ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_437,c_437,c_36927])).

tff(c_72761,plain,(
    ! [B_1026,B_1027,A_1028,C_1029] : k2_enumset1(B_1026,B_1027,A_1028,C_1029) = k2_enumset1(B_1026,A_1028,B_1027,C_1029) ),
    inference(superposition,[status(thm),theory(equality)],[c_72755,c_36983])).

tff(c_30,plain,(
    k2_enumset1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_enumset1('#skF_1','#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_72850,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72761,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:13:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.86/7.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.86/7.60  
% 13.86/7.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.86/7.60  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.86/7.60  
% 13.86/7.60  %Foreground sorts:
% 13.86/7.60  
% 13.86/7.60  
% 13.86/7.60  %Background operators:
% 13.86/7.60  
% 13.86/7.60  
% 13.86/7.60  %Foreground operators:
% 13.86/7.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.86/7.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.86/7.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.86/7.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.86/7.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.86/7.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.86/7.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.86/7.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.86/7.60  tff('#skF_2', type, '#skF_2': $i).
% 13.86/7.60  tff('#skF_3', type, '#skF_3': $i).
% 13.86/7.60  tff('#skF_1', type, '#skF_1': $i).
% 13.86/7.60  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.86/7.60  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.86/7.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.86/7.60  tff('#skF_4', type, '#skF_4': $i).
% 13.86/7.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.86/7.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.86/7.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.86/7.60  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.86/7.60  
% 14.00/7.62  tff(f_53, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_enumset1)).
% 14.00/7.62  tff(f_45, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 14.00/7.62  tff(f_47, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 14.00/7.62  tff(f_49, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 14.00/7.62  tff(f_33, axiom, (![A, B, C, D, E, F]: (k4_enumset1(A, B, C, D, E, F) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k1_tarski(F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 14.00/7.62  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 14.00/7.62  tff(f_37, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k3_enumset1(A, B, C, D, E), k2_tarski(F, G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_enumset1)).
% 14.00/7.62  tff(f_51, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 14.00/7.62  tff(f_43, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 14.00/7.62  tff(f_31, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_enumset1(A, B, C, D), k2_enumset1(E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 14.00/7.62  tff(f_39, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k2_tarski(A, B), k4_enumset1(C, D, E, F, G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_enumset1)).
% 14.00/7.62  tff(f_56, negated_conjecture, ~(![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(A, C, B, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_enumset1)).
% 14.00/7.62  tff(c_28, plain, (![B_63, A_62, C_64]: (k1_enumset1(B_63, A_62, C_64)=k1_enumset1(A_62, B_63, C_64))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.00/7.62  tff(c_20, plain, (![A_44, B_45, C_46]: (k2_enumset1(A_44, A_44, B_45, C_46)=k1_enumset1(A_44, B_45, C_46))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.00/7.62  tff(c_22, plain, (![A_47, B_48, C_49, D_50]: (k3_enumset1(A_47, A_47, B_48, C_49, D_50)=k2_enumset1(A_47, B_48, C_49, D_50))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.00/7.62  tff(c_24, plain, (![B_52, E_55, C_53, D_54, A_51]: (k4_enumset1(A_51, A_51, B_52, C_53, D_54, E_55)=k3_enumset1(A_51, B_52, C_53, D_54, E_55))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.00/7.62  tff(c_8, plain, (![E_17, F_18, A_13, B_14, C_15, D_16]: (k2_xboole_0(k3_enumset1(A_13, B_14, C_15, D_16, E_17), k1_tarski(F_18))=k4_enumset1(A_13, B_14, C_15, D_16, E_17, F_18))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.00/7.62  tff(c_16, plain, (![A_41]: (k2_tarski(A_41, A_41)=k1_tarski(A_41))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.00/7.62  tff(c_285, plain, (![C_132, B_129, A_130, E_133, F_131, G_134, D_128]: (k2_xboole_0(k3_enumset1(A_130, B_129, C_132, D_128, E_133), k2_tarski(F_131, G_134))=k5_enumset1(A_130, B_129, C_132, D_128, E_133, F_131, G_134))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.00/7.62  tff(c_297, plain, (![C_132, B_129, A_130, E_133, A_41, D_128]: (k5_enumset1(A_130, B_129, C_132, D_128, E_133, A_41, A_41)=k2_xboole_0(k3_enumset1(A_130, B_129, C_132, D_128, E_133), k1_tarski(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_285])).
% 14.00/7.62  tff(c_398, plain, (![C_154, A_155, D_158, E_156, B_157, A_153]: (k5_enumset1(A_153, B_157, C_154, D_158, E_156, A_155, A_155)=k4_enumset1(A_153, B_157, C_154, D_158, E_156, A_155))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_297])).
% 14.00/7.62  tff(c_26, plain, (![D_59, A_56, B_57, F_61, C_58, E_60]: (k5_enumset1(A_56, A_56, B_57, C_58, D_59, E_60, F_61)=k4_enumset1(A_56, B_57, C_58, D_59, E_60, F_61))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.00/7.62  tff(c_405, plain, (![C_154, A_155, D_158, E_156, B_157]: (k4_enumset1(B_157, C_154, D_158, E_156, A_155, A_155)=k4_enumset1(B_157, B_157, C_154, D_158, E_156, A_155))), inference(superposition, [status(thm), theory('equality')], [c_398, c_26])).
% 14.00/7.62  tff(c_417, plain, (![B_161, D_162, C_159, A_160, E_163]: (k4_enumset1(B_161, C_159, D_162, E_163, A_160, A_160)=k3_enumset1(B_161, C_159, D_162, E_163, A_160))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_405])).
% 14.00/7.62  tff(c_427, plain, (![C_159, D_162, E_163, A_160]: (k3_enumset1(C_159, D_162, E_163, A_160, A_160)=k3_enumset1(C_159, C_159, D_162, E_163, A_160))), inference(superposition, [status(thm), theory('equality')], [c_417, c_24])).
% 14.00/7.62  tff(c_440, plain, (![C_164, D_165, E_166, A_167]: (k3_enumset1(C_164, D_165, E_166, A_167, A_167)=k2_enumset1(C_164, D_165, E_166, A_167))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_427])).
% 14.00/7.62  tff(c_462, plain, (![D_165, E_166, A_167]: (k2_enumset1(D_165, E_166, A_167, A_167)=k2_enumset1(D_165, D_165, E_166, A_167))), inference(superposition, [status(thm), theory('equality')], [c_440, c_22])).
% 14.00/7.62  tff(c_481, plain, (![D_165, E_166, A_167]: (k2_enumset1(D_165, E_166, A_167, A_167)=k1_enumset1(D_165, E_166, A_167))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_462])).
% 14.00/7.62  tff(c_437, plain, (![C_159, D_162, E_163, A_160]: (k3_enumset1(C_159, D_162, E_163, A_160, A_160)=k2_enumset1(C_159, D_162, E_163, A_160))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_427])).
% 14.00/7.62  tff(c_414, plain, (![C_154, A_155, D_158, E_156, B_157]: (k4_enumset1(B_157, C_154, D_158, E_156, A_155, A_155)=k3_enumset1(B_157, C_154, D_158, E_156, A_155))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_405])).
% 14.00/7.62  tff(c_294, plain, (![A_47, F_131, D_50, G_134, C_49, B_48]: (k5_enumset1(A_47, A_47, B_48, C_49, D_50, F_131, G_134)=k2_xboole_0(k2_enumset1(A_47, B_48, C_49, D_50), k2_tarski(F_131, G_134)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_285])).
% 14.00/7.62  tff(c_300, plain, (![A_47, F_131, D_50, G_134, C_49, B_48]: (k2_xboole_0(k2_enumset1(A_47, B_48, C_49, D_50), k2_tarski(F_131, G_134))=k4_enumset1(A_47, B_48, C_49, D_50, F_131, G_134))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_294])).
% 14.00/7.62  tff(c_18, plain, (![A_42, B_43]: (k1_enumset1(A_42, A_42, B_43)=k2_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.00/7.62  tff(c_484, plain, (![D_168, E_175, B_171, C_172, G_170, H_174, F_169, A_173]: (k2_xboole_0(k2_enumset1(A_173, B_171, C_172, D_168), k2_enumset1(E_175, F_169, G_170, H_174))=k6_enumset1(A_173, B_171, C_172, D_168, E_175, F_169, G_170, H_174))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.00/7.62  tff(c_1582, plain, (![C_255, D_256, A_254, C_258, B_260, A_259, B_257]: (k6_enumset1(A_254, B_260, C_258, D_256, A_259, A_259, B_257, C_255)=k2_xboole_0(k2_enumset1(A_254, B_260, C_258, D_256), k1_enumset1(A_259, B_257, C_255)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_484])).
% 14.00/7.62  tff(c_1638, plain, (![B_43, D_256, A_42, A_254, C_258, B_260]: (k6_enumset1(A_254, B_260, C_258, D_256, A_42, A_42, A_42, B_43)=k2_xboole_0(k2_enumset1(A_254, B_260, C_258, D_256), k2_tarski(A_42, B_43)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1582])).
% 14.00/7.62  tff(c_3612, plain, (![B_330, D_333, A_332, C_335, B_331, A_334]: (k6_enumset1(A_334, B_331, C_335, D_333, A_332, A_332, A_332, B_330)=k4_enumset1(A_334, B_331, C_335, D_333, A_332, B_330))), inference(demodulation, [status(thm), theory('equality')], [c_300, c_1638])).
% 14.00/7.62  tff(c_382, plain, (![G_151, D_149, C_147, A_145, H_150, B_152, F_148, E_146]: (k2_xboole_0(k2_tarski(A_145, B_152), k4_enumset1(C_147, D_149, E_146, F_148, G_151, H_150))=k6_enumset1(A_145, B_152, C_147, D_149, E_146, F_148, G_151, H_150))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.00/7.62  tff(c_394, plain, (![G_151, D_149, C_147, H_150, A_41, F_148, E_146]: (k6_enumset1(A_41, A_41, C_147, D_149, E_146, F_148, G_151, H_150)=k2_xboole_0(k1_tarski(A_41), k4_enumset1(C_147, D_149, E_146, F_148, G_151, H_150)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_382])).
% 14.00/7.62  tff(c_3619, plain, (![B_330, D_333, A_332, C_335, B_331]: (k4_enumset1(B_331, B_331, C_335, D_333, A_332, B_330)=k2_xboole_0(k1_tarski(B_331), k4_enumset1(C_335, D_333, A_332, A_332, A_332, B_330)))), inference(superposition, [status(thm), theory('equality')], [c_3612, c_394])).
% 14.00/7.62  tff(c_36718, plain, (![B_761, A_760, B_759, D_762, C_758]: (k2_xboole_0(k1_tarski(B_761), k4_enumset1(C_758, D_762, A_760, A_760, A_760, B_759))=k3_enumset1(B_761, C_758, D_762, A_760, B_759))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3619])).
% 14.00/7.62  tff(c_36927, plain, (![B_761, B_157, C_154, A_155]: (k2_xboole_0(k1_tarski(B_761), k3_enumset1(B_157, C_154, A_155, A_155, A_155))=k3_enumset1(B_761, B_157, C_154, A_155, A_155))), inference(superposition, [status(thm), theory('equality')], [c_414, c_36718])).
% 14.00/7.62  tff(c_71002, plain, (![B_1014, B_1015, C_1016, A_1017]: (k2_xboole_0(k1_tarski(B_1014), k1_enumset1(B_1015, C_1016, A_1017))=k2_enumset1(B_1014, B_1015, C_1016, A_1017))), inference(demodulation, [status(thm), theory('equality')], [c_481, c_437, c_437, c_36927])).
% 14.00/7.62  tff(c_72755, plain, (![B_1026, B_1027, A_1028, C_1029]: (k2_xboole_0(k1_tarski(B_1026), k1_enumset1(B_1027, A_1028, C_1029))=k2_enumset1(B_1026, A_1028, B_1027, C_1029))), inference(superposition, [status(thm), theory('equality')], [c_28, c_71002])).
% 14.00/7.62  tff(c_36983, plain, (![B_761, B_157, C_154, A_155]: (k2_xboole_0(k1_tarski(B_761), k1_enumset1(B_157, C_154, A_155))=k2_enumset1(B_761, B_157, C_154, A_155))), inference(demodulation, [status(thm), theory('equality')], [c_481, c_437, c_437, c_36927])).
% 14.00/7.62  tff(c_72761, plain, (![B_1026, B_1027, A_1028, C_1029]: (k2_enumset1(B_1026, B_1027, A_1028, C_1029)=k2_enumset1(B_1026, A_1028, B_1027, C_1029))), inference(superposition, [status(thm), theory('equality')], [c_72755, c_36983])).
% 14.00/7.62  tff(c_30, plain, (k2_enumset1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_enumset1('#skF_1', '#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.00/7.62  tff(c_72850, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72761, c_30])).
% 14.00/7.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.00/7.62  
% 14.00/7.62  Inference rules
% 14.00/7.62  ----------------------
% 14.00/7.62  #Ref     : 0
% 14.00/7.62  #Sup     : 15377
% 14.00/7.62  #Fact    : 0
% 14.00/7.62  #Define  : 0
% 14.00/7.62  #Split   : 0
% 14.00/7.62  #Chain   : 0
% 14.00/7.62  #Close   : 0
% 14.00/7.62  
% 14.00/7.62  Ordering : KBO
% 14.00/7.62  
% 14.00/7.62  Simplification rules
% 14.00/7.62  ----------------------
% 14.00/7.62  #Subsume      : 236
% 14.00/7.62  #Demod        : 31081
% 14.00/7.62  #Tautology    : 13520
% 14.00/7.62  #SimpNegUnit  : 0
% 14.00/7.62  #BackRed      : 16
% 14.00/7.62  
% 14.00/7.62  #Partial instantiations: 0
% 14.00/7.62  #Strategies tried      : 1
% 14.00/7.62  
% 14.00/7.62  Timing (in seconds)
% 14.00/7.62  ----------------------
% 14.00/7.62  Preprocessing        : 0.31
% 14.00/7.62  Parsing              : 0.16
% 14.00/7.62  CNF conversion       : 0.02
% 14.00/7.62  Main loop            : 6.56
% 14.00/7.62  Inferencing          : 1.59
% 14.00/7.62  Reduction            : 3.73
% 14.00/7.62  Demodulation         : 3.39
% 14.00/7.62  BG Simplification    : 0.12
% 14.00/7.62  Subsumption          : 0.91
% 14.00/7.62  Abstraction          : 0.27
% 14.00/7.62  MUC search           : 0.00
% 14.00/7.62  Cooper               : 0.00
% 14.00/7.62  Total                : 6.90
% 14.00/7.62  Index Insertion      : 0.00
% 14.00/7.62  Index Deletion       : 0.00
% 14.00/7.62  Index Matching       : 0.00
% 14.00/7.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
