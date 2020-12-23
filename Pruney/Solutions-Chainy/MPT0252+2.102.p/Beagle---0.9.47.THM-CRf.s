%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:13 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 156 expanded)
%              Number of leaves         :   35 (  65 expanded)
%              Depth                    :   18
%              Number of atoms          :   94 ( 185 expanded)
%              Number of equality atoms :   34 (  75 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k2_tarski(G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_40,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(A_5,k2_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_22,B_23] : k1_enumset1(A_22,A_22,B_23) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_241,plain,(
    ! [D_101,C_102,B_103,A_104] : k2_enumset1(D_101,C_102,B_103,A_104) = k2_enumset1(A_104,B_103,C_102,D_101) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_24,B_25,C_26] : k2_enumset1(A_24,A_24,B_25,C_26) = k1_enumset1(A_24,B_25,C_26) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_257,plain,(
    ! [D_101,C_102,B_103] : k2_enumset1(D_101,C_102,B_103,B_103) = k1_enumset1(B_103,C_102,D_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_22])).

tff(c_24,plain,(
    ! [A_27,B_28,C_29,D_30] : k3_enumset1(A_27,A_27,B_28,C_29,D_30) = k2_enumset1(A_27,B_28,C_29,D_30) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [A_31,C_33,B_32,E_35,D_34] : k4_enumset1(A_31,A_31,B_32,C_33,D_34,E_35) = k3_enumset1(A_31,B_32,C_33,D_34,E_35) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [F_41,D_39,A_36,E_40,C_38,B_37] : k5_enumset1(A_36,A_36,B_37,C_38,D_39,E_40,F_41) = k4_enumset1(A_36,B_37,C_38,D_39,E_40,F_41) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [B_43,A_42,D_45,G_48,E_46,C_44,F_47] : k6_enumset1(A_42,A_42,B_43,C_44,D_45,E_46,F_47,G_48) = k5_enumset1(A_42,B_43,C_44,D_45,E_46,F_47,G_48) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_565,plain,(
    ! [G_165,D_161,E_163,H_166,C_167,A_164,B_162,F_160] : k2_xboole_0(k4_enumset1(A_164,B_162,C_167,D_161,E_163,F_160),k2_tarski(G_165,H_166)) = k6_enumset1(A_164,B_162,C_167,D_161,E_163,F_160,G_165,H_166) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_594,plain,(
    ! [D_176,F_177,H_170,E_175,B_171,C_172,G_174,A_173] : r1_tarski(k4_enumset1(A_173,B_171,C_172,D_176,E_175,F_177),k6_enumset1(A_173,B_171,C_172,D_176,E_175,F_177,G_174,H_170)) ),
    inference(superposition,[status(thm),theory(equality)],[c_565,c_10])).

tff(c_599,plain,(
    ! [B_43,A_42,D_45,G_48,E_46,C_44,F_47] : r1_tarski(k4_enumset1(A_42,A_42,B_43,C_44,D_45,E_46),k5_enumset1(A_42,B_43,C_44,D_45,E_46,F_47,G_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_594])).

tff(c_606,plain,(
    ! [B_180,D_179,E_178,A_182,C_184,F_183,G_181] : r1_tarski(k3_enumset1(A_182,B_180,C_184,D_179,E_178),k5_enumset1(A_182,B_180,C_184,D_179,E_178,F_183,G_181)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_599])).

tff(c_611,plain,(
    ! [F_41,D_39,A_36,E_40,C_38,B_37] : r1_tarski(k3_enumset1(A_36,A_36,B_37,C_38,D_39),k4_enumset1(A_36,B_37,C_38,D_39,E_40,F_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_606])).

tff(c_618,plain,(
    ! [B_188,F_185,E_190,D_187,A_186,C_189] : r1_tarski(k2_enumset1(A_186,B_188,C_189,D_187),k4_enumset1(A_186,B_188,C_189,D_187,E_190,F_185)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_611])).

tff(c_623,plain,(
    ! [A_31,C_33,B_32,E_35,D_34] : r1_tarski(k2_enumset1(A_31,A_31,B_32,C_33),k3_enumset1(A_31,B_32,C_33,D_34,E_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_618])).

tff(c_639,plain,(
    ! [B_192,C_195,A_194,E_193,D_191] : r1_tarski(k1_enumset1(A_194,B_192,C_195),k3_enumset1(A_194,B_192,C_195,D_191,E_193)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_623])).

tff(c_650,plain,(
    ! [A_27,B_28,C_29,D_30] : r1_tarski(k1_enumset1(A_27,A_27,B_28),k2_enumset1(A_27,B_28,C_29,D_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_639])).

tff(c_681,plain,(
    ! [A_203,B_204,C_205,D_206] : r1_tarski(k2_tarski(A_203,B_204),k2_enumset1(A_203,B_204,C_205,D_206)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_650])).

tff(c_38,plain,(
    ! [A_51,C_53,B_52] :
      ( r2_hidden(A_51,C_53)
      | ~ r1_tarski(k2_tarski(A_51,B_52),C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_710,plain,(
    ! [A_207,B_208,C_209,D_210] : r2_hidden(A_207,k2_enumset1(A_207,B_208,C_209,D_210)) ),
    inference(resolution,[status(thm)],[c_681,c_38])).

tff(c_723,plain,(
    ! [D_211,B_212,C_213] : r2_hidden(D_211,k1_enumset1(B_212,C_213,D_211)) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_710])).

tff(c_732,plain,(
    ! [B_23,A_22] : r2_hidden(B_23,k2_tarski(A_22,B_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_723])).

tff(c_193,plain,(
    ! [A_91,B_92] : k2_xboole_0(k1_tarski(A_91),k1_tarski(B_92)) = k2_tarski(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_102,plain,(
    ! [B_68,C_69,A_70] :
      ( r2_hidden(B_68,C_69)
      | ~ r1_tarski(k2_tarski(A_70,B_68),C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_116,plain,(
    ! [A_71,C_72] :
      ( r2_hidden(A_71,C_72)
      | ~ r1_tarski(k1_tarski(A_71),C_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_102])).

tff(c_126,plain,(
    ! [A_71,B_6] : r2_hidden(A_71,k2_xboole_0(k1_tarski(A_71),B_6)) ),
    inference(resolution,[status(thm)],[c_10,c_116])).

tff(c_199,plain,(
    ! [A_91,B_92] : r2_hidden(A_91,k2_tarski(A_91,B_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_126])).

tff(c_902,plain,(
    ! [D_246,C_247,B_248] : r1_tarski(k2_tarski(D_246,C_247),k1_enumset1(B_248,C_247,D_246)) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_681])).

tff(c_932,plain,(
    ! [B_249,A_250] : r1_tarski(k2_tarski(B_249,A_250),k2_tarski(A_250,B_249)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_902])).

tff(c_427,plain,(
    ! [A_121,B_122,C_123] :
      ( r1_tarski(k2_tarski(A_121,B_122),C_123)
      | ~ r2_hidden(B_122,C_123)
      | ~ r2_hidden(A_121,C_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_166,plain,(
    ! [A_85,B_86] :
      ( r2_xboole_0(A_85,B_86)
      | B_86 = A_85
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( ~ r2_xboole_0(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_178,plain,(
    ! [B_86,A_85] :
      ( ~ r1_tarski(B_86,A_85)
      | B_86 = A_85
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(resolution,[status(thm)],[c_166,c_8])).

tff(c_439,plain,(
    ! [A_121,B_122,C_123] :
      ( k2_tarski(A_121,B_122) = C_123
      | ~ r1_tarski(C_123,k2_tarski(A_121,B_122))
      | ~ r2_hidden(B_122,C_123)
      | ~ r2_hidden(A_121,C_123) ) ),
    inference(resolution,[status(thm)],[c_427,c_178])).

tff(c_935,plain,(
    ! [B_249,A_250] :
      ( k2_tarski(B_249,A_250) = k2_tarski(A_250,B_249)
      | ~ r2_hidden(B_249,k2_tarski(B_249,A_250))
      | ~ r2_hidden(A_250,k2_tarski(B_249,A_250)) ) ),
    inference(resolution,[status(thm)],[c_932,c_439])).

tff(c_962,plain,(
    ! [B_251,A_252] : k2_tarski(B_251,A_252) = k2_tarski(A_252,B_251) ),
    inference(demodulation,[status(thm),theory(equality)],[c_732,c_199,c_935])).

tff(c_32,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1121,plain,(
    ! [B_253,A_254] : k3_tarski(k2_tarski(B_253,A_254)) = k2_xboole_0(A_254,B_253) ),
    inference(superposition,[status(thm),theory(equality)],[c_962,c_32])).

tff(c_1127,plain,(
    ! [B_253,A_254] : k2_xboole_0(B_253,A_254) = k2_xboole_0(A_254,B_253) ),
    inference(superposition,[status(thm),theory(equality)],[c_1121,c_32])).

tff(c_42,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_310,plain,(
    ! [B_107,A_108] :
      ( ~ r1_tarski(B_107,A_108)
      | B_107 = A_108
      | ~ r1_tarski(A_108,B_107) ) ),
    inference(resolution,[status(thm)],[c_166,c_8])).

tff(c_327,plain,
    ( k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_310])).

tff(c_407,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_327])).

tff(c_1175,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1127,c_407])).

tff(c_1179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1175])).

tff(c_1180,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_133,plain,(
    ! [A_76,C_77,B_78] :
      ( r2_hidden(A_76,C_77)
      | ~ r1_tarski(k2_tarski(A_76,B_78),C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_146,plain,(
    ! [A_76,B_78,B_6] : r2_hidden(A_76,k2_xboole_0(k2_tarski(A_76,B_78),B_6)) ),
    inference(resolution,[status(thm)],[c_10,c_133])).

tff(c_1186,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1180,c_146])).

tff(c_1196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1186])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:13:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.51  
% 2.98/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.51  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.98/1.51  
% 2.98/1.51  %Foreground sorts:
% 2.98/1.51  
% 2.98/1.51  
% 2.98/1.51  %Background operators:
% 2.98/1.51  
% 2.98/1.51  
% 2.98/1.51  %Foreground operators:
% 2.98/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.98/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.98/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.98/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.98/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.98/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.98/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.98/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.51  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.98/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.98/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.98/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.98/1.51  
% 2.98/1.52  tff(f_72, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.98/1.52  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.98/1.52  tff(f_49, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.98/1.52  tff(f_41, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 2.98/1.52  tff(f_51, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.98/1.52  tff(f_53, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.98/1.52  tff(f_55, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.98/1.52  tff(f_57, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.98/1.52  tff(f_59, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.98/1.52  tff(f_45, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k2_tarski(G, H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_enumset1)).
% 2.98/1.52  tff(f_67, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.98/1.52  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.98/1.52  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.98/1.52  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.98/1.52  tff(f_37, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 2.98/1.52  tff(f_61, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.98/1.52  tff(c_40, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.98/1.52  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.98/1.52  tff(c_20, plain, (![A_22, B_23]: (k1_enumset1(A_22, A_22, B_23)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.98/1.52  tff(c_241, plain, (![D_101, C_102, B_103, A_104]: (k2_enumset1(D_101, C_102, B_103, A_104)=k2_enumset1(A_104, B_103, C_102, D_101))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.98/1.52  tff(c_22, plain, (![A_24, B_25, C_26]: (k2_enumset1(A_24, A_24, B_25, C_26)=k1_enumset1(A_24, B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.98/1.52  tff(c_257, plain, (![D_101, C_102, B_103]: (k2_enumset1(D_101, C_102, B_103, B_103)=k1_enumset1(B_103, C_102, D_101))), inference(superposition, [status(thm), theory('equality')], [c_241, c_22])).
% 2.98/1.52  tff(c_24, plain, (![A_27, B_28, C_29, D_30]: (k3_enumset1(A_27, A_27, B_28, C_29, D_30)=k2_enumset1(A_27, B_28, C_29, D_30))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.98/1.52  tff(c_26, plain, (![A_31, C_33, B_32, E_35, D_34]: (k4_enumset1(A_31, A_31, B_32, C_33, D_34, E_35)=k3_enumset1(A_31, B_32, C_33, D_34, E_35))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.98/1.52  tff(c_28, plain, (![F_41, D_39, A_36, E_40, C_38, B_37]: (k5_enumset1(A_36, A_36, B_37, C_38, D_39, E_40, F_41)=k4_enumset1(A_36, B_37, C_38, D_39, E_40, F_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.98/1.52  tff(c_30, plain, (![B_43, A_42, D_45, G_48, E_46, C_44, F_47]: (k6_enumset1(A_42, A_42, B_43, C_44, D_45, E_46, F_47, G_48)=k5_enumset1(A_42, B_43, C_44, D_45, E_46, F_47, G_48))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.98/1.52  tff(c_565, plain, (![G_165, D_161, E_163, H_166, C_167, A_164, B_162, F_160]: (k2_xboole_0(k4_enumset1(A_164, B_162, C_167, D_161, E_163, F_160), k2_tarski(G_165, H_166))=k6_enumset1(A_164, B_162, C_167, D_161, E_163, F_160, G_165, H_166))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.98/1.52  tff(c_594, plain, (![D_176, F_177, H_170, E_175, B_171, C_172, G_174, A_173]: (r1_tarski(k4_enumset1(A_173, B_171, C_172, D_176, E_175, F_177), k6_enumset1(A_173, B_171, C_172, D_176, E_175, F_177, G_174, H_170)))), inference(superposition, [status(thm), theory('equality')], [c_565, c_10])).
% 2.98/1.52  tff(c_599, plain, (![B_43, A_42, D_45, G_48, E_46, C_44, F_47]: (r1_tarski(k4_enumset1(A_42, A_42, B_43, C_44, D_45, E_46), k5_enumset1(A_42, B_43, C_44, D_45, E_46, F_47, G_48)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_594])).
% 2.98/1.52  tff(c_606, plain, (![B_180, D_179, E_178, A_182, C_184, F_183, G_181]: (r1_tarski(k3_enumset1(A_182, B_180, C_184, D_179, E_178), k5_enumset1(A_182, B_180, C_184, D_179, E_178, F_183, G_181)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_599])).
% 2.98/1.52  tff(c_611, plain, (![F_41, D_39, A_36, E_40, C_38, B_37]: (r1_tarski(k3_enumset1(A_36, A_36, B_37, C_38, D_39), k4_enumset1(A_36, B_37, C_38, D_39, E_40, F_41)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_606])).
% 2.98/1.52  tff(c_618, plain, (![B_188, F_185, E_190, D_187, A_186, C_189]: (r1_tarski(k2_enumset1(A_186, B_188, C_189, D_187), k4_enumset1(A_186, B_188, C_189, D_187, E_190, F_185)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_611])).
% 2.98/1.52  tff(c_623, plain, (![A_31, C_33, B_32, E_35, D_34]: (r1_tarski(k2_enumset1(A_31, A_31, B_32, C_33), k3_enumset1(A_31, B_32, C_33, D_34, E_35)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_618])).
% 2.98/1.52  tff(c_639, plain, (![B_192, C_195, A_194, E_193, D_191]: (r1_tarski(k1_enumset1(A_194, B_192, C_195), k3_enumset1(A_194, B_192, C_195, D_191, E_193)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_623])).
% 2.98/1.52  tff(c_650, plain, (![A_27, B_28, C_29, D_30]: (r1_tarski(k1_enumset1(A_27, A_27, B_28), k2_enumset1(A_27, B_28, C_29, D_30)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_639])).
% 2.98/1.52  tff(c_681, plain, (![A_203, B_204, C_205, D_206]: (r1_tarski(k2_tarski(A_203, B_204), k2_enumset1(A_203, B_204, C_205, D_206)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_650])).
% 2.98/1.52  tff(c_38, plain, (![A_51, C_53, B_52]: (r2_hidden(A_51, C_53) | ~r1_tarski(k2_tarski(A_51, B_52), C_53))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.98/1.52  tff(c_710, plain, (![A_207, B_208, C_209, D_210]: (r2_hidden(A_207, k2_enumset1(A_207, B_208, C_209, D_210)))), inference(resolution, [status(thm)], [c_681, c_38])).
% 2.98/1.52  tff(c_723, plain, (![D_211, B_212, C_213]: (r2_hidden(D_211, k1_enumset1(B_212, C_213, D_211)))), inference(superposition, [status(thm), theory('equality')], [c_257, c_710])).
% 2.98/1.52  tff(c_732, plain, (![B_23, A_22]: (r2_hidden(B_23, k2_tarski(A_22, B_23)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_723])).
% 2.98/1.52  tff(c_193, plain, (![A_91, B_92]: (k2_xboole_0(k1_tarski(A_91), k1_tarski(B_92))=k2_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.98/1.52  tff(c_18, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.98/1.52  tff(c_102, plain, (![B_68, C_69, A_70]: (r2_hidden(B_68, C_69) | ~r1_tarski(k2_tarski(A_70, B_68), C_69))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.98/1.52  tff(c_116, plain, (![A_71, C_72]: (r2_hidden(A_71, C_72) | ~r1_tarski(k1_tarski(A_71), C_72))), inference(superposition, [status(thm), theory('equality')], [c_18, c_102])).
% 2.98/1.52  tff(c_126, plain, (![A_71, B_6]: (r2_hidden(A_71, k2_xboole_0(k1_tarski(A_71), B_6)))), inference(resolution, [status(thm)], [c_10, c_116])).
% 2.98/1.52  tff(c_199, plain, (![A_91, B_92]: (r2_hidden(A_91, k2_tarski(A_91, B_92)))), inference(superposition, [status(thm), theory('equality')], [c_193, c_126])).
% 2.98/1.52  tff(c_902, plain, (![D_246, C_247, B_248]: (r1_tarski(k2_tarski(D_246, C_247), k1_enumset1(B_248, C_247, D_246)))), inference(superposition, [status(thm), theory('equality')], [c_257, c_681])).
% 2.98/1.52  tff(c_932, plain, (![B_249, A_250]: (r1_tarski(k2_tarski(B_249, A_250), k2_tarski(A_250, B_249)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_902])).
% 2.98/1.52  tff(c_427, plain, (![A_121, B_122, C_123]: (r1_tarski(k2_tarski(A_121, B_122), C_123) | ~r2_hidden(B_122, C_123) | ~r2_hidden(A_121, C_123))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.98/1.52  tff(c_166, plain, (![A_85, B_86]: (r2_xboole_0(A_85, B_86) | B_86=A_85 | ~r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.98/1.52  tff(c_8, plain, (![B_4, A_3]: (~r2_xboole_0(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.98/1.52  tff(c_178, plain, (![B_86, A_85]: (~r1_tarski(B_86, A_85) | B_86=A_85 | ~r1_tarski(A_85, B_86))), inference(resolution, [status(thm)], [c_166, c_8])).
% 2.98/1.52  tff(c_439, plain, (![A_121, B_122, C_123]: (k2_tarski(A_121, B_122)=C_123 | ~r1_tarski(C_123, k2_tarski(A_121, B_122)) | ~r2_hidden(B_122, C_123) | ~r2_hidden(A_121, C_123))), inference(resolution, [status(thm)], [c_427, c_178])).
% 2.98/1.52  tff(c_935, plain, (![B_249, A_250]: (k2_tarski(B_249, A_250)=k2_tarski(A_250, B_249) | ~r2_hidden(B_249, k2_tarski(B_249, A_250)) | ~r2_hidden(A_250, k2_tarski(B_249, A_250)))), inference(resolution, [status(thm)], [c_932, c_439])).
% 2.98/1.52  tff(c_962, plain, (![B_251, A_252]: (k2_tarski(B_251, A_252)=k2_tarski(A_252, B_251))), inference(demodulation, [status(thm), theory('equality')], [c_732, c_199, c_935])).
% 2.98/1.52  tff(c_32, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.98/1.52  tff(c_1121, plain, (![B_253, A_254]: (k3_tarski(k2_tarski(B_253, A_254))=k2_xboole_0(A_254, B_253))), inference(superposition, [status(thm), theory('equality')], [c_962, c_32])).
% 2.98/1.52  tff(c_1127, plain, (![B_253, A_254]: (k2_xboole_0(B_253, A_254)=k2_xboole_0(A_254, B_253))), inference(superposition, [status(thm), theory('equality')], [c_1121, c_32])).
% 2.98/1.52  tff(c_42, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.98/1.52  tff(c_310, plain, (![B_107, A_108]: (~r1_tarski(B_107, A_108) | B_107=A_108 | ~r1_tarski(A_108, B_107))), inference(resolution, [status(thm)], [c_166, c_8])).
% 2.98/1.52  tff(c_327, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_310])).
% 2.98/1.52  tff(c_407, plain, (~r1_tarski('#skF_3', k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_327])).
% 2.98/1.52  tff(c_1175, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1127, c_407])).
% 2.98/1.52  tff(c_1179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_1175])).
% 2.98/1.52  tff(c_1180, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_327])).
% 2.98/1.52  tff(c_133, plain, (![A_76, C_77, B_78]: (r2_hidden(A_76, C_77) | ~r1_tarski(k2_tarski(A_76, B_78), C_77))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.98/1.52  tff(c_146, plain, (![A_76, B_78, B_6]: (r2_hidden(A_76, k2_xboole_0(k2_tarski(A_76, B_78), B_6)))), inference(resolution, [status(thm)], [c_10, c_133])).
% 2.98/1.52  tff(c_1186, plain, (r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1180, c_146])).
% 2.98/1.52  tff(c_1196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_1186])).
% 2.98/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.52  
% 2.98/1.52  Inference rules
% 2.98/1.52  ----------------------
% 2.98/1.52  #Ref     : 0
% 2.98/1.52  #Sup     : 274
% 2.98/1.52  #Fact    : 0
% 2.98/1.52  #Define  : 0
% 2.98/1.53  #Split   : 1
% 2.98/1.53  #Chain   : 0
% 2.98/1.53  #Close   : 0
% 2.98/1.53  
% 2.98/1.53  Ordering : KBO
% 2.98/1.53  
% 2.98/1.53  Simplification rules
% 2.98/1.53  ----------------------
% 2.98/1.53  #Subsume      : 15
% 2.98/1.53  #Demod        : 134
% 2.98/1.53  #Tautology    : 155
% 2.98/1.53  #SimpNegUnit  : 1
% 2.98/1.53  #BackRed      : 5
% 2.98/1.53  
% 2.98/1.53  #Partial instantiations: 0
% 2.98/1.53  #Strategies tried      : 1
% 2.98/1.53  
% 2.98/1.53  Timing (in seconds)
% 2.98/1.53  ----------------------
% 2.98/1.53  Preprocessing        : 0.31
% 2.98/1.53  Parsing              : 0.16
% 2.98/1.53  CNF conversion       : 0.02
% 2.98/1.53  Main loop            : 0.41
% 2.98/1.53  Inferencing          : 0.16
% 2.98/1.53  Reduction            : 0.15
% 2.98/1.53  Demodulation         : 0.11
% 2.98/1.53  BG Simplification    : 0.02
% 2.98/1.53  Subsumption          : 0.06
% 2.98/1.53  Abstraction          : 0.03
% 2.98/1.53  MUC search           : 0.00
% 2.98/1.53  Cooper               : 0.00
% 2.98/1.53  Total                : 0.76
% 2.98/1.53  Index Insertion      : 0.00
% 2.98/1.53  Index Deletion       : 0.00
% 2.98/1.53  Index Matching       : 0.00
% 2.98/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
