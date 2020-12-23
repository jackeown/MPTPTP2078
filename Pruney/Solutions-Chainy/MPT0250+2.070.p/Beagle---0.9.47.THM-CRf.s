%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:41 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 203 expanded)
%              Number of leaves         :   33 (  83 expanded)
%              Depth                    :   17
%              Number of atoms          :   91 ( 241 expanded)
%              Number of equality atoms :   34 ( 109 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D,E] : k5_enumset1(A,A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,B,C,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).

tff(f_63,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

tff(c_46,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_193,plain,(
    ! [B_85,C_86,A_87] :
      ( r2_hidden(B_85,C_86)
      | ~ r1_tarski(k2_tarski(A_87,B_85),C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_211,plain,(
    ! [B_85,A_87] : r2_hidden(B_85,k2_tarski(A_87,B_85)) ),
    inference(resolution,[status(thm)],[c_8,c_193])).

tff(c_170,plain,(
    ! [A_80,C_81,B_82] :
      ( r2_hidden(A_80,C_81)
      | ~ r1_tarski(k2_tarski(A_80,B_82),C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_188,plain,(
    ! [A_80,B_82] : r2_hidden(A_80,k2_tarski(A_80,B_82)) ),
    inference(resolution,[status(thm)],[c_8,c_170])).

tff(c_24,plain,(
    ! [A_32,B_33] : k1_enumset1(A_32,A_32,B_33) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_34,B_35,C_36] : k2_enumset1(A_34,A_34,B_35,C_36) = k1_enumset1(A_34,B_35,C_36) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [A_37,B_38,C_39,D_40] : k3_enumset1(A_37,A_37,B_38,C_39,D_40) = k2_enumset1(A_37,B_38,C_39,D_40) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    ! [B_56,E_59,C_57,A_55,D_58] : k5_enumset1(A_55,A_55,A_55,B_56,C_57,D_58,E_59) = k3_enumset1(A_55,B_56,C_57,D_58,E_59) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_674,plain,(
    ! [B_150,C_147,D_148,F_149,E_145,A_146] : k5_enumset1(A_146,A_146,B_150,C_147,D_148,E_145,F_149) = k4_enumset1(A_146,B_150,C_147,D_148,E_145,F_149) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_687,plain,(
    ! [B_56,E_59,C_57,A_55,D_58] : k4_enumset1(A_55,A_55,B_56,C_57,D_58,E_59) = k3_enumset1(A_55,B_56,C_57,D_58,E_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_674])).

tff(c_790,plain,(
    ! [A_163,C_162,D_166,B_164,G_168,E_167,F_165] : k2_xboole_0(k4_enumset1(A_163,B_164,C_162,D_166,E_167,F_165),k1_tarski(G_168)) = k5_enumset1(A_163,B_164,C_162,D_166,E_167,F_165,G_168) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1187,plain,(
    ! [A_206,C_204,B_205,E_207,D_203,F_209,G_208] : r1_tarski(k4_enumset1(A_206,B_205,C_204,D_203,E_207,F_209),k5_enumset1(A_206,B_205,C_204,D_203,E_207,F_209,G_208)) ),
    inference(superposition,[status(thm),theory(equality)],[c_790,c_14])).

tff(c_1198,plain,(
    ! [B_56,E_59,C_57,A_55,D_58] : r1_tarski(k4_enumset1(A_55,A_55,A_55,B_56,C_57,D_58),k3_enumset1(A_55,B_56,C_57,D_58,E_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1187])).

tff(c_1215,plain,(
    ! [C_221,E_222,D_219,A_220,B_218] : r1_tarski(k2_enumset1(A_220,B_218,C_221,D_219),k3_enumset1(A_220,B_218,C_221,D_219,E_222)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_687,c_1198])).

tff(c_1220,plain,(
    ! [A_37,B_38,C_39,D_40] : r1_tarski(k2_enumset1(A_37,A_37,B_38,C_39),k2_enumset1(A_37,B_38,C_39,D_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1215])).

tff(c_1236,plain,(
    ! [A_223,B_224,C_225,D_226] : r1_tarski(k1_enumset1(A_223,B_224,C_225),k2_enumset1(A_223,B_224,C_225,D_226)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1220])).

tff(c_1250,plain,(
    ! [A_34,B_35,C_36] : r1_tarski(k1_enumset1(A_34,A_34,B_35),k1_enumset1(A_34,B_35,C_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1236])).

tff(c_1307,plain,(
    ! [A_233,B_234,C_235] : r1_tarski(k2_tarski(A_233,B_234),k1_enumset1(A_233,B_234,C_235)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1250])).

tff(c_42,plain,(
    ! [B_63,C_64,A_62] :
      ( r2_hidden(B_63,C_64)
      | ~ r1_tarski(k2_tarski(A_62,B_63),C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1326,plain,(
    ! [B_234,A_233,C_235] : r2_hidden(B_234,k1_enumset1(A_233,B_234,C_235)) ),
    inference(resolution,[status(thm)],[c_1307,c_42])).

tff(c_44,plain,(
    ! [A_62,C_64,B_63] :
      ( r2_hidden(A_62,C_64)
      | ~ r1_tarski(k2_tarski(A_62,B_63),C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1327,plain,(
    ! [A_233,B_234,C_235] : r2_hidden(A_233,k1_enumset1(A_233,B_234,C_235)) ),
    inference(resolution,[status(thm)],[c_1307,c_44])).

tff(c_384,plain,(
    ! [D_120,B_121,C_122,A_123] : k2_enumset1(D_120,B_121,C_122,A_123) = k2_enumset1(A_123,B_121,C_122,D_120) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_400,plain,(
    ! [D_120,B_121,C_122] : k2_enumset1(D_120,B_121,C_122,B_121) = k1_enumset1(B_121,C_122,D_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_26])).

tff(c_1462,plain,(
    ! [D_244,B_245,C_246] : r1_tarski(k1_enumset1(D_244,B_245,C_246),k1_enumset1(B_245,C_246,D_244)) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_1236])).

tff(c_1481,plain,(
    ! [B_247,A_248] : r1_tarski(k1_enumset1(B_247,A_248,A_248),k2_tarski(A_248,B_247)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1462])).

tff(c_431,plain,(
    ! [A_124,B_125,C_126] :
      ( r1_tarski(k2_tarski(A_124,B_125),C_126)
      | ~ r2_hidden(B_125,C_126)
      | ~ r2_hidden(A_124,C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_443,plain,(
    ! [A_124,B_125,C_126] :
      ( k2_tarski(A_124,B_125) = C_126
      | ~ r1_tarski(C_126,k2_tarski(A_124,B_125))
      | ~ r2_hidden(B_125,C_126)
      | ~ r2_hidden(A_124,C_126) ) ),
    inference(resolution,[status(thm)],[c_431,c_4])).

tff(c_1484,plain,(
    ! [B_247,A_248] :
      ( k1_enumset1(B_247,A_248,A_248) = k2_tarski(A_248,B_247)
      | ~ r2_hidden(B_247,k1_enumset1(B_247,A_248,A_248))
      | ~ r2_hidden(A_248,k1_enumset1(B_247,A_248,A_248)) ) ),
    inference(resolution,[status(thm)],[c_1481,c_443])).

tff(c_1507,plain,(
    ! [B_249,A_250] : k1_enumset1(B_249,A_250,A_250) = k2_tarski(A_250,B_249) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1326,c_1327,c_1484])).

tff(c_1258,plain,(
    ! [A_34,B_35,C_36] : r1_tarski(k2_tarski(A_34,B_35),k1_enumset1(A_34,B_35,C_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1250])).

tff(c_1559,plain,(
    ! [B_251,A_252] : r1_tarski(k2_tarski(B_251,A_252),k2_tarski(A_252,B_251)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1507,c_1258])).

tff(c_1562,plain,(
    ! [B_251,A_252] :
      ( k2_tarski(B_251,A_252) = k2_tarski(A_252,B_251)
      | ~ r2_hidden(B_251,k2_tarski(B_251,A_252))
      | ~ r2_hidden(A_252,k2_tarski(B_251,A_252)) ) ),
    inference(resolution,[status(thm)],[c_1559,c_443])).

tff(c_1589,plain,(
    ! [B_253,A_254] : k2_tarski(B_253,A_254) = k2_tarski(A_254,B_253) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_188,c_1562])).

tff(c_38,plain,(
    ! [A_60,B_61] : k3_tarski(k2_tarski(A_60,B_61)) = k2_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1763,plain,(
    ! [A_257,B_258] : k3_tarski(k2_tarski(A_257,B_258)) = k2_xboole_0(B_258,A_257) ),
    inference(superposition,[status(thm),theory(equality)],[c_1589,c_38])).

tff(c_1769,plain,(
    ! [B_258,A_257] : k2_xboole_0(B_258,A_257) = k2_xboole_0(A_257,B_258) ),
    inference(superposition,[status(thm),theory(equality)],[c_1763,c_38])).

tff(c_48,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_231,plain,(
    ! [B_94,A_95] :
      ( B_94 = A_95
      | ~ r1_tarski(B_94,A_95)
      | ~ r1_tarski(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_241,plain,
    ( k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_231])).

tff(c_311,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_241])).

tff(c_1792,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0('#skF_2',k1_tarski('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1769,c_311])).

tff(c_1798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1792])).

tff(c_1799,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_94,plain,(
    ! [A_71,B_72] : k1_enumset1(A_71,A_71,B_72) = k2_tarski(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ! [A_54] : k1_enumset1(A_54,A_54,A_54) = k1_tarski(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_101,plain,(
    ! [B_72] : k2_tarski(B_72,B_72) = k1_tarski(B_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_34])).

tff(c_218,plain,(
    ! [B_91,A_92,B_93] : r2_hidden(B_91,k2_xboole_0(k2_tarski(A_92,B_91),B_93)) ),
    inference(resolution,[status(thm)],[c_14,c_193])).

tff(c_229,plain,(
    ! [B_72,B_93] : r2_hidden(B_72,k2_xboole_0(k1_tarski(B_72),B_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_218])).

tff(c_1806,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1799,c_229])).

tff(c_1813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1806])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:49:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.61  
% 3.46/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.62  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 3.46/1.62  
% 3.46/1.62  %Foreground sorts:
% 3.46/1.62  
% 3.46/1.62  
% 3.46/1.62  %Background operators:
% 3.46/1.62  
% 3.46/1.62  
% 3.46/1.62  %Foreground operators:
% 3.46/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.46/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.46/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.46/1.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.46/1.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.46/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.46/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.46/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.46/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.46/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.46/1.62  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.46/1.62  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.46/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.62  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.46/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.46/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.46/1.62  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.46/1.62  
% 3.82/1.63  tff(f_74, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 3.82/1.63  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.82/1.63  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.82/1.63  tff(f_69, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.82/1.63  tff(f_49, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.82/1.63  tff(f_51, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.82/1.63  tff(f_53, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.82/1.63  tff(f_61, axiom, (![A, B, C, D, E]: (k5_enumset1(A, A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_enumset1)).
% 3.82/1.63  tff(f_55, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.82/1.63  tff(f_45, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_enumset1)).
% 3.82/1.63  tff(f_43, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, B, C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_enumset1)).
% 3.82/1.63  tff(f_63, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.82/1.63  tff(f_59, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 3.82/1.63  tff(c_46, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.82/1.63  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.82/1.63  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.82/1.63  tff(c_193, plain, (![B_85, C_86, A_87]: (r2_hidden(B_85, C_86) | ~r1_tarski(k2_tarski(A_87, B_85), C_86))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.82/1.63  tff(c_211, plain, (![B_85, A_87]: (r2_hidden(B_85, k2_tarski(A_87, B_85)))), inference(resolution, [status(thm)], [c_8, c_193])).
% 3.82/1.63  tff(c_170, plain, (![A_80, C_81, B_82]: (r2_hidden(A_80, C_81) | ~r1_tarski(k2_tarski(A_80, B_82), C_81))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.82/1.63  tff(c_188, plain, (![A_80, B_82]: (r2_hidden(A_80, k2_tarski(A_80, B_82)))), inference(resolution, [status(thm)], [c_8, c_170])).
% 3.82/1.63  tff(c_24, plain, (![A_32, B_33]: (k1_enumset1(A_32, A_32, B_33)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.82/1.63  tff(c_26, plain, (![A_34, B_35, C_36]: (k2_enumset1(A_34, A_34, B_35, C_36)=k1_enumset1(A_34, B_35, C_36))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.82/1.63  tff(c_28, plain, (![A_37, B_38, C_39, D_40]: (k3_enumset1(A_37, A_37, B_38, C_39, D_40)=k2_enumset1(A_37, B_38, C_39, D_40))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.82/1.63  tff(c_36, plain, (![B_56, E_59, C_57, A_55, D_58]: (k5_enumset1(A_55, A_55, A_55, B_56, C_57, D_58, E_59)=k3_enumset1(A_55, B_56, C_57, D_58, E_59))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.82/1.63  tff(c_674, plain, (![B_150, C_147, D_148, F_149, E_145, A_146]: (k5_enumset1(A_146, A_146, B_150, C_147, D_148, E_145, F_149)=k4_enumset1(A_146, B_150, C_147, D_148, E_145, F_149))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.82/1.63  tff(c_687, plain, (![B_56, E_59, C_57, A_55, D_58]: (k4_enumset1(A_55, A_55, B_56, C_57, D_58, E_59)=k3_enumset1(A_55, B_56, C_57, D_58, E_59))), inference(superposition, [status(thm), theory('equality')], [c_36, c_674])).
% 3.82/1.63  tff(c_790, plain, (![A_163, C_162, D_166, B_164, G_168, E_167, F_165]: (k2_xboole_0(k4_enumset1(A_163, B_164, C_162, D_166, E_167, F_165), k1_tarski(G_168))=k5_enumset1(A_163, B_164, C_162, D_166, E_167, F_165, G_168))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.82/1.63  tff(c_1187, plain, (![A_206, C_204, B_205, E_207, D_203, F_209, G_208]: (r1_tarski(k4_enumset1(A_206, B_205, C_204, D_203, E_207, F_209), k5_enumset1(A_206, B_205, C_204, D_203, E_207, F_209, G_208)))), inference(superposition, [status(thm), theory('equality')], [c_790, c_14])).
% 3.82/1.63  tff(c_1198, plain, (![B_56, E_59, C_57, A_55, D_58]: (r1_tarski(k4_enumset1(A_55, A_55, A_55, B_56, C_57, D_58), k3_enumset1(A_55, B_56, C_57, D_58, E_59)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1187])).
% 3.82/1.63  tff(c_1215, plain, (![C_221, E_222, D_219, A_220, B_218]: (r1_tarski(k2_enumset1(A_220, B_218, C_221, D_219), k3_enumset1(A_220, B_218, C_221, D_219, E_222)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_687, c_1198])).
% 3.82/1.63  tff(c_1220, plain, (![A_37, B_38, C_39, D_40]: (r1_tarski(k2_enumset1(A_37, A_37, B_38, C_39), k2_enumset1(A_37, B_38, C_39, D_40)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1215])).
% 3.82/1.63  tff(c_1236, plain, (![A_223, B_224, C_225, D_226]: (r1_tarski(k1_enumset1(A_223, B_224, C_225), k2_enumset1(A_223, B_224, C_225, D_226)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1220])).
% 3.82/1.63  tff(c_1250, plain, (![A_34, B_35, C_36]: (r1_tarski(k1_enumset1(A_34, A_34, B_35), k1_enumset1(A_34, B_35, C_36)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1236])).
% 3.82/1.63  tff(c_1307, plain, (![A_233, B_234, C_235]: (r1_tarski(k2_tarski(A_233, B_234), k1_enumset1(A_233, B_234, C_235)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1250])).
% 3.82/1.63  tff(c_42, plain, (![B_63, C_64, A_62]: (r2_hidden(B_63, C_64) | ~r1_tarski(k2_tarski(A_62, B_63), C_64))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.82/1.63  tff(c_1326, plain, (![B_234, A_233, C_235]: (r2_hidden(B_234, k1_enumset1(A_233, B_234, C_235)))), inference(resolution, [status(thm)], [c_1307, c_42])).
% 3.82/1.63  tff(c_44, plain, (![A_62, C_64, B_63]: (r2_hidden(A_62, C_64) | ~r1_tarski(k2_tarski(A_62, B_63), C_64))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.82/1.63  tff(c_1327, plain, (![A_233, B_234, C_235]: (r2_hidden(A_233, k1_enumset1(A_233, B_234, C_235)))), inference(resolution, [status(thm)], [c_1307, c_44])).
% 3.82/1.63  tff(c_384, plain, (![D_120, B_121, C_122, A_123]: (k2_enumset1(D_120, B_121, C_122, A_123)=k2_enumset1(A_123, B_121, C_122, D_120))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.82/1.63  tff(c_400, plain, (![D_120, B_121, C_122]: (k2_enumset1(D_120, B_121, C_122, B_121)=k1_enumset1(B_121, C_122, D_120))), inference(superposition, [status(thm), theory('equality')], [c_384, c_26])).
% 3.82/1.63  tff(c_1462, plain, (![D_244, B_245, C_246]: (r1_tarski(k1_enumset1(D_244, B_245, C_246), k1_enumset1(B_245, C_246, D_244)))), inference(superposition, [status(thm), theory('equality')], [c_400, c_1236])).
% 3.82/1.63  tff(c_1481, plain, (![B_247, A_248]: (r1_tarski(k1_enumset1(B_247, A_248, A_248), k2_tarski(A_248, B_247)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1462])).
% 3.82/1.63  tff(c_431, plain, (![A_124, B_125, C_126]: (r1_tarski(k2_tarski(A_124, B_125), C_126) | ~r2_hidden(B_125, C_126) | ~r2_hidden(A_124, C_126))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.82/1.63  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.82/1.63  tff(c_443, plain, (![A_124, B_125, C_126]: (k2_tarski(A_124, B_125)=C_126 | ~r1_tarski(C_126, k2_tarski(A_124, B_125)) | ~r2_hidden(B_125, C_126) | ~r2_hidden(A_124, C_126))), inference(resolution, [status(thm)], [c_431, c_4])).
% 3.82/1.63  tff(c_1484, plain, (![B_247, A_248]: (k1_enumset1(B_247, A_248, A_248)=k2_tarski(A_248, B_247) | ~r2_hidden(B_247, k1_enumset1(B_247, A_248, A_248)) | ~r2_hidden(A_248, k1_enumset1(B_247, A_248, A_248)))), inference(resolution, [status(thm)], [c_1481, c_443])).
% 3.82/1.63  tff(c_1507, plain, (![B_249, A_250]: (k1_enumset1(B_249, A_250, A_250)=k2_tarski(A_250, B_249))), inference(demodulation, [status(thm), theory('equality')], [c_1326, c_1327, c_1484])).
% 3.82/1.63  tff(c_1258, plain, (![A_34, B_35, C_36]: (r1_tarski(k2_tarski(A_34, B_35), k1_enumset1(A_34, B_35, C_36)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1250])).
% 3.82/1.63  tff(c_1559, plain, (![B_251, A_252]: (r1_tarski(k2_tarski(B_251, A_252), k2_tarski(A_252, B_251)))), inference(superposition, [status(thm), theory('equality')], [c_1507, c_1258])).
% 3.82/1.63  tff(c_1562, plain, (![B_251, A_252]: (k2_tarski(B_251, A_252)=k2_tarski(A_252, B_251) | ~r2_hidden(B_251, k2_tarski(B_251, A_252)) | ~r2_hidden(A_252, k2_tarski(B_251, A_252)))), inference(resolution, [status(thm)], [c_1559, c_443])).
% 3.82/1.63  tff(c_1589, plain, (![B_253, A_254]: (k2_tarski(B_253, A_254)=k2_tarski(A_254, B_253))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_188, c_1562])).
% 3.82/1.63  tff(c_38, plain, (![A_60, B_61]: (k3_tarski(k2_tarski(A_60, B_61))=k2_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.82/1.63  tff(c_1763, plain, (![A_257, B_258]: (k3_tarski(k2_tarski(A_257, B_258))=k2_xboole_0(B_258, A_257))), inference(superposition, [status(thm), theory('equality')], [c_1589, c_38])).
% 3.82/1.63  tff(c_1769, plain, (![B_258, A_257]: (k2_xboole_0(B_258, A_257)=k2_xboole_0(A_257, B_258))), inference(superposition, [status(thm), theory('equality')], [c_1763, c_38])).
% 3.82/1.63  tff(c_48, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.82/1.63  tff(c_231, plain, (![B_94, A_95]: (B_94=A_95 | ~r1_tarski(B_94, A_95) | ~r1_tarski(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.82/1.63  tff(c_241, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_231])).
% 3.82/1.63  tff(c_311, plain, (~r1_tarski('#skF_2', k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_241])).
% 3.82/1.63  tff(c_1792, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_2', k1_tarski('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1769, c_311])).
% 3.82/1.63  tff(c_1798, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_1792])).
% 3.82/1.63  tff(c_1799, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_241])).
% 3.82/1.63  tff(c_94, plain, (![A_71, B_72]: (k1_enumset1(A_71, A_71, B_72)=k2_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.82/1.63  tff(c_34, plain, (![A_54]: (k1_enumset1(A_54, A_54, A_54)=k1_tarski(A_54))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.82/1.63  tff(c_101, plain, (![B_72]: (k2_tarski(B_72, B_72)=k1_tarski(B_72))), inference(superposition, [status(thm), theory('equality')], [c_94, c_34])).
% 3.82/1.63  tff(c_218, plain, (![B_91, A_92, B_93]: (r2_hidden(B_91, k2_xboole_0(k2_tarski(A_92, B_91), B_93)))), inference(resolution, [status(thm)], [c_14, c_193])).
% 3.82/1.63  tff(c_229, plain, (![B_72, B_93]: (r2_hidden(B_72, k2_xboole_0(k1_tarski(B_72), B_93)))), inference(superposition, [status(thm), theory('equality')], [c_101, c_218])).
% 3.82/1.63  tff(c_1806, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1799, c_229])).
% 3.82/1.63  tff(c_1813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_1806])).
% 3.82/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.63  
% 3.82/1.63  Inference rules
% 3.82/1.63  ----------------------
% 3.82/1.63  #Ref     : 0
% 3.82/1.63  #Sup     : 441
% 3.82/1.63  #Fact    : 0
% 3.82/1.63  #Define  : 0
% 3.82/1.63  #Split   : 1
% 3.82/1.63  #Chain   : 0
% 3.82/1.63  #Close   : 0
% 3.82/1.63  
% 3.82/1.64  Ordering : KBO
% 3.82/1.64  
% 3.82/1.64  Simplification rules
% 3.82/1.64  ----------------------
% 3.82/1.64  #Subsume      : 13
% 3.82/1.64  #Demod        : 214
% 3.82/1.64  #Tautology    : 234
% 3.82/1.64  #SimpNegUnit  : 1
% 3.82/1.64  #BackRed      : 7
% 3.82/1.64  
% 3.82/1.64  #Partial instantiations: 0
% 3.82/1.64  #Strategies tried      : 1
% 3.82/1.64  
% 3.82/1.64  Timing (in seconds)
% 3.82/1.64  ----------------------
% 3.82/1.64  Preprocessing        : 0.32
% 3.82/1.64  Parsing              : 0.17
% 3.82/1.64  CNF conversion       : 0.02
% 3.82/1.64  Main loop            : 0.56
% 3.82/1.64  Inferencing          : 0.19
% 3.82/1.64  Reduction            : 0.22
% 3.82/1.64  Demodulation         : 0.18
% 3.82/1.64  BG Simplification    : 0.03
% 3.82/1.64  Subsumption          : 0.08
% 3.82/1.64  Abstraction          : 0.03
% 3.82/1.64  MUC search           : 0.00
% 3.82/1.64  Cooper               : 0.00
% 3.82/1.64  Total                : 0.92
% 3.82/1.64  Index Insertion      : 0.00
% 3.82/1.64  Index Deletion       : 0.00
% 3.82/1.64  Index Matching       : 0.00
% 3.82/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
