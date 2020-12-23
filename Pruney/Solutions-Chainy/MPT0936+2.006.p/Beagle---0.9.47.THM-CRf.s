%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:27 EST 2020

% Result     : Theorem 5.90s
% Output     : CNFRefutation 6.16s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 269 expanded)
%              Number of leaves         :   37 ( 104 expanded)
%              Depth                    :   12
%              Number of atoms          :   91 ( 374 expanded)
%              Number of equality atoms :   66 ( 310 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_96,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] : k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A,B,C)))) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_mcart_1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_82,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

tff(c_18,plain,(
    ! [A_29] : k2_zfmisc_1(A_29,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_111,plain,(
    ! [A_55,B_56] : ~ r2_hidden(A_55,k2_zfmisc_1(A_55,B_56)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_114,plain,(
    ! [A_29] : ~ r2_hidden(A_29,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_111])).

tff(c_20,plain,(
    ! [B_30] : k2_zfmisc_1(k1_xboole_0,B_30) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_86,plain,(
    ! [A_50,B_51,C_52] : k4_tarski(k4_tarski(A_50,B_51),C_52) = k3_mcart_1(A_50,B_51,C_52) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_243,plain,(
    ! [A_145,B_146,C_147] : k2_zfmisc_1(k2_tarski(A_145,B_146),k1_tarski(C_147)) = k2_tarski(k4_tarski(A_145,C_147),k4_tarski(B_146,C_147)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_265,plain,(
    ! [B_146,C_147] : k2_zfmisc_1(k2_tarski(B_146,B_146),k1_tarski(C_147)) = k1_tarski(k4_tarski(B_146,C_147)) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_2])).

tff(c_309,plain,(
    ! [B_153,C_154] : k2_zfmisc_1(k1_tarski(B_153),k1_tarski(C_154)) = k1_tarski(k4_tarski(B_153,C_154)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_265])).

tff(c_84,plain,(
    ! [A_48,B_49] :
      ( k1_relat_1(k2_zfmisc_1(A_48,B_49)) = A_48
      | k1_xboole_0 = B_49
      | k1_xboole_0 = A_48 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_318,plain,(
    ! [B_153,C_154] :
      ( k1_relat_1(k1_tarski(k4_tarski(B_153,C_154))) = k1_tarski(B_153)
      | k1_tarski(C_154) = k1_xboole_0
      | k1_tarski(B_153) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_84])).

tff(c_486,plain,(
    ! [B_177,C_178] :
      ( k1_relat_1(k1_tarski(k4_tarski(B_177,C_178))) = k1_tarski(B_177)
      | k1_tarski(C_178) = k1_xboole_0
      | k1_tarski(B_177) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_84])).

tff(c_2850,plain,(
    ! [A_652,B_653,C_654] :
      ( k1_relat_1(k1_tarski(k3_mcart_1(A_652,B_653,C_654))) = k1_tarski(k4_tarski(A_652,B_653))
      | k1_tarski(C_654) = k1_xboole_0
      | k1_tarski(k4_tarski(A_652,B_653)) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_486])).

tff(c_88,plain,(
    k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_3','#skF_4','#skF_5')))) != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2856,plain,
    ( k1_relat_1(k1_tarski(k4_tarski('#skF_3','#skF_4'))) != k1_tarski('#skF_3')
    | k1_tarski('#skF_5') = k1_xboole_0
    | k1_tarski(k4_tarski('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2850,c_88])).

tff(c_2866,plain,(
    k1_relat_1(k1_tarski(k4_tarski('#skF_3','#skF_4'))) != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2856])).

tff(c_2870,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_2866])).

tff(c_2871,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2870])).

tff(c_24,plain,(
    ! [A_33,B_34,C_35] : k2_zfmisc_1(k1_tarski(A_33),k2_tarski(B_34,C_35)) = k2_tarski(k4_tarski(A_33,B_34),k4_tarski(A_33,C_35)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : k3_enumset1(A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] : k4_enumset1(A_11,A_11,B_12,C_13,D_14,E_15) = k3_enumset1(A_11,B_12,C_13,D_14,E_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [C_18,B_17,A_16,D_19,E_20,F_21] : k5_enumset1(A_16,A_16,B_17,C_18,D_19,E_20,F_21) = k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_536,plain,(
    ! [A_185,B_191,F_188,G_189,D_190,C_186,E_187] : k6_enumset1(A_185,A_185,B_191,C_186,D_190,E_187,F_188,G_189) = k5_enumset1(A_185,B_191,C_186,D_190,E_187,F_188,G_189) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [G_42,D_39,A_36,J_47,E_40,H_43,C_38,B_37] : r2_hidden(J_47,k6_enumset1(A_36,B_37,C_38,D_39,E_40,J_47,G_42,H_43)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_569,plain,(
    ! [C_195,A_194,G_196,F_193,B_198,D_197,E_192] : r2_hidden(E_192,k5_enumset1(A_194,B_198,C_195,D_197,E_192,F_193,G_196)) ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_34])).

tff(c_573,plain,(
    ! [F_199,B_200,A_202,E_201,C_204,D_203] : r2_hidden(D_203,k4_enumset1(A_202,B_200,C_204,D_203,E_201,F_199)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_569])).

tff(c_577,plain,(
    ! [A_206,D_208,E_209,C_205,B_207] : r2_hidden(C_205,k3_enumset1(A_206,B_207,C_205,D_208,E_209)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_573])).

tff(c_581,plain,(
    ! [B_210,A_211,C_212,D_213] : r2_hidden(B_210,k2_enumset1(A_211,B_210,C_212,D_213)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_577])).

tff(c_585,plain,(
    ! [A_214,B_215,C_216] : r2_hidden(A_214,k1_enumset1(A_214,B_215,C_216)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_581])).

tff(c_633,plain,(
    ! [A_226,B_227] : r2_hidden(A_226,k2_tarski(A_226,B_227)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_585])).

tff(c_747,plain,(
    ! [A_395,B_396,C_397] : r2_hidden(k4_tarski(A_395,B_396),k2_zfmisc_1(k1_tarski(A_395),k2_tarski(B_396,C_397))) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_633])).

tff(c_750,plain,(
    ! [A_395,A_33,B_34,C_35] : r2_hidden(k4_tarski(A_395,k4_tarski(A_33,B_34)),k2_zfmisc_1(k1_tarski(A_395),k2_zfmisc_1(k1_tarski(A_33),k2_tarski(B_34,C_35)))) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_747])).

tff(c_2917,plain,(
    ! [A_33,B_34,C_35] : r2_hidden(k4_tarski('#skF_3',k4_tarski(A_33,B_34)),k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(k1_tarski(A_33),k2_tarski(B_34,C_35)))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2871,c_750])).

tff(c_3018,plain,(
    ! [A_33,B_34] : r2_hidden(k4_tarski('#skF_3',k4_tarski(A_33,B_34)),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2917])).

tff(c_3020,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_3018])).

tff(c_3021,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2870])).

tff(c_3066,plain,(
    ! [A_33,B_34,C_35] : r2_hidden(k4_tarski('#skF_4',k4_tarski(A_33,B_34)),k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(k1_tarski(A_33),k2_tarski(B_34,C_35)))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3021,c_750])).

tff(c_3167,plain,(
    ! [A_33,B_34] : r2_hidden(k4_tarski('#skF_4',k4_tarski(A_33,B_34)),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_3066])).

tff(c_3169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_3167])).

tff(c_3170,plain,
    ( k1_tarski(k4_tarski('#skF_3','#skF_4')) = k1_xboole_0
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2856])).

tff(c_3184,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3170])).

tff(c_3228,plain,(
    ! [A_33,B_34,C_35] : r2_hidden(k4_tarski('#skF_5',k4_tarski(A_33,B_34)),k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(k1_tarski(A_33),k2_tarski(B_34,C_35)))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3184,c_750])).

tff(c_3329,plain,(
    ! [A_33,B_34] : r2_hidden(k4_tarski('#skF_5',k4_tarski(A_33,B_34)),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_3228])).

tff(c_3331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_3329])).

tff(c_3332,plain,(
    k1_tarski(k4_tarski('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3170])).

tff(c_3375,plain,(
    ! [A_33,B_34,C_35] : r2_hidden(k4_tarski(k4_tarski('#skF_3','#skF_4'),k4_tarski(A_33,B_34)),k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(k1_tarski(A_33),k2_tarski(B_34,C_35)))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3332,c_750])).

tff(c_3493,plain,(
    ! [A_33,B_34] : r2_hidden(k3_mcart_1('#skF_3','#skF_4',k4_tarski(A_33,B_34)),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_86,c_3375])).

tff(c_3495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_3493])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:21:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.90/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.90/2.10  
% 5.90/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.90/2.10  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.90/2.10  
% 5.90/2.10  %Foreground sorts:
% 5.90/2.10  
% 5.90/2.10  
% 5.90/2.10  %Background operators:
% 5.90/2.10  
% 5.90/2.10  
% 5.90/2.10  %Foreground operators:
% 5.90/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.90/2.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.90/2.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.90/2.10  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.90/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.90/2.10  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 5.90/2.10  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.90/2.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.90/2.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.90/2.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.90/2.10  tff('#skF_5', type, '#skF_5': $i).
% 5.90/2.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.90/2.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.90/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.90/2.10  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.90/2.10  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.90/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.90/2.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.90/2.10  tff('#skF_4', type, '#skF_4': $i).
% 5.90/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.90/2.10  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.90/2.10  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.90/2.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.90/2.10  
% 6.16/2.13  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.16/2.13  tff(f_48, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 6.16/2.13  tff(f_96, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 6.16/2.13  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.16/2.13  tff(f_52, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 6.16/2.13  tff(f_94, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 6.16/2.13  tff(f_99, negated_conjecture, ~(![A, B, C]: (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(A, B, C)))) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_mcart_1)).
% 6.16/2.13  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.16/2.13  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 6.16/2.13  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 6.16/2.13  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 6.16/2.13  tff(f_37, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 6.16/2.13  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 6.16/2.13  tff(f_82, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 6.16/2.13  tff(c_18, plain, (![A_29]: (k2_zfmisc_1(A_29, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.16/2.13  tff(c_111, plain, (![A_55, B_56]: (~r2_hidden(A_55, k2_zfmisc_1(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.16/2.13  tff(c_114, plain, (![A_29]: (~r2_hidden(A_29, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_111])).
% 6.16/2.13  tff(c_20, plain, (![B_30]: (k2_zfmisc_1(k1_xboole_0, B_30)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.16/2.13  tff(c_86, plain, (![A_50, B_51, C_52]: (k4_tarski(k4_tarski(A_50, B_51), C_52)=k3_mcart_1(A_50, B_51, C_52))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.16/2.13  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.16/2.13  tff(c_243, plain, (![A_145, B_146, C_147]: (k2_zfmisc_1(k2_tarski(A_145, B_146), k1_tarski(C_147))=k2_tarski(k4_tarski(A_145, C_147), k4_tarski(B_146, C_147)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.16/2.13  tff(c_265, plain, (![B_146, C_147]: (k2_zfmisc_1(k2_tarski(B_146, B_146), k1_tarski(C_147))=k1_tarski(k4_tarski(B_146, C_147)))), inference(superposition, [status(thm), theory('equality')], [c_243, c_2])).
% 6.16/2.13  tff(c_309, plain, (![B_153, C_154]: (k2_zfmisc_1(k1_tarski(B_153), k1_tarski(C_154))=k1_tarski(k4_tarski(B_153, C_154)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_265])).
% 6.16/2.13  tff(c_84, plain, (![A_48, B_49]: (k1_relat_1(k2_zfmisc_1(A_48, B_49))=A_48 | k1_xboole_0=B_49 | k1_xboole_0=A_48)), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.16/2.13  tff(c_318, plain, (![B_153, C_154]: (k1_relat_1(k1_tarski(k4_tarski(B_153, C_154)))=k1_tarski(B_153) | k1_tarski(C_154)=k1_xboole_0 | k1_tarski(B_153)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_309, c_84])).
% 6.16/2.13  tff(c_486, plain, (![B_177, C_178]: (k1_relat_1(k1_tarski(k4_tarski(B_177, C_178)))=k1_tarski(B_177) | k1_tarski(C_178)=k1_xboole_0 | k1_tarski(B_177)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_309, c_84])).
% 6.16/2.13  tff(c_2850, plain, (![A_652, B_653, C_654]: (k1_relat_1(k1_tarski(k3_mcart_1(A_652, B_653, C_654)))=k1_tarski(k4_tarski(A_652, B_653)) | k1_tarski(C_654)=k1_xboole_0 | k1_tarski(k4_tarski(A_652, B_653))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_86, c_486])).
% 6.16/2.13  tff(c_88, plain, (k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1('#skF_3', '#skF_4', '#skF_5'))))!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.16/2.13  tff(c_2856, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_3', '#skF_4')))!=k1_tarski('#skF_3') | k1_tarski('#skF_5')=k1_xboole_0 | k1_tarski(k4_tarski('#skF_3', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2850, c_88])).
% 6.16/2.13  tff(c_2866, plain, (k1_relat_1(k1_tarski(k4_tarski('#skF_3', '#skF_4')))!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_2856])).
% 6.16/2.13  tff(c_2870, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_tarski('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_318, c_2866])).
% 6.16/2.13  tff(c_2871, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2870])).
% 6.16/2.13  tff(c_24, plain, (![A_33, B_34, C_35]: (k2_zfmisc_1(k1_tarski(A_33), k2_tarski(B_34, C_35))=k2_tarski(k4_tarski(A_33, B_34), k4_tarski(A_33, C_35)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.16/2.13  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.16/2.13  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.16/2.13  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.16/2.13  tff(c_10, plain, (![D_14, E_15, B_12, A_11, C_13]: (k4_enumset1(A_11, A_11, B_12, C_13, D_14, E_15)=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.16/2.13  tff(c_12, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k5_enumset1(A_16, A_16, B_17, C_18, D_19, E_20, F_21)=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.16/2.13  tff(c_536, plain, (![A_185, B_191, F_188, G_189, D_190, C_186, E_187]: (k6_enumset1(A_185, A_185, B_191, C_186, D_190, E_187, F_188, G_189)=k5_enumset1(A_185, B_191, C_186, D_190, E_187, F_188, G_189))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.16/2.13  tff(c_34, plain, (![G_42, D_39, A_36, J_47, E_40, H_43, C_38, B_37]: (r2_hidden(J_47, k6_enumset1(A_36, B_37, C_38, D_39, E_40, J_47, G_42, H_43)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.16/2.13  tff(c_569, plain, (![C_195, A_194, G_196, F_193, B_198, D_197, E_192]: (r2_hidden(E_192, k5_enumset1(A_194, B_198, C_195, D_197, E_192, F_193, G_196)))), inference(superposition, [status(thm), theory('equality')], [c_536, c_34])).
% 6.16/2.13  tff(c_573, plain, (![F_199, B_200, A_202, E_201, C_204, D_203]: (r2_hidden(D_203, k4_enumset1(A_202, B_200, C_204, D_203, E_201, F_199)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_569])).
% 6.16/2.13  tff(c_577, plain, (![A_206, D_208, E_209, C_205, B_207]: (r2_hidden(C_205, k3_enumset1(A_206, B_207, C_205, D_208, E_209)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_573])).
% 6.16/2.13  tff(c_581, plain, (![B_210, A_211, C_212, D_213]: (r2_hidden(B_210, k2_enumset1(A_211, B_210, C_212, D_213)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_577])).
% 6.16/2.13  tff(c_585, plain, (![A_214, B_215, C_216]: (r2_hidden(A_214, k1_enumset1(A_214, B_215, C_216)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_581])).
% 6.16/2.13  tff(c_633, plain, (![A_226, B_227]: (r2_hidden(A_226, k2_tarski(A_226, B_227)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_585])).
% 6.16/2.13  tff(c_747, plain, (![A_395, B_396, C_397]: (r2_hidden(k4_tarski(A_395, B_396), k2_zfmisc_1(k1_tarski(A_395), k2_tarski(B_396, C_397))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_633])).
% 6.16/2.13  tff(c_750, plain, (![A_395, A_33, B_34, C_35]: (r2_hidden(k4_tarski(A_395, k4_tarski(A_33, B_34)), k2_zfmisc_1(k1_tarski(A_395), k2_zfmisc_1(k1_tarski(A_33), k2_tarski(B_34, C_35)))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_747])).
% 6.16/2.13  tff(c_2917, plain, (![A_33, B_34, C_35]: (r2_hidden(k4_tarski('#skF_3', k4_tarski(A_33, B_34)), k2_zfmisc_1(k1_xboole_0, k2_zfmisc_1(k1_tarski(A_33), k2_tarski(B_34, C_35)))))), inference(superposition, [status(thm), theory('equality')], [c_2871, c_750])).
% 6.16/2.13  tff(c_3018, plain, (![A_33, B_34]: (r2_hidden(k4_tarski('#skF_3', k4_tarski(A_33, B_34)), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2917])).
% 6.16/2.13  tff(c_3020, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_3018])).
% 6.16/2.13  tff(c_3021, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2870])).
% 6.16/2.13  tff(c_3066, plain, (![A_33, B_34, C_35]: (r2_hidden(k4_tarski('#skF_4', k4_tarski(A_33, B_34)), k2_zfmisc_1(k1_xboole_0, k2_zfmisc_1(k1_tarski(A_33), k2_tarski(B_34, C_35)))))), inference(superposition, [status(thm), theory('equality')], [c_3021, c_750])).
% 6.16/2.13  tff(c_3167, plain, (![A_33, B_34]: (r2_hidden(k4_tarski('#skF_4', k4_tarski(A_33, B_34)), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_3066])).
% 6.16/2.13  tff(c_3169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_3167])).
% 6.16/2.13  tff(c_3170, plain, (k1_tarski(k4_tarski('#skF_3', '#skF_4'))=k1_xboole_0 | k1_tarski('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2856])).
% 6.16/2.13  tff(c_3184, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3170])).
% 6.16/2.13  tff(c_3228, plain, (![A_33, B_34, C_35]: (r2_hidden(k4_tarski('#skF_5', k4_tarski(A_33, B_34)), k2_zfmisc_1(k1_xboole_0, k2_zfmisc_1(k1_tarski(A_33), k2_tarski(B_34, C_35)))))), inference(superposition, [status(thm), theory('equality')], [c_3184, c_750])).
% 6.16/2.13  tff(c_3329, plain, (![A_33, B_34]: (r2_hidden(k4_tarski('#skF_5', k4_tarski(A_33, B_34)), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_3228])).
% 6.16/2.13  tff(c_3331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_3329])).
% 6.16/2.13  tff(c_3332, plain, (k1_tarski(k4_tarski('#skF_3', '#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_3170])).
% 6.16/2.13  tff(c_3375, plain, (![A_33, B_34, C_35]: (r2_hidden(k4_tarski(k4_tarski('#skF_3', '#skF_4'), k4_tarski(A_33, B_34)), k2_zfmisc_1(k1_xboole_0, k2_zfmisc_1(k1_tarski(A_33), k2_tarski(B_34, C_35)))))), inference(superposition, [status(thm), theory('equality')], [c_3332, c_750])).
% 6.16/2.13  tff(c_3493, plain, (![A_33, B_34]: (r2_hidden(k3_mcart_1('#skF_3', '#skF_4', k4_tarski(A_33, B_34)), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_86, c_3375])).
% 6.16/2.13  tff(c_3495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_3493])).
% 6.16/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.16/2.13  
% 6.16/2.13  Inference rules
% 6.16/2.13  ----------------------
% 6.16/2.13  #Ref     : 0
% 6.16/2.13  #Sup     : 905
% 6.16/2.13  #Fact    : 0
% 6.16/2.13  #Define  : 0
% 6.16/2.13  #Split   : 3
% 6.16/2.13  #Chain   : 0
% 6.16/2.13  #Close   : 0
% 6.16/2.13  
% 6.16/2.13  Ordering : KBO
% 6.16/2.13  
% 6.16/2.13  Simplification rules
% 6.16/2.13  ----------------------
% 6.16/2.13  #Subsume      : 150
% 6.16/2.13  #Demod        : 658
% 6.16/2.13  #Tautology    : 241
% 6.16/2.13  #SimpNegUnit  : 4
% 6.16/2.13  #BackRed      : 3
% 6.16/2.13  
% 6.16/2.13  #Partial instantiations: 0
% 6.16/2.13  #Strategies tried      : 1
% 6.16/2.13  
% 6.16/2.13  Timing (in seconds)
% 6.16/2.13  ----------------------
% 6.16/2.13  Preprocessing        : 0.34
% 6.16/2.13  Parsing              : 0.16
% 6.16/2.13  CNF conversion       : 0.03
% 6.16/2.13  Main loop            : 1.03
% 6.16/2.13  Inferencing          : 0.31
% 6.16/2.13  Reduction            : 0.44
% 6.16/2.13  Demodulation         : 0.36
% 6.16/2.13  BG Simplification    : 0.04
% 6.16/2.13  Subsumption          : 0.19
% 6.16/2.13  Abstraction          : 0.06
% 6.16/2.13  MUC search           : 0.00
% 6.16/2.13  Cooper               : 0.00
% 6.16/2.13  Total                : 1.41
% 6.16/2.13  Index Insertion      : 0.00
% 6.16/2.13  Index Deletion       : 0.00
% 6.16/2.13  Index Matching       : 0.00
% 6.16/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
