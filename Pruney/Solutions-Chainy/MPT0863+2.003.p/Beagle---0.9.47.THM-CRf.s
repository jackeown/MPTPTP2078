%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:07 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 282 expanded)
%              Number of leaves         :   31 ( 104 expanded)
%              Depth                    :    7
%              Number of atoms          :  171 ( 592 expanded)
%              Number of equality atoms :   48 ( 203 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k2_tarski(D,E)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & ( k2_mcart_1(A) = D
            | k2_mcart_1(A) = E ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_mcart_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(c_60,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | k2_mcart_1('#skF_3') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_96,plain,(
    k2_mcart_1('#skF_3') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_97,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_26,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_107,plain,(
    ! [A_41,C_42,B_43] :
      ( r2_hidden(A_41,C_42)
      | ~ r1_tarski(k2_tarski(A_41,B_43),C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_116,plain,(
    ! [A_44,B_45] : r2_hidden(A_44,k2_tarski(A_44,B_45)) ),
    inference(resolution,[status(thm)],[c_24,c_107])).

tff(c_119,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_116])).

tff(c_58,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),k2_tarski('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_161,plain,(
    ! [A_68,C_69,B_70] :
      ( r2_hidden(k2_mcart_1(A_68),C_69)
      | ~ r2_hidden(A_68,k2_zfmisc_1(B_70,C_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_164,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k2_tarski('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_58,c_161])).

tff(c_222,plain,(
    ! [C_92,A_93,B_94] :
      ( k4_xboole_0(C_92,k2_tarski(A_93,B_94)) = C_92
      | r2_hidden(B_94,C_92)
      | r2_hidden(A_93,C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_395,plain,(
    ! [D_111,A_112,B_113,C_114] :
      ( ~ r2_hidden(D_111,k2_tarski(A_112,B_113))
      | ~ r2_hidden(D_111,C_114)
      | r2_hidden(B_113,C_114)
      | r2_hidden(A_112,C_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_4])).

tff(c_444,plain,(
    ! [C_116] :
      ( ~ r2_hidden(k2_mcart_1('#skF_3'),C_116)
      | r2_hidden('#skF_7',C_116)
      | r2_hidden('#skF_6',C_116) ) ),
    inference(resolution,[status(thm)],[c_164,c_395])).

tff(c_468,plain,
    ( r2_hidden('#skF_7',k1_tarski(k2_mcart_1('#skF_3')))
    | r2_hidden('#skF_6',k1_tarski(k2_mcart_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_119,c_444])).

tff(c_533,plain,(
    r2_hidden('#skF_6',k1_tarski(k2_mcart_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_468])).

tff(c_54,plain,(
    ! [A_31,B_32] : k1_mcart_1(k4_tarski(A_31,B_32)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_261,plain,(
    ! [A_97,B_98,C_99,D_100] :
      ( r2_hidden(k4_tarski(A_97,B_98),k2_zfmisc_1(C_99,D_100))
      | ~ r2_hidden(B_98,D_100)
      | ~ r2_hidden(A_97,C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_52,plain,(
    ! [A_28,B_29,C_30] :
      ( k1_mcart_1(A_28) = B_29
      | ~ r2_hidden(A_28,k2_zfmisc_1(k1_tarski(B_29),C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_275,plain,(
    ! [A_97,B_98,B_29,D_100] :
      ( k1_mcart_1(k4_tarski(A_97,B_98)) = B_29
      | ~ r2_hidden(B_98,D_100)
      | ~ r2_hidden(A_97,k1_tarski(B_29)) ) ),
    inference(resolution,[status(thm)],[c_261,c_52])).

tff(c_283,plain,(
    ! [B_29,A_97,B_98,D_100] :
      ( B_29 = A_97
      | ~ r2_hidden(B_98,D_100)
      | ~ r2_hidden(A_97,k1_tarski(B_29)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_275])).

tff(c_284,plain,(
    ! [B_98,D_100] : ~ r2_hidden(B_98,D_100) ),
    inference(splitLeft,[status(thm)],[c_283])).

tff(c_165,plain,(
    ! [A_71,B_72,C_73] :
      ( r2_hidden(k1_mcart_1(A_71),B_72)
      | ~ r2_hidden(A_71,k2_zfmisc_1(B_72,C_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_168,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_58,c_165])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_168])).

tff(c_304,plain,(
    ! [B_29,A_97] :
      ( B_29 = A_97
      | ~ r2_hidden(A_97,k1_tarski(B_29)) ) ),
    inference(splitRight,[status(thm)],[c_283])).

tff(c_549,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_533,c_304])).

tff(c_555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_549])).

tff(c_556,plain,(
    r2_hidden('#skF_7',k1_tarski(k2_mcart_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_468])).

tff(c_573,plain,(
    k2_mcart_1('#skF_3') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_556,c_304])).

tff(c_579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_573])).

tff(c_581,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_64,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_588,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_64])).

tff(c_580,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_608,plain,(
    ! [B_132,C_133,A_134] :
      ( r2_hidden(B_132,C_133)
      | ~ r1_tarski(k2_tarski(A_134,B_132),C_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_626,plain,(
    ! [B_138,A_139] : r2_hidden(B_138,k2_tarski(A_139,B_138)) ),
    inference(resolution,[status(thm)],[c_24,c_608])).

tff(c_629,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_626])).

tff(c_648,plain,(
    ! [A_148,B_149,C_150] :
      ( r2_hidden(k1_mcart_1(A_148),B_149)
      | ~ r2_hidden(A_148,k2_zfmisc_1(B_149,C_150)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_651,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_58,c_648])).

tff(c_715,plain,(
    ! [C_175,A_176,B_177] :
      ( k4_xboole_0(C_175,k2_tarski(A_176,B_177)) = C_175
      | r2_hidden(B_177,C_175)
      | r2_hidden(A_176,C_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_820,plain,(
    ! [D_194,A_195,B_196,C_197] :
      ( ~ r2_hidden(D_194,k2_tarski(A_195,B_196))
      | ~ r2_hidden(D_194,C_197)
      | r2_hidden(B_196,C_197)
      | r2_hidden(A_195,C_197) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_715,c_4])).

tff(c_832,plain,(
    ! [C_198] :
      ( ~ r2_hidden(k1_mcart_1('#skF_3'),C_198)
      | r2_hidden('#skF_5',C_198)
      | r2_hidden('#skF_4',C_198) ) ),
    inference(resolution,[status(thm)],[c_651,c_820])).

tff(c_856,plain,
    ( r2_hidden('#skF_5',k1_tarski(k1_mcart_1('#skF_3')))
    | r2_hidden('#skF_4',k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_629,c_832])).

tff(c_858,plain,(
    r2_hidden('#skF_4',k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_856])).

tff(c_761,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( r2_hidden(k4_tarski(A_182,B_183),k2_zfmisc_1(C_184,D_185))
      | ~ r2_hidden(B_183,D_185)
      | ~ r2_hidden(A_182,C_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_771,plain,(
    ! [A_182,B_183,B_29,D_185] :
      ( k1_mcart_1(k4_tarski(A_182,B_183)) = B_29
      | ~ r2_hidden(B_183,D_185)
      | ~ r2_hidden(A_182,k1_tarski(B_29)) ) ),
    inference(resolution,[status(thm)],[c_761,c_52])).

tff(c_779,plain,(
    ! [B_29,A_182,B_183,D_185] :
      ( B_29 = A_182
      | ~ r2_hidden(B_183,D_185)
      | ~ r2_hidden(A_182,k1_tarski(B_29)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_771])).

tff(c_784,plain,(
    ! [B_183,D_185] : ~ r2_hidden(B_183,D_185) ),
    inference(splitLeft,[status(thm)],[c_779])).

tff(c_802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_784,c_651])).

tff(c_803,plain,(
    ! [B_29,A_182] :
      ( B_29 = A_182
      | ~ r2_hidden(A_182,k1_tarski(B_29)) ) ),
    inference(splitRight,[status(thm)],[c_779])).

tff(c_863,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_858,c_803])).

tff(c_870,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_580,c_863])).

tff(c_871,plain,(
    r2_hidden('#skF_5',k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_856])).

tff(c_963,plain,(
    k1_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_871,c_803])).

tff(c_970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_588,c_963])).

tff(c_971,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_972,plain,(
    k2_mcart_1('#skF_3') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_62,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | k2_mcart_1('#skF_3') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_978,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_62])).

tff(c_990,plain,(
    ! [A_204,C_205,B_206] :
      ( r2_hidden(A_204,C_205)
      | ~ r1_tarski(k2_tarski(A_204,B_206),C_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_999,plain,(
    ! [A_207,B_208] : r2_hidden(A_207,k2_tarski(A_207,B_208)) ),
    inference(resolution,[status(thm)],[c_24,c_990])).

tff(c_1002,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_999])).

tff(c_1034,plain,(
    ! [A_225,B_226,C_227] :
      ( r2_hidden(k1_mcart_1(A_225),B_226)
      | ~ r2_hidden(A_225,k2_zfmisc_1(B_226,C_227)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1037,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_58,c_1034])).

tff(c_1106,plain,(
    ! [C_255,A_256,B_257] :
      ( k4_xboole_0(C_255,k2_tarski(A_256,B_257)) = C_255
      | r2_hidden(B_257,C_255)
      | r2_hidden(A_256,C_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1209,plain,(
    ! [D_274,A_275,B_276,C_277] :
      ( ~ r2_hidden(D_274,k2_tarski(A_275,B_276))
      | ~ r2_hidden(D_274,C_277)
      | r2_hidden(B_276,C_277)
      | r2_hidden(A_275,C_277) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1106,c_4])).

tff(c_1221,plain,(
    ! [C_278] :
      ( ~ r2_hidden(k1_mcart_1('#skF_3'),C_278)
      | r2_hidden('#skF_5',C_278)
      | r2_hidden('#skF_4',C_278) ) ),
    inference(resolution,[status(thm)],[c_1037,c_1209])).

tff(c_1245,plain,
    ( r2_hidden('#skF_5',k1_tarski(k1_mcart_1('#skF_3')))
    | r2_hidden('#skF_4',k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1002,c_1221])).

tff(c_1253,plain,(
    r2_hidden('#skF_4',k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1245])).

tff(c_1127,plain,(
    ! [A_258,B_259,C_260,D_261] :
      ( r2_hidden(k4_tarski(A_258,B_259),k2_zfmisc_1(C_260,D_261))
      | ~ r2_hidden(B_259,D_261)
      | ~ r2_hidden(A_258,C_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1139,plain,(
    ! [A_258,B_259,B_29,D_261] :
      ( k1_mcart_1(k4_tarski(A_258,B_259)) = B_29
      | ~ r2_hidden(B_259,D_261)
      | ~ r2_hidden(A_258,k1_tarski(B_29)) ) ),
    inference(resolution,[status(thm)],[c_1127,c_52])).

tff(c_1147,plain,(
    ! [B_29,A_258,B_259,D_261] :
      ( B_29 = A_258
      | ~ r2_hidden(B_259,D_261)
      | ~ r2_hidden(A_258,k1_tarski(B_29)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1139])).

tff(c_1150,plain,(
    ! [B_259,D_261] : ~ r2_hidden(B_259,D_261) ),
    inference(splitLeft,[status(thm)],[c_1147])).

tff(c_1167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1150,c_1037])).

tff(c_1168,plain,(
    ! [B_29,A_258] :
      ( B_29 = A_258
      | ~ r2_hidden(A_258,k1_tarski(B_29)) ) ),
    inference(splitRight,[status(thm)],[c_1147])).

tff(c_1260,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1253,c_1168])).

tff(c_1266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_978,c_1260])).

tff(c_1267,plain,(
    r2_hidden('#skF_5',k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1245])).

tff(c_1275,plain,(
    k1_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1267,c_1168])).

tff(c_1281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_971,c_1275])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:35:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.63/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.79  
% 3.75/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.79  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.75/1.79  
% 3.75/1.79  %Foreground sorts:
% 3.75/1.79  
% 3.75/1.79  
% 3.75/1.79  %Background operators:
% 3.75/1.79  
% 3.75/1.79  
% 3.75/1.79  %Foreground operators:
% 3.75/1.79  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.75/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.75/1.79  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.75/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.75/1.79  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.75/1.79  tff('#skF_7', type, '#skF_7': $i).
% 3.75/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.75/1.79  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.75/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.75/1.79  tff('#skF_5', type, '#skF_5': $i).
% 3.75/1.79  tff('#skF_6', type, '#skF_6': $i).
% 3.75/1.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.75/1.79  tff('#skF_3', type, '#skF_3': $i).
% 3.75/1.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.75/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.79  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.75/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.75/1.79  tff('#skF_4', type, '#skF_4': $i).
% 3.75/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.79  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.75/1.79  
% 3.75/1.81  tff(f_96, negated_conjecture, ~(![A, B, C, D, E]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k2_tarski(D, E))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & ((k2_mcart_1(A) = D) | (k2_mcart_1(A) = E))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_mcart_1)).
% 3.75/1.81  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.75/1.81  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.75/1.81  tff(f_69, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.75/1.81  tff(f_75, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.75/1.81  tff(f_63, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 3.75/1.81  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.75/1.81  tff(f_85, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.75/1.81  tff(f_53, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.75/1.81  tff(f_81, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 3.75/1.81  tff(c_60, plain, (k1_mcart_1('#skF_3')!='#skF_5' | k2_mcart_1('#skF_3')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.75/1.81  tff(c_96, plain, (k2_mcart_1('#skF_3')!='#skF_7'), inference(splitLeft, [status(thm)], [c_60])).
% 3.75/1.81  tff(c_66, plain, (k1_mcart_1('#skF_3')!='#skF_4' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.75/1.81  tff(c_97, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitLeft, [status(thm)], [c_66])).
% 3.75/1.81  tff(c_26, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.75/1.81  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.75/1.81  tff(c_107, plain, (![A_41, C_42, B_43]: (r2_hidden(A_41, C_42) | ~r1_tarski(k2_tarski(A_41, B_43), C_42))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.75/1.81  tff(c_116, plain, (![A_44, B_45]: (r2_hidden(A_44, k2_tarski(A_44, B_45)))), inference(resolution, [status(thm)], [c_24, c_107])).
% 3.75/1.81  tff(c_119, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_116])).
% 3.75/1.81  tff(c_58, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), k2_tarski('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.75/1.81  tff(c_161, plain, (![A_68, C_69, B_70]: (r2_hidden(k2_mcart_1(A_68), C_69) | ~r2_hidden(A_68, k2_zfmisc_1(B_70, C_69)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.75/1.81  tff(c_164, plain, (r2_hidden(k2_mcart_1('#skF_3'), k2_tarski('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_58, c_161])).
% 3.75/1.81  tff(c_222, plain, (![C_92, A_93, B_94]: (k4_xboole_0(C_92, k2_tarski(A_93, B_94))=C_92 | r2_hidden(B_94, C_92) | r2_hidden(A_93, C_92))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.75/1.81  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.75/1.81  tff(c_395, plain, (![D_111, A_112, B_113, C_114]: (~r2_hidden(D_111, k2_tarski(A_112, B_113)) | ~r2_hidden(D_111, C_114) | r2_hidden(B_113, C_114) | r2_hidden(A_112, C_114))), inference(superposition, [status(thm), theory('equality')], [c_222, c_4])).
% 3.75/1.81  tff(c_444, plain, (![C_116]: (~r2_hidden(k2_mcart_1('#skF_3'), C_116) | r2_hidden('#skF_7', C_116) | r2_hidden('#skF_6', C_116))), inference(resolution, [status(thm)], [c_164, c_395])).
% 3.75/1.81  tff(c_468, plain, (r2_hidden('#skF_7', k1_tarski(k2_mcart_1('#skF_3'))) | r2_hidden('#skF_6', k1_tarski(k2_mcart_1('#skF_3')))), inference(resolution, [status(thm)], [c_119, c_444])).
% 3.75/1.81  tff(c_533, plain, (r2_hidden('#skF_6', k1_tarski(k2_mcart_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_468])).
% 3.75/1.81  tff(c_54, plain, (![A_31, B_32]: (k1_mcart_1(k4_tarski(A_31, B_32))=A_31)), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.75/1.81  tff(c_261, plain, (![A_97, B_98, C_99, D_100]: (r2_hidden(k4_tarski(A_97, B_98), k2_zfmisc_1(C_99, D_100)) | ~r2_hidden(B_98, D_100) | ~r2_hidden(A_97, C_99))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.75/1.81  tff(c_52, plain, (![A_28, B_29, C_30]: (k1_mcart_1(A_28)=B_29 | ~r2_hidden(A_28, k2_zfmisc_1(k1_tarski(B_29), C_30)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.75/1.81  tff(c_275, plain, (![A_97, B_98, B_29, D_100]: (k1_mcart_1(k4_tarski(A_97, B_98))=B_29 | ~r2_hidden(B_98, D_100) | ~r2_hidden(A_97, k1_tarski(B_29)))), inference(resolution, [status(thm)], [c_261, c_52])).
% 3.75/1.81  tff(c_283, plain, (![B_29, A_97, B_98, D_100]: (B_29=A_97 | ~r2_hidden(B_98, D_100) | ~r2_hidden(A_97, k1_tarski(B_29)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_275])).
% 3.75/1.81  tff(c_284, plain, (![B_98, D_100]: (~r2_hidden(B_98, D_100))), inference(splitLeft, [status(thm)], [c_283])).
% 3.75/1.81  tff(c_165, plain, (![A_71, B_72, C_73]: (r2_hidden(k1_mcart_1(A_71), B_72) | ~r2_hidden(A_71, k2_zfmisc_1(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.75/1.81  tff(c_168, plain, (r2_hidden(k1_mcart_1('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_58, c_165])).
% 3.75/1.81  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_284, c_168])).
% 3.75/1.81  tff(c_304, plain, (![B_29, A_97]: (B_29=A_97 | ~r2_hidden(A_97, k1_tarski(B_29)))), inference(splitRight, [status(thm)], [c_283])).
% 3.75/1.81  tff(c_549, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_533, c_304])).
% 3.75/1.81  tff(c_555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97, c_549])).
% 3.75/1.81  tff(c_556, plain, (r2_hidden('#skF_7', k1_tarski(k2_mcart_1('#skF_3')))), inference(splitRight, [status(thm)], [c_468])).
% 3.75/1.81  tff(c_573, plain, (k2_mcart_1('#skF_3')='#skF_7'), inference(resolution, [status(thm)], [c_556, c_304])).
% 3.75/1.81  tff(c_579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_573])).
% 3.75/1.81  tff(c_581, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_66])).
% 3.75/1.81  tff(c_64, plain, (k1_mcart_1('#skF_3')!='#skF_5' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.75/1.81  tff(c_588, plain, (k1_mcart_1('#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_581, c_64])).
% 3.75/1.81  tff(c_580, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitRight, [status(thm)], [c_66])).
% 3.75/1.81  tff(c_608, plain, (![B_132, C_133, A_134]: (r2_hidden(B_132, C_133) | ~r1_tarski(k2_tarski(A_134, B_132), C_133))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.75/1.81  tff(c_626, plain, (![B_138, A_139]: (r2_hidden(B_138, k2_tarski(A_139, B_138)))), inference(resolution, [status(thm)], [c_24, c_608])).
% 3.75/1.81  tff(c_629, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_626])).
% 3.75/1.81  tff(c_648, plain, (![A_148, B_149, C_150]: (r2_hidden(k1_mcart_1(A_148), B_149) | ~r2_hidden(A_148, k2_zfmisc_1(B_149, C_150)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.75/1.81  tff(c_651, plain, (r2_hidden(k1_mcart_1('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_58, c_648])).
% 3.75/1.81  tff(c_715, plain, (![C_175, A_176, B_177]: (k4_xboole_0(C_175, k2_tarski(A_176, B_177))=C_175 | r2_hidden(B_177, C_175) | r2_hidden(A_176, C_175))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.75/1.81  tff(c_820, plain, (![D_194, A_195, B_196, C_197]: (~r2_hidden(D_194, k2_tarski(A_195, B_196)) | ~r2_hidden(D_194, C_197) | r2_hidden(B_196, C_197) | r2_hidden(A_195, C_197))), inference(superposition, [status(thm), theory('equality')], [c_715, c_4])).
% 3.75/1.81  tff(c_832, plain, (![C_198]: (~r2_hidden(k1_mcart_1('#skF_3'), C_198) | r2_hidden('#skF_5', C_198) | r2_hidden('#skF_4', C_198))), inference(resolution, [status(thm)], [c_651, c_820])).
% 3.75/1.81  tff(c_856, plain, (r2_hidden('#skF_5', k1_tarski(k1_mcart_1('#skF_3'))) | r2_hidden('#skF_4', k1_tarski(k1_mcart_1('#skF_3')))), inference(resolution, [status(thm)], [c_629, c_832])).
% 3.75/1.81  tff(c_858, plain, (r2_hidden('#skF_4', k1_tarski(k1_mcart_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_856])).
% 3.75/1.81  tff(c_761, plain, (![A_182, B_183, C_184, D_185]: (r2_hidden(k4_tarski(A_182, B_183), k2_zfmisc_1(C_184, D_185)) | ~r2_hidden(B_183, D_185) | ~r2_hidden(A_182, C_184))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.75/1.81  tff(c_771, plain, (![A_182, B_183, B_29, D_185]: (k1_mcart_1(k4_tarski(A_182, B_183))=B_29 | ~r2_hidden(B_183, D_185) | ~r2_hidden(A_182, k1_tarski(B_29)))), inference(resolution, [status(thm)], [c_761, c_52])).
% 3.75/1.81  tff(c_779, plain, (![B_29, A_182, B_183, D_185]: (B_29=A_182 | ~r2_hidden(B_183, D_185) | ~r2_hidden(A_182, k1_tarski(B_29)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_771])).
% 3.75/1.81  tff(c_784, plain, (![B_183, D_185]: (~r2_hidden(B_183, D_185))), inference(splitLeft, [status(thm)], [c_779])).
% 3.75/1.81  tff(c_802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_784, c_651])).
% 3.75/1.81  tff(c_803, plain, (![B_29, A_182]: (B_29=A_182 | ~r2_hidden(A_182, k1_tarski(B_29)))), inference(splitRight, [status(thm)], [c_779])).
% 3.75/1.81  tff(c_863, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_858, c_803])).
% 3.75/1.81  tff(c_870, plain, $false, inference(negUnitSimplification, [status(thm)], [c_580, c_863])).
% 3.75/1.81  tff(c_871, plain, (r2_hidden('#skF_5', k1_tarski(k1_mcart_1('#skF_3')))), inference(splitRight, [status(thm)], [c_856])).
% 3.75/1.81  tff(c_963, plain, (k1_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_871, c_803])).
% 3.75/1.81  tff(c_970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_588, c_963])).
% 3.75/1.81  tff(c_971, plain, (k1_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_60])).
% 3.75/1.81  tff(c_972, plain, (k2_mcart_1('#skF_3')='#skF_7'), inference(splitRight, [status(thm)], [c_60])).
% 3.75/1.81  tff(c_62, plain, (k1_mcart_1('#skF_3')!='#skF_4' | k2_mcart_1('#skF_3')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.75/1.81  tff(c_978, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_972, c_62])).
% 3.75/1.81  tff(c_990, plain, (![A_204, C_205, B_206]: (r2_hidden(A_204, C_205) | ~r1_tarski(k2_tarski(A_204, B_206), C_205))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.75/1.81  tff(c_999, plain, (![A_207, B_208]: (r2_hidden(A_207, k2_tarski(A_207, B_208)))), inference(resolution, [status(thm)], [c_24, c_990])).
% 3.75/1.81  tff(c_1002, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_999])).
% 3.75/1.81  tff(c_1034, plain, (![A_225, B_226, C_227]: (r2_hidden(k1_mcart_1(A_225), B_226) | ~r2_hidden(A_225, k2_zfmisc_1(B_226, C_227)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.75/1.81  tff(c_1037, plain, (r2_hidden(k1_mcart_1('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_58, c_1034])).
% 3.75/1.81  tff(c_1106, plain, (![C_255, A_256, B_257]: (k4_xboole_0(C_255, k2_tarski(A_256, B_257))=C_255 | r2_hidden(B_257, C_255) | r2_hidden(A_256, C_255))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.75/1.81  tff(c_1209, plain, (![D_274, A_275, B_276, C_277]: (~r2_hidden(D_274, k2_tarski(A_275, B_276)) | ~r2_hidden(D_274, C_277) | r2_hidden(B_276, C_277) | r2_hidden(A_275, C_277))), inference(superposition, [status(thm), theory('equality')], [c_1106, c_4])).
% 3.75/1.81  tff(c_1221, plain, (![C_278]: (~r2_hidden(k1_mcart_1('#skF_3'), C_278) | r2_hidden('#skF_5', C_278) | r2_hidden('#skF_4', C_278))), inference(resolution, [status(thm)], [c_1037, c_1209])).
% 3.75/1.81  tff(c_1245, plain, (r2_hidden('#skF_5', k1_tarski(k1_mcart_1('#skF_3'))) | r2_hidden('#skF_4', k1_tarski(k1_mcart_1('#skF_3')))), inference(resolution, [status(thm)], [c_1002, c_1221])).
% 3.75/1.81  tff(c_1253, plain, (r2_hidden('#skF_4', k1_tarski(k1_mcart_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_1245])).
% 3.75/1.81  tff(c_1127, plain, (![A_258, B_259, C_260, D_261]: (r2_hidden(k4_tarski(A_258, B_259), k2_zfmisc_1(C_260, D_261)) | ~r2_hidden(B_259, D_261) | ~r2_hidden(A_258, C_260))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.75/1.81  tff(c_1139, plain, (![A_258, B_259, B_29, D_261]: (k1_mcart_1(k4_tarski(A_258, B_259))=B_29 | ~r2_hidden(B_259, D_261) | ~r2_hidden(A_258, k1_tarski(B_29)))), inference(resolution, [status(thm)], [c_1127, c_52])).
% 3.75/1.81  tff(c_1147, plain, (![B_29, A_258, B_259, D_261]: (B_29=A_258 | ~r2_hidden(B_259, D_261) | ~r2_hidden(A_258, k1_tarski(B_29)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1139])).
% 3.75/1.81  tff(c_1150, plain, (![B_259, D_261]: (~r2_hidden(B_259, D_261))), inference(splitLeft, [status(thm)], [c_1147])).
% 3.75/1.81  tff(c_1167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1150, c_1037])).
% 3.75/1.81  tff(c_1168, plain, (![B_29, A_258]: (B_29=A_258 | ~r2_hidden(A_258, k1_tarski(B_29)))), inference(splitRight, [status(thm)], [c_1147])).
% 3.75/1.81  tff(c_1260, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_1253, c_1168])).
% 3.75/1.81  tff(c_1266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_978, c_1260])).
% 3.75/1.81  tff(c_1267, plain, (r2_hidden('#skF_5', k1_tarski(k1_mcart_1('#skF_3')))), inference(splitRight, [status(thm)], [c_1245])).
% 3.75/1.81  tff(c_1275, plain, (k1_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_1267, c_1168])).
% 3.75/1.81  tff(c_1281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_971, c_1275])).
% 3.75/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.81  
% 3.75/1.81  Inference rules
% 3.75/1.81  ----------------------
% 3.75/1.81  #Ref     : 0
% 3.75/1.81  #Sup     : 251
% 3.75/1.81  #Fact    : 0
% 3.75/1.81  #Define  : 0
% 3.75/1.81  #Split   : 9
% 3.75/1.81  #Chain   : 0
% 3.75/1.81  #Close   : 0
% 3.75/1.81  
% 3.75/1.81  Ordering : KBO
% 3.75/1.81  
% 3.75/1.81  Simplification rules
% 3.75/1.81  ----------------------
% 3.75/1.81  #Subsume      : 49
% 3.75/1.81  #Demod        : 53
% 3.75/1.81  #Tautology    : 117
% 3.75/1.81  #SimpNegUnit  : 57
% 3.75/1.81  #BackRed      : 35
% 3.75/1.81  
% 3.75/1.81  #Partial instantiations: 0
% 3.75/1.81  #Strategies tried      : 1
% 3.75/1.81  
% 3.75/1.81  Timing (in seconds)
% 3.75/1.81  ----------------------
% 3.75/1.82  Preprocessing        : 0.35
% 3.75/1.82  Parsing              : 0.17
% 3.75/1.82  CNF conversion       : 0.03
% 3.75/1.82  Main loop            : 0.68
% 3.75/1.82  Inferencing          : 0.26
% 3.75/1.82  Reduction            : 0.19
% 3.75/1.82  Demodulation         : 0.14
% 3.75/1.82  BG Simplification    : 0.03
% 3.75/1.82  Subsumption          : 0.13
% 3.75/1.82  Abstraction          : 0.04
% 3.75/1.82  MUC search           : 0.00
% 3.75/1.82  Cooper               : 0.00
% 3.75/1.82  Total                : 1.08
% 3.75/1.82  Index Insertion      : 0.00
% 3.75/1.82  Index Deletion       : 0.00
% 3.75/1.82  Index Matching       : 0.00
% 3.75/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
