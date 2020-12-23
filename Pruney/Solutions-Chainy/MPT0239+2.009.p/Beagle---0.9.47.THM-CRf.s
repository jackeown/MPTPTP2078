%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:53 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 254 expanded)
%              Number of leaves         :   28 (  95 expanded)
%              Depth                    :    9
%              Number of atoms          :  114 ( 402 expanded)
%              Number of equality atoms :   64 ( 275 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_40,axiom,(
    ! [A,B,C,D] : k4_enumset1(A,A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C] : k4_enumset1(A,A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_enumset1)).

tff(f_38,axiom,(
    ! [A,B] : k2_enumset1(A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

tff(f_36,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
      <=> ( A = C
          & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(c_639,plain,(
    ! [A_157,B_158,C_159,D_160] : k4_enumset1(A_157,A_157,A_157,B_158,C_159,D_160) = k2_enumset1(A_157,B_158,C_159,D_160) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    ! [A_14,B_15,C_16] : k4_enumset1(A_14,A_14,A_14,A_14,B_15,C_16) = k1_enumset1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_655,plain,(
    ! [B_161,C_162,D_163] : k2_enumset1(B_161,B_161,C_162,D_163) = k1_enumset1(B_161,C_162,D_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_639,c_26])).

tff(c_22,plain,(
    ! [A_8,B_9] : k2_enumset1(A_8,A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_671,plain,(
    ! [C_164,D_165] : k1_enumset1(C_164,C_164,D_165) = k2_tarski(C_164,D_165) ),
    inference(superposition,[status(thm),theory(equality)],[c_655,c_22])).

tff(c_20,plain,(
    ! [A_7] : k1_enumset1(A_7,A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_687,plain,(
    ! [D_166] : k2_tarski(D_166,D_166) = k1_tarski(D_166) ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_20])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_696,plain,(
    ! [D_166] : r2_hidden(D_166,k1_tarski(D_166)) ),
    inference(superposition,[status(thm),theory(equality)],[c_687,c_4])).

tff(c_28,plain,(
    ! [A_17,B_18,C_19,D_20] :
      ( r2_hidden(k4_tarski(A_17,B_18),k2_zfmisc_1(C_19,D_20))
      | ~ r2_hidden(B_18,D_20)
      | ~ r2_hidden(A_17,C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_215,plain,(
    ! [A_66,B_67,C_68,D_69] : k4_enumset1(A_66,A_66,A_66,B_67,C_68,D_69) = k2_enumset1(A_66,B_67,C_68,D_69) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_231,plain,(
    ! [B_70,C_71,D_72] : k2_enumset1(B_70,B_70,C_71,D_72) = k1_enumset1(B_70,C_71,D_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_26])).

tff(c_247,plain,(
    ! [C_73,D_74] : k1_enumset1(C_73,C_73,D_74) = k2_tarski(C_73,D_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_22])).

tff(c_276,plain,(
    ! [D_79] : k2_tarski(D_79,D_79) = k1_tarski(D_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_20])).

tff(c_285,plain,(
    ! [D_79] : r2_hidden(D_79,k1_tarski(D_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_4])).

tff(c_38,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_47,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_42,plain,
    ( '#skF_6' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_78,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_32,plain,(
    ! [A_17,C_19,B_18,D_20] :
      ( r2_hidden(A_17,C_19)
      | ~ r2_hidden(k4_tarski(A_17,B_18),k2_zfmisc_1(C_19,D_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_82,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_78,c_32])).

tff(c_98,plain,(
    ! [A_42,B_43,C_44,D_45] : k4_enumset1(A_42,A_42,A_42,B_43,C_44,D_45) = k2_enumset1(A_42,B_43,C_44,D_45) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_114,plain,(
    ! [B_46,C_47,D_48] : k2_enumset1(B_46,B_46,C_47,D_48) = k1_enumset1(B_46,C_47,D_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_26])).

tff(c_130,plain,(
    ! [C_49,D_50] : k1_enumset1(C_49,C_49,D_50) = k2_tarski(C_49,D_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_22])).

tff(c_146,plain,(
    ! [D_51] : k2_tarski(D_51,D_51) = k1_tarski(D_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_20])).

tff(c_2,plain,(
    ! [D_6,B_2,A_1] :
      ( D_6 = B_2
      | D_6 = A_1
      | ~ r2_hidden(D_6,k2_tarski(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_177,plain,(
    ! [D_58,D_57] :
      ( D_58 = D_57
      | D_58 = D_57
      | ~ r2_hidden(D_57,k1_tarski(D_58)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_2])).

tff(c_186,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_82,c_177])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_47,c_186])).

tff(c_195,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_44,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_200,plain,(
    '#skF_5' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_44])).

tff(c_194,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_6')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_310,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_194,c_40])).

tff(c_311,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_310])).

tff(c_314,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_311])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_285,c_314])).

tff(c_320,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_488,plain,(
    ! [A_125,B_126,C_127,D_128] : k4_enumset1(A_125,A_125,A_125,B_126,C_127,D_128) = k2_enumset1(A_125,B_126,C_127,D_128) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_504,plain,(
    ! [B_129,C_130,D_131] : k2_enumset1(B_129,B_129,C_130,D_131) = k1_enumset1(B_129,C_130,D_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_26])).

tff(c_520,plain,(
    ! [C_132,D_133] : k1_enumset1(C_132,C_132,D_133) = k2_tarski(C_132,D_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_22])).

tff(c_536,plain,(
    ! [D_134] : k2_tarski(D_134,D_134) = k1_tarski(D_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_20])).

tff(c_545,plain,(
    ! [D_134] : r2_hidden(D_134,k1_tarski(D_134)) ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_4])).

tff(c_319,plain,
    ( '#skF_10' != '#skF_8'
    | '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_325,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_319])).

tff(c_359,plain,
    ( '#skF_6' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_42])).

tff(c_360,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_359])).

tff(c_30,plain,(
    ! [B_18,D_20,A_17,C_19] :
      ( r2_hidden(B_18,D_20)
      | ~ r2_hidden(k4_tarski(A_17,B_18),k2_zfmisc_1(C_19,D_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_367,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_360,c_30])).

tff(c_379,plain,(
    ! [A_109,B_110,C_111,D_112] : k4_enumset1(A_109,A_109,A_109,B_110,C_111,D_112) = k2_enumset1(A_109,B_110,C_111,D_112) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_395,plain,(
    ! [B_113,C_114,D_115] : k2_enumset1(B_113,B_113,C_114,D_115) = k1_enumset1(B_113,C_114,D_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_26])).

tff(c_411,plain,(
    ! [C_116,D_117] : k1_enumset1(C_116,C_116,D_117) = k2_tarski(C_116,D_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_22])).

tff(c_427,plain,(
    ! [D_118] : k2_tarski(D_118,D_118) = k1_tarski(D_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_411,c_20])).

tff(c_452,plain,(
    ! [D_121,D_120] :
      ( D_121 = D_120
      | D_121 = D_120
      | ~ r2_hidden(D_120,k1_tarski(D_121)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_427,c_2])).

tff(c_458,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_367,c_452])).

tff(c_464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_325,c_325,c_458])).

tff(c_466,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_359])).

tff(c_471,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_44])).

tff(c_472,plain,(
    '#skF_5' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_466,c_471])).

tff(c_465,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_359])).

tff(c_572,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_472,c_465,c_40])).

tff(c_573,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_466,c_572])).

tff(c_576,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_573])).

tff(c_580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_545,c_576])).

tff(c_582,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_36,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_592,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_582,c_36])).

tff(c_581,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_34,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_6')))
    | '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_718,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_582,c_592,c_581,c_34])).

tff(c_721,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_718])).

tff(c_725,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_696,c_721])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.44  
% 2.44/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.45  %$ r2_hidden > k4_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 2.44/1.45  
% 2.44/1.45  %Foreground sorts:
% 2.44/1.45  
% 2.44/1.45  
% 2.44/1.45  %Background operators:
% 2.44/1.45  
% 2.44/1.45  
% 2.44/1.45  %Foreground operators:
% 2.44/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.44/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.44/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.44/1.45  tff('#skF_7', type, '#skF_7': $i).
% 2.44/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.44/1.45  tff('#skF_10', type, '#skF_10': $i).
% 2.44/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.44/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.44/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.44/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.44/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.44/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.44/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.44/1.45  tff('#skF_9', type, '#skF_9': $i).
% 2.44/1.45  tff('#skF_8', type, '#skF_8': $i).
% 2.44/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.44/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.44/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.45  
% 2.76/1.46  tff(f_40, axiom, (![A, B, C, D]: (k4_enumset1(A, A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_enumset1)).
% 2.76/1.46  tff(f_42, axiom, (![A, B, C]: (k4_enumset1(A, A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_enumset1)).
% 2.76/1.46  tff(f_38, axiom, (![A, B]: (k2_enumset1(A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 2.76/1.46  tff(f_36, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 2.76/1.46  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.76/1.46  tff(f_48, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.76/1.46  tff(f_55, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), k1_tarski(D))) <=> ((A = C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 2.76/1.46  tff(c_639, plain, (![A_157, B_158, C_159, D_160]: (k4_enumset1(A_157, A_157, A_157, B_158, C_159, D_160)=k2_enumset1(A_157, B_158, C_159, D_160))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.76/1.46  tff(c_26, plain, (![A_14, B_15, C_16]: (k4_enumset1(A_14, A_14, A_14, A_14, B_15, C_16)=k1_enumset1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.76/1.46  tff(c_655, plain, (![B_161, C_162, D_163]: (k2_enumset1(B_161, B_161, C_162, D_163)=k1_enumset1(B_161, C_162, D_163))), inference(superposition, [status(thm), theory('equality')], [c_639, c_26])).
% 2.76/1.46  tff(c_22, plain, (![A_8, B_9]: (k2_enumset1(A_8, A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.76/1.46  tff(c_671, plain, (![C_164, D_165]: (k1_enumset1(C_164, C_164, D_165)=k2_tarski(C_164, D_165))), inference(superposition, [status(thm), theory('equality')], [c_655, c_22])).
% 2.76/1.46  tff(c_20, plain, (![A_7]: (k1_enumset1(A_7, A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.76/1.46  tff(c_687, plain, (![D_166]: (k2_tarski(D_166, D_166)=k1_tarski(D_166))), inference(superposition, [status(thm), theory('equality')], [c_671, c_20])).
% 2.76/1.46  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.76/1.46  tff(c_696, plain, (![D_166]: (r2_hidden(D_166, k1_tarski(D_166)))), inference(superposition, [status(thm), theory('equality')], [c_687, c_4])).
% 2.76/1.46  tff(c_28, plain, (![A_17, B_18, C_19, D_20]: (r2_hidden(k4_tarski(A_17, B_18), k2_zfmisc_1(C_19, D_20)) | ~r2_hidden(B_18, D_20) | ~r2_hidden(A_17, C_19))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.76/1.46  tff(c_215, plain, (![A_66, B_67, C_68, D_69]: (k4_enumset1(A_66, A_66, A_66, B_67, C_68, D_69)=k2_enumset1(A_66, B_67, C_68, D_69))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.76/1.46  tff(c_231, plain, (![B_70, C_71, D_72]: (k2_enumset1(B_70, B_70, C_71, D_72)=k1_enumset1(B_70, C_71, D_72))), inference(superposition, [status(thm), theory('equality')], [c_215, c_26])).
% 2.76/1.46  tff(c_247, plain, (![C_73, D_74]: (k1_enumset1(C_73, C_73, D_74)=k2_tarski(C_73, D_74))), inference(superposition, [status(thm), theory('equality')], [c_231, c_22])).
% 2.76/1.46  tff(c_276, plain, (![D_79]: (k2_tarski(D_79, D_79)=k1_tarski(D_79))), inference(superposition, [status(thm), theory('equality')], [c_247, c_20])).
% 2.76/1.46  tff(c_285, plain, (![D_79]: (r2_hidden(D_79, k1_tarski(D_79)))), inference(superposition, [status(thm), theory('equality')], [c_276, c_4])).
% 2.76/1.46  tff(c_38, plain, ('#skF_5'='#skF_3' | '#skF_10'!='#skF_8' | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.76/1.46  tff(c_47, plain, ('#skF_7'!='#skF_9'), inference(splitLeft, [status(thm)], [c_38])).
% 2.76/1.46  tff(c_42, plain, ('#skF_6'='#skF_4' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.76/1.46  tff(c_78, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_42])).
% 2.76/1.46  tff(c_32, plain, (![A_17, C_19, B_18, D_20]: (r2_hidden(A_17, C_19) | ~r2_hidden(k4_tarski(A_17, B_18), k2_zfmisc_1(C_19, D_20)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.76/1.46  tff(c_82, plain, (r2_hidden('#skF_7', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_78, c_32])).
% 2.76/1.46  tff(c_98, plain, (![A_42, B_43, C_44, D_45]: (k4_enumset1(A_42, A_42, A_42, B_43, C_44, D_45)=k2_enumset1(A_42, B_43, C_44, D_45))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.76/1.46  tff(c_114, plain, (![B_46, C_47, D_48]: (k2_enumset1(B_46, B_46, C_47, D_48)=k1_enumset1(B_46, C_47, D_48))), inference(superposition, [status(thm), theory('equality')], [c_98, c_26])).
% 2.76/1.46  tff(c_130, plain, (![C_49, D_50]: (k1_enumset1(C_49, C_49, D_50)=k2_tarski(C_49, D_50))), inference(superposition, [status(thm), theory('equality')], [c_114, c_22])).
% 2.76/1.46  tff(c_146, plain, (![D_51]: (k2_tarski(D_51, D_51)=k1_tarski(D_51))), inference(superposition, [status(thm), theory('equality')], [c_130, c_20])).
% 2.76/1.46  tff(c_2, plain, (![D_6, B_2, A_1]: (D_6=B_2 | D_6=A_1 | ~r2_hidden(D_6, k2_tarski(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.76/1.46  tff(c_177, plain, (![D_58, D_57]: (D_58=D_57 | D_58=D_57 | ~r2_hidden(D_57, k1_tarski(D_58)))), inference(superposition, [status(thm), theory('equality')], [c_146, c_2])).
% 2.76/1.46  tff(c_186, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_82, c_177])).
% 2.76/1.46  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_47, c_186])).
% 2.76/1.46  tff(c_195, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_42])).
% 2.76/1.46  tff(c_44, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.76/1.46  tff(c_200, plain, ('#skF_5'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_195, c_44])).
% 2.76/1.46  tff(c_194, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_42])).
% 2.76/1.46  tff(c_40, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_6'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.76/1.46  tff(c_310, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_194, c_40])).
% 2.76/1.46  tff(c_311, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_195, c_310])).
% 2.76/1.46  tff(c_314, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_311])).
% 2.76/1.46  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_285, c_285, c_314])).
% 2.76/1.46  tff(c_320, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_38])).
% 2.76/1.46  tff(c_488, plain, (![A_125, B_126, C_127, D_128]: (k4_enumset1(A_125, A_125, A_125, B_126, C_127, D_128)=k2_enumset1(A_125, B_126, C_127, D_128))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.76/1.46  tff(c_504, plain, (![B_129, C_130, D_131]: (k2_enumset1(B_129, B_129, C_130, D_131)=k1_enumset1(B_129, C_130, D_131))), inference(superposition, [status(thm), theory('equality')], [c_488, c_26])).
% 2.76/1.46  tff(c_520, plain, (![C_132, D_133]: (k1_enumset1(C_132, C_132, D_133)=k2_tarski(C_132, D_133))), inference(superposition, [status(thm), theory('equality')], [c_504, c_22])).
% 2.76/1.46  tff(c_536, plain, (![D_134]: (k2_tarski(D_134, D_134)=k1_tarski(D_134))), inference(superposition, [status(thm), theory('equality')], [c_520, c_20])).
% 2.76/1.46  tff(c_545, plain, (![D_134]: (r2_hidden(D_134, k1_tarski(D_134)))), inference(superposition, [status(thm), theory('equality')], [c_536, c_4])).
% 2.76/1.46  tff(c_319, plain, ('#skF_10'!='#skF_8' | '#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 2.76/1.46  tff(c_325, plain, ('#skF_10'!='#skF_8'), inference(splitLeft, [status(thm)], [c_319])).
% 2.76/1.46  tff(c_359, plain, ('#skF_6'='#skF_4' | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_42])).
% 2.76/1.46  tff(c_360, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_359])).
% 2.76/1.46  tff(c_30, plain, (![B_18, D_20, A_17, C_19]: (r2_hidden(B_18, D_20) | ~r2_hidden(k4_tarski(A_17, B_18), k2_zfmisc_1(C_19, D_20)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.76/1.46  tff(c_367, plain, (r2_hidden('#skF_8', k1_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_360, c_30])).
% 2.76/1.46  tff(c_379, plain, (![A_109, B_110, C_111, D_112]: (k4_enumset1(A_109, A_109, A_109, B_110, C_111, D_112)=k2_enumset1(A_109, B_110, C_111, D_112))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.76/1.46  tff(c_395, plain, (![B_113, C_114, D_115]: (k2_enumset1(B_113, B_113, C_114, D_115)=k1_enumset1(B_113, C_114, D_115))), inference(superposition, [status(thm), theory('equality')], [c_379, c_26])).
% 2.76/1.46  tff(c_411, plain, (![C_116, D_117]: (k1_enumset1(C_116, C_116, D_117)=k2_tarski(C_116, D_117))), inference(superposition, [status(thm), theory('equality')], [c_395, c_22])).
% 2.76/1.46  tff(c_427, plain, (![D_118]: (k2_tarski(D_118, D_118)=k1_tarski(D_118))), inference(superposition, [status(thm), theory('equality')], [c_411, c_20])).
% 2.76/1.46  tff(c_452, plain, (![D_121, D_120]: (D_121=D_120 | D_121=D_120 | ~r2_hidden(D_120, k1_tarski(D_121)))), inference(superposition, [status(thm), theory('equality')], [c_427, c_2])).
% 2.76/1.46  tff(c_458, plain, ('#skF_10'='#skF_8'), inference(resolution, [status(thm)], [c_367, c_452])).
% 2.76/1.46  tff(c_464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_325, c_325, c_458])).
% 2.76/1.46  tff(c_466, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_359])).
% 2.76/1.46  tff(c_471, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_44])).
% 2.76/1.46  tff(c_472, plain, ('#skF_5'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_466, c_471])).
% 2.76/1.46  tff(c_465, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_359])).
% 2.76/1.46  tff(c_572, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_472, c_465, c_40])).
% 2.76/1.46  tff(c_573, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_466, c_572])).
% 2.76/1.46  tff(c_576, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_573])).
% 2.76/1.46  tff(c_580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_545, c_545, c_576])).
% 2.76/1.46  tff(c_582, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_319])).
% 2.76/1.46  tff(c_36, plain, ('#skF_6'='#skF_4' | '#skF_10'!='#skF_8' | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.76/1.46  tff(c_592, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_320, c_582, c_36])).
% 2.76/1.46  tff(c_581, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_319])).
% 2.76/1.46  tff(c_34, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_6'))) | '#skF_10'!='#skF_8' | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.76/1.46  tff(c_718, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_582, c_592, c_581, c_34])).
% 2.76/1.46  tff(c_721, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_718])).
% 2.76/1.46  tff(c_725, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_696, c_696, c_721])).
% 2.76/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.46  
% 2.76/1.46  Inference rules
% 2.76/1.46  ----------------------
% 2.76/1.46  #Ref     : 0
% 2.76/1.46  #Sup     : 152
% 2.76/1.46  #Fact    : 0
% 2.76/1.46  #Define  : 0
% 2.76/1.46  #Split   : 5
% 2.76/1.46  #Chain   : 0
% 2.76/1.46  #Close   : 0
% 2.76/1.46  
% 2.76/1.46  Ordering : KBO
% 2.76/1.46  
% 2.76/1.46  Simplification rules
% 2.76/1.46  ----------------------
% 2.76/1.46  #Subsume      : 6
% 2.76/1.46  #Demod        : 51
% 2.76/1.46  #Tautology    : 114
% 2.76/1.46  #SimpNegUnit  : 6
% 2.76/1.46  #BackRed      : 0
% 2.76/1.46  
% 2.76/1.46  #Partial instantiations: 0
% 2.76/1.46  #Strategies tried      : 1
% 2.76/1.46  
% 2.76/1.46  Timing (in seconds)
% 2.76/1.47  ----------------------
% 2.76/1.47  Preprocessing        : 0.34
% 2.76/1.47  Parsing              : 0.16
% 2.76/1.47  CNF conversion       : 0.03
% 2.76/1.47  Main loop            : 0.28
% 2.76/1.47  Inferencing          : 0.12
% 2.76/1.47  Reduction            : 0.09
% 2.76/1.47  Demodulation         : 0.06
% 2.76/1.47  BG Simplification    : 0.02
% 2.76/1.47  Subsumption          : 0.04
% 2.76/1.47  Abstraction          : 0.02
% 2.76/1.47  MUC search           : 0.00
% 2.76/1.47  Cooper               : 0.00
% 2.76/1.47  Total                : 0.66
% 2.76/1.47  Index Insertion      : 0.00
% 2.76/1.47  Index Deletion       : 0.00
% 2.76/1.47  Index Matching       : 0.00
% 2.76/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
