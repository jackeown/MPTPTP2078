%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:53 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 220 expanded)
%              Number of leaves         :   28 (  84 expanded)
%              Depth                    :    8
%              Number of atoms          :  112 ( 377 expanded)
%              Number of equality atoms :   50 ( 240 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
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

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
      <=> ( A = C
          & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(c_501,plain,(
    ! [A_147,B_148] : k1_enumset1(A_147,A_147,B_148) = k2_tarski(A_147,B_148) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,(
    ! [A_27] : k1_enumset1(A_27,A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_517,plain,(
    ! [B_149] : k2_tarski(B_149,B_149) = k1_tarski(B_149) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_30])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_523,plain,(
    ! [B_149] : r2_hidden(B_149,k1_tarski(B_149)) ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_4])).

tff(c_32,plain,(
    ! [A_28,B_29,C_30,D_31] :
      ( r2_hidden(k4_tarski(A_28,B_29),k2_zfmisc_1(C_30,D_31))
      | ~ r2_hidden(B_29,D_31)
      | ~ r2_hidden(A_28,C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_61,plain,(
    ! [A_37,B_38] : k1_enumset1(A_37,A_37,B_38) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_77,plain,(
    ! [B_39] : k2_tarski(B_39,B_39) = k1_tarski(B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_30])).

tff(c_83,plain,(
    ! [B_39] : r2_hidden(B_39,k1_tarski(B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_4])).

tff(c_236,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( r2_hidden(k4_tarski(A_86,B_87),k2_zfmisc_1(C_88,D_89))
      | ~ r2_hidden(B_87,D_89)
      | ~ r2_hidden(A_86,C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_42,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_51,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_46,plain,
    ( '#skF_6' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_93,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_125,plain,(
    ! [A_49,C_50,B_51,D_52] :
      ( r2_hidden(A_49,C_50)
      | ~ r2_hidden(k4_tarski(A_49,B_51),k2_zfmisc_1(C_50,D_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_129,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_93,c_125])).

tff(c_68,plain,(
    ! [B_38] : k2_tarski(B_38,B_38) = k1_tarski(B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_30])).

tff(c_105,plain,(
    ! [D_44,B_45,A_46] :
      ( D_44 = B_45
      | D_44 = A_46
      | ~ r2_hidden(D_44,k2_tarski(A_46,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_108,plain,(
    ! [D_44,B_38] :
      ( D_44 = B_38
      | D_44 = B_38
      | ~ r2_hidden(D_44,k1_tarski(B_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_105])).

tff(c_132,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_129,c_108])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_51,c_132])).

tff(c_138,plain,(
    ~ r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_48,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_143,plain,(
    r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_143])).

tff(c_176,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_137,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_6')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_225,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_7','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_137,c_44])).

tff(c_226,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_225])).

tff(c_239,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_236,c_226])).

tff(c_252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_83,c_239])).

tff(c_254,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_271,plain,(
    ! [A_91,B_92] : k1_enumset1(A_91,A_91,B_92) = k2_tarski(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_287,plain,(
    ! [B_93] : k2_tarski(B_93,B_93) = k1_tarski(B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_30])).

tff(c_293,plain,(
    ! [B_93] : r2_hidden(B_93,k1_tarski(B_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_4])).

tff(c_456,plain,(
    ! [A_142,B_143,C_144,D_145] :
      ( r2_hidden(k4_tarski(A_142,B_143),k2_zfmisc_1(C_144,D_145))
      | ~ r2_hidden(B_143,D_145)
      | ~ r2_hidden(A_142,C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_350,plain,
    ( '#skF_5' = '#skF_3'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_48])).

tff(c_351,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_350])).

tff(c_253,plain,
    ( '#skF_10' != '#skF_8'
    | '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_259,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_302,plain,
    ( '#skF_6' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_46])).

tff(c_303,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_302])).

tff(c_336,plain,(
    ! [B_103,D_104,A_105,C_106] :
      ( r2_hidden(B_103,D_104)
      | ~ r2_hidden(k4_tarski(A_105,B_103),k2_zfmisc_1(C_106,D_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_340,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_10')) ),
    inference(resolution,[status(thm)],[c_303,c_336])).

tff(c_278,plain,(
    ! [B_92] : k2_tarski(B_92,B_92) = k1_tarski(B_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_30])).

tff(c_307,plain,(
    ! [D_95,B_96,A_97] :
      ( D_95 = B_96
      | D_95 = A_97
      | ~ r2_hidden(D_95,k2_tarski(A_97,B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_310,plain,(
    ! [D_95,B_92] :
      ( D_95 = B_92
      | D_95 = B_92
      | ~ r2_hidden(D_95,k1_tarski(B_92)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_307])).

tff(c_343,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_340,c_310])).

tff(c_347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_259,c_343])).

tff(c_349,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_302])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_349])).

tff(c_391,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_390,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_348,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_302])).

tff(c_434,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_9','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_390,c_348,c_44])).

tff(c_435,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_391,c_434])).

tff(c_465,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_456,c_435])).

tff(c_474,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_293,c_465])).

tff(c_476,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_40,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_486,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_476,c_40])).

tff(c_475,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_38,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_6')))
    | '#skF_10' != '#skF_8'
    | '#skF_7' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_595,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_476,c_486,c_475,c_38])).

tff(c_598,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_595])).

tff(c_602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_523,c_523,c_598])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.44  
% 2.38/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.45  %$ r2_hidden > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 2.38/1.45  
% 2.38/1.45  %Foreground sorts:
% 2.38/1.45  
% 2.38/1.45  
% 2.38/1.45  %Background operators:
% 2.38/1.45  
% 2.38/1.45  
% 2.38/1.45  %Foreground operators:
% 2.38/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.38/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.38/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.38/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.38/1.45  tff('#skF_7', type, '#skF_7': $i).
% 2.38/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.38/1.45  tff('#skF_10', type, '#skF_10': $i).
% 2.38/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.38/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.38/1.45  tff('#skF_6', type, '#skF_6': $i).
% 2.38/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.38/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.38/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.38/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.38/1.45  tff('#skF_9', type, '#skF_9': $i).
% 2.38/1.45  tff('#skF_8', type, '#skF_8': $i).
% 2.38/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.38/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.38/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.38/1.45  
% 2.67/1.48  tff(f_36, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.67/1.48  tff(f_46, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 2.67/1.48  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.67/1.48  tff(f_52, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.67/1.48  tff(f_59, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), k1_tarski(D))) <=> ((A = C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 2.67/1.48  tff(c_501, plain, (![A_147, B_148]: (k1_enumset1(A_147, A_147, B_148)=k2_tarski(A_147, B_148))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.67/1.48  tff(c_30, plain, (![A_27]: (k1_enumset1(A_27, A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.67/1.48  tff(c_517, plain, (![B_149]: (k2_tarski(B_149, B_149)=k1_tarski(B_149))), inference(superposition, [status(thm), theory('equality')], [c_501, c_30])).
% 2.67/1.48  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.67/1.48  tff(c_523, plain, (![B_149]: (r2_hidden(B_149, k1_tarski(B_149)))), inference(superposition, [status(thm), theory('equality')], [c_517, c_4])).
% 2.67/1.48  tff(c_32, plain, (![A_28, B_29, C_30, D_31]: (r2_hidden(k4_tarski(A_28, B_29), k2_zfmisc_1(C_30, D_31)) | ~r2_hidden(B_29, D_31) | ~r2_hidden(A_28, C_30))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.67/1.48  tff(c_61, plain, (![A_37, B_38]: (k1_enumset1(A_37, A_37, B_38)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.67/1.48  tff(c_77, plain, (![B_39]: (k2_tarski(B_39, B_39)=k1_tarski(B_39))), inference(superposition, [status(thm), theory('equality')], [c_61, c_30])).
% 2.67/1.48  tff(c_83, plain, (![B_39]: (r2_hidden(B_39, k1_tarski(B_39)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_4])).
% 2.67/1.48  tff(c_236, plain, (![A_86, B_87, C_88, D_89]: (r2_hidden(k4_tarski(A_86, B_87), k2_zfmisc_1(C_88, D_89)) | ~r2_hidden(B_87, D_89) | ~r2_hidden(A_86, C_88))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.67/1.48  tff(c_42, plain, ('#skF_5'='#skF_3' | '#skF_10'!='#skF_8' | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.48  tff(c_51, plain, ('#skF_7'!='#skF_9'), inference(splitLeft, [status(thm)], [c_42])).
% 2.67/1.48  tff(c_46, plain, ('#skF_6'='#skF_4' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.48  tff(c_93, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_46])).
% 2.67/1.48  tff(c_125, plain, (![A_49, C_50, B_51, D_52]: (r2_hidden(A_49, C_50) | ~r2_hidden(k4_tarski(A_49, B_51), k2_zfmisc_1(C_50, D_52)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.67/1.48  tff(c_129, plain, (r2_hidden('#skF_7', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_93, c_125])).
% 2.67/1.48  tff(c_68, plain, (![B_38]: (k2_tarski(B_38, B_38)=k1_tarski(B_38))), inference(superposition, [status(thm), theory('equality')], [c_61, c_30])).
% 2.67/1.48  tff(c_105, plain, (![D_44, B_45, A_46]: (D_44=B_45 | D_44=A_46 | ~r2_hidden(D_44, k2_tarski(A_46, B_45)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.67/1.48  tff(c_108, plain, (![D_44, B_38]: (D_44=B_38 | D_44=B_38 | ~r2_hidden(D_44, k1_tarski(B_38)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_105])).
% 2.67/1.48  tff(c_132, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_129, c_108])).
% 2.67/1.48  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_51, c_132])).
% 2.67/1.48  tff(c_138, plain, (~r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_46])).
% 2.67/1.48  tff(c_48, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.48  tff(c_143, plain, (r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_48])).
% 2.67/1.48  tff(c_175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_143])).
% 2.67/1.48  tff(c_176, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_48])).
% 2.67/1.48  tff(c_137, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_46])).
% 2.67/1.48  tff(c_44, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_6'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.48  tff(c_225, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_7', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_137, c_44])).
% 2.67/1.48  tff(c_226, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_138, c_225])).
% 2.67/1.48  tff(c_239, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_236, c_226])).
% 2.67/1.48  tff(c_252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_83, c_239])).
% 2.67/1.48  tff(c_254, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_42])).
% 2.67/1.48  tff(c_271, plain, (![A_91, B_92]: (k1_enumset1(A_91, A_91, B_92)=k2_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.67/1.48  tff(c_287, plain, (![B_93]: (k2_tarski(B_93, B_93)=k1_tarski(B_93))), inference(superposition, [status(thm), theory('equality')], [c_271, c_30])).
% 2.67/1.48  tff(c_293, plain, (![B_93]: (r2_hidden(B_93, k1_tarski(B_93)))), inference(superposition, [status(thm), theory('equality')], [c_287, c_4])).
% 2.67/1.48  tff(c_456, plain, (![A_142, B_143, C_144, D_145]: (r2_hidden(k4_tarski(A_142, B_143), k2_zfmisc_1(C_144, D_145)) | ~r2_hidden(B_143, D_145) | ~r2_hidden(A_142, C_144))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.67/1.48  tff(c_350, plain, ('#skF_5'='#skF_3' | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_48])).
% 2.67/1.48  tff(c_351, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_350])).
% 2.67/1.48  tff(c_253, plain, ('#skF_10'!='#skF_8' | '#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_42])).
% 2.67/1.48  tff(c_259, plain, ('#skF_10'!='#skF_8'), inference(splitLeft, [status(thm)], [c_253])).
% 2.67/1.48  tff(c_302, plain, ('#skF_6'='#skF_4' | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_46])).
% 2.67/1.48  tff(c_303, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_302])).
% 2.67/1.48  tff(c_336, plain, (![B_103, D_104, A_105, C_106]: (r2_hidden(B_103, D_104) | ~r2_hidden(k4_tarski(A_105, B_103), k2_zfmisc_1(C_106, D_104)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.67/1.48  tff(c_340, plain, (r2_hidden('#skF_8', k1_tarski('#skF_10'))), inference(resolution, [status(thm)], [c_303, c_336])).
% 2.67/1.48  tff(c_278, plain, (![B_92]: (k2_tarski(B_92, B_92)=k1_tarski(B_92))), inference(superposition, [status(thm), theory('equality')], [c_271, c_30])).
% 2.67/1.48  tff(c_307, plain, (![D_95, B_96, A_97]: (D_95=B_96 | D_95=A_97 | ~r2_hidden(D_95, k2_tarski(A_97, B_96)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.67/1.48  tff(c_310, plain, (![D_95, B_92]: (D_95=B_92 | D_95=B_92 | ~r2_hidden(D_95, k1_tarski(B_92)))), inference(superposition, [status(thm), theory('equality')], [c_278, c_307])).
% 2.67/1.48  tff(c_343, plain, ('#skF_10'='#skF_8'), inference(resolution, [status(thm)], [c_340, c_310])).
% 2.67/1.48  tff(c_347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_259, c_259, c_343])).
% 2.67/1.48  tff(c_349, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_302])).
% 2.67/1.48  tff(c_389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_351, c_349])).
% 2.67/1.48  tff(c_391, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_350])).
% 2.67/1.48  tff(c_390, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_350])).
% 2.67/1.48  tff(c_348, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_302])).
% 2.67/1.48  tff(c_434, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_9', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_390, c_348, c_44])).
% 2.67/1.48  tff(c_435, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_391, c_434])).
% 2.67/1.48  tff(c_465, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_456, c_435])).
% 2.67/1.48  tff(c_474, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_293, c_293, c_465])).
% 2.67/1.48  tff(c_476, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_253])).
% 2.67/1.48  tff(c_40, plain, ('#skF_6'='#skF_4' | '#skF_10'!='#skF_8' | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.48  tff(c_486, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_254, c_476, c_40])).
% 2.67/1.48  tff(c_475, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_253])).
% 2.67/1.48  tff(c_38, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_6'))) | '#skF_10'!='#skF_8' | '#skF_7'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.48  tff(c_595, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_254, c_476, c_486, c_475, c_38])).
% 2.67/1.48  tff(c_598, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_595])).
% 2.67/1.48  tff(c_602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_523, c_523, c_598])).
% 2.67/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.48  
% 2.67/1.48  Inference rules
% 2.67/1.48  ----------------------
% 2.67/1.48  #Ref     : 0
% 2.67/1.48  #Sup     : 117
% 2.67/1.48  #Fact    : 0
% 2.67/1.48  #Define  : 0
% 2.67/1.48  #Split   : 6
% 2.67/1.48  #Chain   : 0
% 2.67/1.48  #Close   : 0
% 2.67/1.48  
% 2.67/1.48  Ordering : KBO
% 2.67/1.48  
% 2.67/1.48  Simplification rules
% 2.67/1.48  ----------------------
% 2.67/1.48  #Subsume      : 6
% 2.67/1.48  #Demod        : 44
% 2.67/1.48  #Tautology    : 103
% 2.67/1.48  #SimpNegUnit  : 5
% 2.67/1.48  #BackRed      : 0
% 2.67/1.48  
% 2.67/1.48  #Partial instantiations: 0
% 2.67/1.48  #Strategies tried      : 1
% 2.67/1.48  
% 2.67/1.48  Timing (in seconds)
% 2.67/1.48  ----------------------
% 2.67/1.49  Preprocessing        : 0.34
% 2.67/1.49  Parsing              : 0.17
% 2.67/1.49  CNF conversion       : 0.03
% 2.67/1.49  Main loop            : 0.26
% 2.67/1.49  Inferencing          : 0.10
% 2.67/1.49  Reduction            : 0.08
% 2.67/1.49  Demodulation         : 0.06
% 2.67/1.49  BG Simplification    : 0.02
% 2.67/1.49  Subsumption          : 0.04
% 2.67/1.49  Abstraction          : 0.01
% 2.67/1.49  MUC search           : 0.00
% 2.67/1.49  Cooper               : 0.00
% 2.67/1.49  Total                : 0.66
% 2.67/1.49  Index Insertion      : 0.00
% 2.67/1.49  Index Deletion       : 0.00
% 2.67/1.49  Index Matching       : 0.00
% 2.67/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
