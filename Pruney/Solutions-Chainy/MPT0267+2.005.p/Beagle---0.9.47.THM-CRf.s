%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:32 EST 2020

% Result     : Theorem 6.25s
% Output     : CNFRefutation 6.25s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 280 expanded)
%              Number of leaves         :   32 ( 101 expanded)
%              Depth                    :   12
%              Number of atoms          :  209 ( 523 expanded)
%              Number of equality atoms :   32 ( 146 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
      <=> ( r2_hidden(A,B)
          & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_30,plain,(
    ! [C_21] : r2_hidden(C_21,k1_tarski(C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_60,plain,
    ( '#skF_6' != '#skF_4'
    | r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_123,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_62,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_220,plain,(
    r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_130,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k4_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_139,plain,(
    ! [A_55,B_56] : r1_xboole_0(k3_xboole_0(A_55,B_56),k4_xboole_0(A_55,B_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_26])).

tff(c_231,plain,(
    ! [A_70,B_71,C_72] :
      ( ~ r1_xboole_0(A_70,B_71)
      | ~ r2_hidden(C_72,B_71)
      | ~ r2_hidden(C_72,A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_366,plain,(
    ! [C_92,A_93,B_94] :
      ( ~ r2_hidden(C_92,k4_xboole_0(A_93,B_94))
      | ~ r2_hidden(C_92,k3_xboole_0(A_93,B_94)) ) ),
    inference(resolution,[status(thm)],[c_139,c_231])).

tff(c_384,plain,(
    ~ r2_hidden('#skF_7',k3_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(resolution,[status(thm)],[c_220,c_366])).

tff(c_54,plain,
    ( '#skF_6' != '#skF_4'
    | '#skF_7' = '#skF_9'
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_122,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_22,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_481,plain,(
    ! [A_106,B_107,C_108] :
      ( r2_hidden(A_106,B_107)
      | r2_hidden(A_106,C_108)
      | ~ r2_hidden(A_106,k5_xboole_0(B_107,C_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1135,plain,(
    ! [A_181,A_182,B_183] :
      ( r2_hidden(A_181,A_182)
      | r2_hidden(A_181,k3_xboole_0(A_182,B_183))
      | ~ r2_hidden(A_181,k4_xboole_0(A_182,B_183)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_481])).

tff(c_1152,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | r2_hidden('#skF_7',k3_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(resolution,[status(thm)],[c_220,c_1135])).

tff(c_1169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_384,c_122,c_1152])).

tff(c_1170,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1391,plain,(
    ! [A_217,C_218,B_219] :
      ( r2_hidden(A_217,C_218)
      | ~ r2_hidden(A_217,B_219)
      | r2_hidden(A_217,k5_xboole_0(B_219,C_218)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2044,plain,(
    ! [A_286,A_287,B_288] :
      ( r2_hidden(A_286,k3_xboole_0(A_287,B_288))
      | ~ r2_hidden(A_286,A_287)
      | r2_hidden(A_286,k4_xboole_0(A_287,B_288)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1391])).

tff(c_1171,plain,(
    ~ r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_58,plain,
    ( ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1245,plain,(
    ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1171,c_58])).

tff(c_2064,plain,
    ( r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_2044,c_1245])).

tff(c_2087,plain,(
    r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1170,c_2064])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1419,plain,(
    ! [A_223,B_224,C_225] :
      ( r2_hidden(A_223,B_224)
      | ~ r2_hidden(A_223,C_225)
      | r2_hidden(A_223,k5_xboole_0(B_224,C_225)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1940,plain,(
    ! [A_277,A_278,B_279] :
      ( r2_hidden(A_277,A_278)
      | ~ r2_hidden(A_277,k3_xboole_0(A_278,B_279))
      | r2_hidden(A_277,k4_xboole_0(A_278,B_279)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1419])).

tff(c_24,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1182,plain,(
    ! [A_187,B_188,C_189] :
      ( ~ r1_xboole_0(A_187,B_188)
      | ~ r2_hidden(C_189,B_188)
      | ~ r2_hidden(C_189,A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1192,plain,(
    ! [C_190,B_191,A_192] :
      ( ~ r2_hidden(C_190,B_191)
      | ~ r2_hidden(C_190,k4_xboole_0(A_192,B_191)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1182])).

tff(c_1199,plain,(
    ! [C_190,A_13,B_14] :
      ( ~ r2_hidden(C_190,k4_xboole_0(A_13,B_14))
      | ~ r2_hidden(C_190,k3_xboole_0(A_13,B_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1192])).

tff(c_1986,plain,(
    ! [A_280,A_281,B_282] :
      ( r2_hidden(A_280,A_281)
      | ~ r2_hidden(A_280,k3_xboole_0(A_281,B_282)) ) ),
    inference(resolution,[status(thm)],[c_1940,c_1199])).

tff(c_2005,plain,(
    ! [A_280,A_1,B_2] :
      ( r2_hidden(A_280,A_1)
      | ~ r2_hidden(A_280,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1986])).

tff(c_2096,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_2087,c_2005])).

tff(c_28,plain,(
    ! [C_21,A_17] :
      ( C_21 = A_17
      | ~ r2_hidden(C_21,k1_tarski(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2103,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2096,c_28])).

tff(c_2108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_2103])).

tff(c_2109,plain,(
    r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2115,plain,(
    ! [A_289,B_290] : k4_xboole_0(A_289,k4_xboole_0(A_289,B_290)) = k3_xboole_0(A_289,B_290) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2124,plain,(
    ! [A_289,B_290] : r1_xboole_0(k3_xboole_0(A_289,B_290),k4_xboole_0(A_289,B_290)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2115,c_26])).

tff(c_2213,plain,(
    ! [A_303,B_304,C_305] :
      ( ~ r1_xboole_0(A_303,B_304)
      | ~ r2_hidden(C_305,B_304)
      | ~ r2_hidden(C_305,A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2358,plain,(
    ! [C_328,A_329,B_330] :
      ( ~ r2_hidden(C_328,k4_xboole_0(A_329,B_330))
      | ~ r2_hidden(C_328,k3_xboole_0(A_329,B_330)) ) ),
    inference(resolution,[status(thm)],[c_2124,c_2213])).

tff(c_2378,plain,(
    ~ r2_hidden('#skF_7',k3_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(resolution,[status(thm)],[c_2109,c_2358])).

tff(c_2464,plain,(
    ! [A_338,B_339,C_340] :
      ( r2_hidden(A_338,B_339)
      | r2_hidden(A_338,C_340)
      | ~ r2_hidden(A_338,k5_xboole_0(B_339,C_340)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3904,plain,(
    ! [A_445,A_446,B_447] :
      ( r2_hidden(A_445,A_446)
      | r2_hidden(A_445,k3_xboole_0(A_446,B_447))
      | ~ r2_hidden(A_445,k4_xboole_0(A_446,B_447)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2464])).

tff(c_3941,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | r2_hidden('#skF_7',k3_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(resolution,[status(thm)],[c_2109,c_3904])).

tff(c_3950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2378,c_122,c_3941])).

tff(c_3951,plain,
    ( '#skF_6' != '#skF_4'
    | '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_3953,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3951])).

tff(c_3952,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_56,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | '#skF_7' = '#skF_9'
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3955,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | '#skF_7' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3952,c_56])).

tff(c_3956,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_3955])).

tff(c_4025,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3956,c_62])).

tff(c_4026,plain,(
    r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_4025])).

tff(c_4070,plain,(
    ! [A_465,B_466,C_467] :
      ( ~ r1_xboole_0(A_465,B_466)
      | ~ r2_hidden(C_467,B_466)
      | ~ r2_hidden(C_467,A_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4080,plain,(
    ! [C_468,B_469,A_470] :
      ( ~ r2_hidden(C_468,B_469)
      | ~ r2_hidden(C_468,k4_xboole_0(A_470,B_469)) ) ),
    inference(resolution,[status(thm)],[c_26,c_4070])).

tff(c_4087,plain,(
    ~ r2_hidden('#skF_9',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_4026,c_4080])).

tff(c_4099,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4087])).

tff(c_4100,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_4025])).

tff(c_4384,plain,(
    ! [A_512,C_513,B_514] :
      ( r2_hidden(A_512,C_513)
      | ~ r2_hidden(A_512,B_514)
      | r2_hidden(A_512,k5_xboole_0(B_514,C_513)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4763,plain,(
    ! [A_561,A_562,B_563] :
      ( r2_hidden(A_561,k3_xboole_0(A_562,B_563))
      | ~ r2_hidden(A_561,A_562)
      | r2_hidden(A_561,k4_xboole_0(A_562,B_563)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4384])).

tff(c_4101,plain,(
    ~ r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_4025])).

tff(c_4186,plain,
    ( ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3956,c_58])).

tff(c_4187,plain,(
    ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_4101,c_4186])).

tff(c_4783,plain,
    ( r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_4763,c_4187])).

tff(c_4803,plain,(
    r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4100,c_4783])).

tff(c_4157,plain,(
    ! [A_481,B_482,C_483] :
      ( r2_hidden(A_481,B_482)
      | ~ r2_hidden(A_481,C_483)
      | r2_hidden(A_481,k5_xboole_0(B_482,C_483)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4845,plain,(
    ! [A_570,A_571,B_572] :
      ( r2_hidden(A_570,A_571)
      | ~ r2_hidden(A_570,k3_xboole_0(A_571,B_572))
      | r2_hidden(A_570,k4_xboole_0(A_571,B_572)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4157])).

tff(c_4147,plain,(
    ! [A_478,B_479,C_480] :
      ( ~ r1_xboole_0(A_478,B_479)
      | ~ r2_hidden(C_480,B_479)
      | ~ r2_hidden(C_480,A_478) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4164,plain,(
    ! [C_484,B_485,A_486] :
      ( ~ r2_hidden(C_484,B_485)
      | ~ r2_hidden(C_484,k4_xboole_0(A_486,B_485)) ) ),
    inference(resolution,[status(thm)],[c_26,c_4147])).

tff(c_4175,plain,(
    ! [C_484,A_13,B_14] :
      ( ~ r2_hidden(C_484,k4_xboole_0(A_13,B_14))
      | ~ r2_hidden(C_484,k3_xboole_0(A_13,B_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4164])).

tff(c_4889,plain,(
    ! [A_573,A_574,B_575] :
      ( r2_hidden(A_573,A_574)
      | ~ r2_hidden(A_573,k3_xboole_0(A_574,B_575)) ) ),
    inference(resolution,[status(thm)],[c_4845,c_4175])).

tff(c_4934,plain,(
    ! [A_576,A_577,B_578] :
      ( r2_hidden(A_576,A_577)
      | ~ r2_hidden(A_576,k3_xboole_0(B_578,A_577)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4889])).

tff(c_4973,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_4803,c_4934])).

tff(c_4980,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4973,c_28])).

tff(c_4984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3953,c_4980])).

tff(c_4985,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_3955])).

tff(c_5358,plain,(
    ! [A_629,C_630,B_631] :
      ( r2_hidden(A_629,C_630)
      | ~ r2_hidden(A_629,B_631)
      | r2_hidden(A_629,k5_xboole_0(B_631,C_630)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5741,plain,(
    ! [A_680,A_681,B_682] :
      ( r2_hidden(A_680,k3_xboole_0(A_681,B_682))
      | ~ r2_hidden(A_680,A_681)
      | r2_hidden(A_680,k4_xboole_0(A_681,B_682)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_5358])).

tff(c_4986,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_3955])).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | '#skF_7' = '#skF_9'
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_5052,plain,
    ( ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | '#skF_7' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3952,c_52])).

tff(c_5053,plain,(
    ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_4986,c_5052])).

tff(c_5761,plain,
    ( r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_5741,c_5053])).

tff(c_5778,plain,(
    r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4985,c_5761])).

tff(c_5204,plain,(
    ! [A_612,B_613,C_614] :
      ( r2_hidden(A_612,B_613)
      | ~ r2_hidden(A_612,C_614)
      | r2_hidden(A_612,k5_xboole_0(B_613,C_614)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6160,plain,(
    ! [A_708,A_709,B_710] :
      ( r2_hidden(A_708,A_709)
      | ~ r2_hidden(A_708,k3_xboole_0(A_709,B_710))
      | r2_hidden(A_708,k4_xboole_0(A_709,B_710)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_5204])).

tff(c_5003,plain,(
    ! [A_581,B_582] : k4_xboole_0(A_581,k4_xboole_0(A_581,B_582)) = k3_xboole_0(A_581,B_582) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_5012,plain,(
    ! [A_581,B_582] : r1_xboole_0(k3_xboole_0(A_581,B_582),k4_xboole_0(A_581,B_582)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5003,c_26])).

tff(c_5088,plain,(
    ! [A_593,B_594,C_595] :
      ( ~ r1_xboole_0(A_593,B_594)
      | ~ r2_hidden(C_595,B_594)
      | ~ r2_hidden(C_595,A_593) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_5096,plain,(
    ! [C_595,A_581,B_582] :
      ( ~ r2_hidden(C_595,k4_xboole_0(A_581,B_582))
      | ~ r2_hidden(C_595,k3_xboole_0(A_581,B_582)) ) ),
    inference(resolution,[status(thm)],[c_5012,c_5088])).

tff(c_6213,plain,(
    ! [A_711,A_712,B_713] :
      ( r2_hidden(A_711,A_712)
      | ~ r2_hidden(A_711,k3_xboole_0(A_712,B_713)) ) ),
    inference(resolution,[status(thm)],[c_6160,c_5096])).

tff(c_6253,plain,(
    ! [A_714,A_715,B_716] :
      ( r2_hidden(A_714,A_715)
      | ~ r2_hidden(A_714,k3_xboole_0(B_716,A_715)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_6213])).

tff(c_6287,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_5778,c_6253])).

tff(c_6298,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6287,c_28])).

tff(c_6304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3953,c_6298])).

tff(c_6305,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_3951])).

tff(c_6306,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3951])).

tff(c_6307,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_6318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6306,c_6307])).

tff(c_6319,plain,(
    r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_6331,plain,(
    r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6305,c_6319])).

tff(c_6443,plain,(
    ! [A_734,B_735,C_736] :
      ( ~ r1_xboole_0(A_734,B_735)
      | ~ r2_hidden(C_736,B_735)
      | ~ r2_hidden(C_736,A_734) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6453,plain,(
    ! [C_737,B_738,A_739] :
      ( ~ r2_hidden(C_737,B_738)
      | ~ r2_hidden(C_737,k4_xboole_0(A_739,B_738)) ) ),
    inference(resolution,[status(thm)],[c_26,c_6443])).

tff(c_6467,plain,(
    ~ r2_hidden('#skF_9',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_6331,c_6453])).

tff(c_6473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6467])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:42:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.25/2.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.25/2.23  
% 6.25/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.25/2.23  %$ r2_hidden > r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 6.25/2.23  
% 6.25/2.23  %Foreground sorts:
% 6.25/2.23  
% 6.25/2.23  
% 6.25/2.23  %Background operators:
% 6.25/2.23  
% 6.25/2.23  
% 6.25/2.23  %Foreground operators:
% 6.25/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.25/2.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.25/2.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.25/2.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.25/2.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.25/2.23  tff('#skF_7', type, '#skF_7': $i).
% 6.25/2.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.25/2.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.25/2.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.25/2.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.25/2.23  tff('#skF_5', type, '#skF_5': $i).
% 6.25/2.23  tff('#skF_6', type, '#skF_6': $i).
% 6.25/2.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.25/2.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.25/2.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.25/2.23  tff('#skF_9', type, '#skF_9': $i).
% 6.25/2.23  tff('#skF_8', type, '#skF_8': $i).
% 6.25/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.25/2.23  tff('#skF_4', type, '#skF_4': $i).
% 6.25/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.25/2.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.25/2.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.25/2.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.25/2.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.25/2.23  
% 6.25/2.25  tff(f_65, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 6.25/2.25  tff(f_85, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 6.25/2.25  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.25/2.25  tff(f_58, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 6.25/2.25  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.25/2.25  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.25/2.25  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 6.25/2.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.25/2.25  tff(c_30, plain, (![C_21]: (r2_hidden(C_21, k1_tarski(C_21)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.25/2.25  tff(c_60, plain, ('#skF_6'!='#skF_4' | r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.25/2.25  tff(c_123, plain, ('#skF_6'!='#skF_4'), inference(splitLeft, [status(thm)], [c_60])).
% 6.25/2.25  tff(c_62, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.25/2.25  tff(c_220, plain, (r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitLeft, [status(thm)], [c_62])).
% 6.25/2.25  tff(c_130, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k4_xboole_0(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.25/2.25  tff(c_26, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.25/2.25  tff(c_139, plain, (![A_55, B_56]: (r1_xboole_0(k3_xboole_0(A_55, B_56), k4_xboole_0(A_55, B_56)))), inference(superposition, [status(thm), theory('equality')], [c_130, c_26])).
% 6.25/2.25  tff(c_231, plain, (![A_70, B_71, C_72]: (~r1_xboole_0(A_70, B_71) | ~r2_hidden(C_72, B_71) | ~r2_hidden(C_72, A_70))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.25/2.25  tff(c_366, plain, (![C_92, A_93, B_94]: (~r2_hidden(C_92, k4_xboole_0(A_93, B_94)) | ~r2_hidden(C_92, k3_xboole_0(A_93, B_94)))), inference(resolution, [status(thm)], [c_139, c_231])).
% 6.25/2.25  tff(c_384, plain, (~r2_hidden('#skF_7', k3_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(resolution, [status(thm)], [c_220, c_366])).
% 6.25/2.25  tff(c_54, plain, ('#skF_6'!='#skF_4' | '#skF_7'='#skF_9' | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.25/2.25  tff(c_122, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_54])).
% 6.25/2.25  tff(c_22, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.25/2.25  tff(c_481, plain, (![A_106, B_107, C_108]: (r2_hidden(A_106, B_107) | r2_hidden(A_106, C_108) | ~r2_hidden(A_106, k5_xboole_0(B_107, C_108)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.25/2.25  tff(c_1135, plain, (![A_181, A_182, B_183]: (r2_hidden(A_181, A_182) | r2_hidden(A_181, k3_xboole_0(A_182, B_183)) | ~r2_hidden(A_181, k4_xboole_0(A_182, B_183)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_481])).
% 6.25/2.25  tff(c_1152, plain, (r2_hidden('#skF_7', '#skF_8') | r2_hidden('#skF_7', k3_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(resolution, [status(thm)], [c_220, c_1135])).
% 6.25/2.25  tff(c_1169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_384, c_122, c_1152])).
% 6.25/2.25  tff(c_1170, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_62])).
% 6.25/2.25  tff(c_1391, plain, (![A_217, C_218, B_219]: (r2_hidden(A_217, C_218) | ~r2_hidden(A_217, B_219) | r2_hidden(A_217, k5_xboole_0(B_219, C_218)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.25/2.25  tff(c_2044, plain, (![A_286, A_287, B_288]: (r2_hidden(A_286, k3_xboole_0(A_287, B_288)) | ~r2_hidden(A_286, A_287) | r2_hidden(A_286, k4_xboole_0(A_287, B_288)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1391])).
% 6.25/2.25  tff(c_1171, plain, (~r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_62])).
% 6.25/2.25  tff(c_58, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6'))) | r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.25/2.25  tff(c_1245, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_1171, c_58])).
% 6.25/2.25  tff(c_2064, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6'))) | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_2044, c_1245])).
% 6.25/2.25  tff(c_2087, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_1170, c_2064])).
% 6.25/2.25  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.25/2.25  tff(c_1419, plain, (![A_223, B_224, C_225]: (r2_hidden(A_223, B_224) | ~r2_hidden(A_223, C_225) | r2_hidden(A_223, k5_xboole_0(B_224, C_225)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.25/2.25  tff(c_1940, plain, (![A_277, A_278, B_279]: (r2_hidden(A_277, A_278) | ~r2_hidden(A_277, k3_xboole_0(A_278, B_279)) | r2_hidden(A_277, k4_xboole_0(A_278, B_279)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1419])).
% 6.25/2.25  tff(c_24, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.25/2.25  tff(c_1182, plain, (![A_187, B_188, C_189]: (~r1_xboole_0(A_187, B_188) | ~r2_hidden(C_189, B_188) | ~r2_hidden(C_189, A_187))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.25/2.25  tff(c_1192, plain, (![C_190, B_191, A_192]: (~r2_hidden(C_190, B_191) | ~r2_hidden(C_190, k4_xboole_0(A_192, B_191)))), inference(resolution, [status(thm)], [c_26, c_1182])).
% 6.25/2.25  tff(c_1199, plain, (![C_190, A_13, B_14]: (~r2_hidden(C_190, k4_xboole_0(A_13, B_14)) | ~r2_hidden(C_190, k3_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1192])).
% 6.25/2.25  tff(c_1986, plain, (![A_280, A_281, B_282]: (r2_hidden(A_280, A_281) | ~r2_hidden(A_280, k3_xboole_0(A_281, B_282)))), inference(resolution, [status(thm)], [c_1940, c_1199])).
% 6.25/2.25  tff(c_2005, plain, (![A_280, A_1, B_2]: (r2_hidden(A_280, A_1) | ~r2_hidden(A_280, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1986])).
% 6.25/2.25  tff(c_2096, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_2087, c_2005])).
% 6.25/2.25  tff(c_28, plain, (![C_21, A_17]: (C_21=A_17 | ~r2_hidden(C_21, k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.25/2.25  tff(c_2103, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_2096, c_28])).
% 6.25/2.25  tff(c_2108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_2103])).
% 6.25/2.25  tff(c_2109, plain, (r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_60])).
% 6.25/2.25  tff(c_2115, plain, (![A_289, B_290]: (k4_xboole_0(A_289, k4_xboole_0(A_289, B_290))=k3_xboole_0(A_289, B_290))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.25/2.25  tff(c_2124, plain, (![A_289, B_290]: (r1_xboole_0(k3_xboole_0(A_289, B_290), k4_xboole_0(A_289, B_290)))), inference(superposition, [status(thm), theory('equality')], [c_2115, c_26])).
% 6.25/2.25  tff(c_2213, plain, (![A_303, B_304, C_305]: (~r1_xboole_0(A_303, B_304) | ~r2_hidden(C_305, B_304) | ~r2_hidden(C_305, A_303))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.25/2.25  tff(c_2358, plain, (![C_328, A_329, B_330]: (~r2_hidden(C_328, k4_xboole_0(A_329, B_330)) | ~r2_hidden(C_328, k3_xboole_0(A_329, B_330)))), inference(resolution, [status(thm)], [c_2124, c_2213])).
% 6.25/2.25  tff(c_2378, plain, (~r2_hidden('#skF_7', k3_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(resolution, [status(thm)], [c_2109, c_2358])).
% 6.25/2.25  tff(c_2464, plain, (![A_338, B_339, C_340]: (r2_hidden(A_338, B_339) | r2_hidden(A_338, C_340) | ~r2_hidden(A_338, k5_xboole_0(B_339, C_340)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.25/2.25  tff(c_3904, plain, (![A_445, A_446, B_447]: (r2_hidden(A_445, A_446) | r2_hidden(A_445, k3_xboole_0(A_446, B_447)) | ~r2_hidden(A_445, k4_xboole_0(A_446, B_447)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2464])).
% 6.25/2.25  tff(c_3941, plain, (r2_hidden('#skF_7', '#skF_8') | r2_hidden('#skF_7', k3_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(resolution, [status(thm)], [c_2109, c_3904])).
% 6.25/2.25  tff(c_3950, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2378, c_122, c_3941])).
% 6.25/2.25  tff(c_3951, plain, ('#skF_6'!='#skF_4' | '#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_54])).
% 6.25/2.25  tff(c_3953, plain, ('#skF_6'!='#skF_4'), inference(splitLeft, [status(thm)], [c_3951])).
% 6.25/2.25  tff(c_3952, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_54])).
% 6.25/2.25  tff(c_56, plain, (r2_hidden('#skF_4', '#skF_5') | '#skF_7'='#skF_9' | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.25/2.25  tff(c_3955, plain, (r2_hidden('#skF_4', '#skF_5') | '#skF_7'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_3952, c_56])).
% 6.25/2.25  tff(c_3956, plain, ('#skF_7'='#skF_9'), inference(splitLeft, [status(thm)], [c_3955])).
% 6.25/2.25  tff(c_4025, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_3956, c_62])).
% 6.25/2.25  tff(c_4026, plain, (r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitLeft, [status(thm)], [c_4025])).
% 6.25/2.25  tff(c_4070, plain, (![A_465, B_466, C_467]: (~r1_xboole_0(A_465, B_466) | ~r2_hidden(C_467, B_466) | ~r2_hidden(C_467, A_465))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.25/2.25  tff(c_4080, plain, (![C_468, B_469, A_470]: (~r2_hidden(C_468, B_469) | ~r2_hidden(C_468, k4_xboole_0(A_470, B_469)))), inference(resolution, [status(thm)], [c_26, c_4070])).
% 6.25/2.25  tff(c_4087, plain, (~r2_hidden('#skF_9', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_4026, c_4080])).
% 6.25/2.25  tff(c_4099, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_4087])).
% 6.25/2.25  tff(c_4100, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_4025])).
% 6.25/2.25  tff(c_4384, plain, (![A_512, C_513, B_514]: (r2_hidden(A_512, C_513) | ~r2_hidden(A_512, B_514) | r2_hidden(A_512, k5_xboole_0(B_514, C_513)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.25/2.25  tff(c_4763, plain, (![A_561, A_562, B_563]: (r2_hidden(A_561, k3_xboole_0(A_562, B_563)) | ~r2_hidden(A_561, A_562) | r2_hidden(A_561, k4_xboole_0(A_562, B_563)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_4384])).
% 6.25/2.25  tff(c_4101, plain, (~r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_4025])).
% 6.25/2.25  tff(c_4186, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6'))) | r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_3956, c_58])).
% 6.25/2.25  tff(c_4187, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_4101, c_4186])).
% 6.25/2.25  tff(c_4783, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6'))) | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_4763, c_4187])).
% 6.25/2.25  tff(c_4803, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_4100, c_4783])).
% 6.25/2.25  tff(c_4157, plain, (![A_481, B_482, C_483]: (r2_hidden(A_481, B_482) | ~r2_hidden(A_481, C_483) | r2_hidden(A_481, k5_xboole_0(B_482, C_483)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.25/2.25  tff(c_4845, plain, (![A_570, A_571, B_572]: (r2_hidden(A_570, A_571) | ~r2_hidden(A_570, k3_xboole_0(A_571, B_572)) | r2_hidden(A_570, k4_xboole_0(A_571, B_572)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_4157])).
% 6.25/2.25  tff(c_4147, plain, (![A_478, B_479, C_480]: (~r1_xboole_0(A_478, B_479) | ~r2_hidden(C_480, B_479) | ~r2_hidden(C_480, A_478))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.25/2.25  tff(c_4164, plain, (![C_484, B_485, A_486]: (~r2_hidden(C_484, B_485) | ~r2_hidden(C_484, k4_xboole_0(A_486, B_485)))), inference(resolution, [status(thm)], [c_26, c_4147])).
% 6.25/2.25  tff(c_4175, plain, (![C_484, A_13, B_14]: (~r2_hidden(C_484, k4_xboole_0(A_13, B_14)) | ~r2_hidden(C_484, k3_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_4164])).
% 6.25/2.25  tff(c_4889, plain, (![A_573, A_574, B_575]: (r2_hidden(A_573, A_574) | ~r2_hidden(A_573, k3_xboole_0(A_574, B_575)))), inference(resolution, [status(thm)], [c_4845, c_4175])).
% 6.25/2.25  tff(c_4934, plain, (![A_576, A_577, B_578]: (r2_hidden(A_576, A_577) | ~r2_hidden(A_576, k3_xboole_0(B_578, A_577)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4889])).
% 6.25/2.25  tff(c_4973, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_4803, c_4934])).
% 6.25/2.25  tff(c_4980, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_4973, c_28])).
% 6.25/2.25  tff(c_4984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3953, c_4980])).
% 6.25/2.25  tff(c_4985, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_3955])).
% 6.25/2.25  tff(c_5358, plain, (![A_629, C_630, B_631]: (r2_hidden(A_629, C_630) | ~r2_hidden(A_629, B_631) | r2_hidden(A_629, k5_xboole_0(B_631, C_630)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.25/2.25  tff(c_5741, plain, (![A_680, A_681, B_682]: (r2_hidden(A_680, k3_xboole_0(A_681, B_682)) | ~r2_hidden(A_680, A_681) | r2_hidden(A_680, k4_xboole_0(A_681, B_682)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_5358])).
% 6.25/2.25  tff(c_4986, plain, ('#skF_7'!='#skF_9'), inference(splitRight, [status(thm)], [c_3955])).
% 6.25/2.25  tff(c_52, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6'))) | '#skF_7'='#skF_9' | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.25/2.25  tff(c_5052, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6'))) | '#skF_7'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_3952, c_52])).
% 6.25/2.25  tff(c_5053, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_4986, c_5052])).
% 6.25/2.25  tff(c_5761, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6'))) | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_5741, c_5053])).
% 6.25/2.25  tff(c_5778, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_4985, c_5761])).
% 6.25/2.25  tff(c_5204, plain, (![A_612, B_613, C_614]: (r2_hidden(A_612, B_613) | ~r2_hidden(A_612, C_614) | r2_hidden(A_612, k5_xboole_0(B_613, C_614)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.25/2.25  tff(c_6160, plain, (![A_708, A_709, B_710]: (r2_hidden(A_708, A_709) | ~r2_hidden(A_708, k3_xboole_0(A_709, B_710)) | r2_hidden(A_708, k4_xboole_0(A_709, B_710)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_5204])).
% 6.25/2.25  tff(c_5003, plain, (![A_581, B_582]: (k4_xboole_0(A_581, k4_xboole_0(A_581, B_582))=k3_xboole_0(A_581, B_582))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.25/2.25  tff(c_5012, plain, (![A_581, B_582]: (r1_xboole_0(k3_xboole_0(A_581, B_582), k4_xboole_0(A_581, B_582)))), inference(superposition, [status(thm), theory('equality')], [c_5003, c_26])).
% 6.25/2.25  tff(c_5088, plain, (![A_593, B_594, C_595]: (~r1_xboole_0(A_593, B_594) | ~r2_hidden(C_595, B_594) | ~r2_hidden(C_595, A_593))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.25/2.25  tff(c_5096, plain, (![C_595, A_581, B_582]: (~r2_hidden(C_595, k4_xboole_0(A_581, B_582)) | ~r2_hidden(C_595, k3_xboole_0(A_581, B_582)))), inference(resolution, [status(thm)], [c_5012, c_5088])).
% 6.25/2.25  tff(c_6213, plain, (![A_711, A_712, B_713]: (r2_hidden(A_711, A_712) | ~r2_hidden(A_711, k3_xboole_0(A_712, B_713)))), inference(resolution, [status(thm)], [c_6160, c_5096])).
% 6.25/2.25  tff(c_6253, plain, (![A_714, A_715, B_716]: (r2_hidden(A_714, A_715) | ~r2_hidden(A_714, k3_xboole_0(B_716, A_715)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_6213])).
% 6.25/2.25  tff(c_6287, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_5778, c_6253])).
% 6.25/2.25  tff(c_6298, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_6287, c_28])).
% 6.25/2.25  tff(c_6304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3953, c_6298])).
% 6.25/2.25  tff(c_6305, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_3951])).
% 6.25/2.25  tff(c_6306, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_3951])).
% 6.25/2.25  tff(c_6307, plain, ('#skF_6'!='#skF_4'), inference(splitLeft, [status(thm)], [c_60])).
% 6.25/2.25  tff(c_6318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6306, c_6307])).
% 6.25/2.25  tff(c_6319, plain, (r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_60])).
% 6.25/2.25  tff(c_6331, plain, (r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_6305, c_6319])).
% 6.25/2.25  tff(c_6443, plain, (![A_734, B_735, C_736]: (~r1_xboole_0(A_734, B_735) | ~r2_hidden(C_736, B_735) | ~r2_hidden(C_736, A_734))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.25/2.25  tff(c_6453, plain, (![C_737, B_738, A_739]: (~r2_hidden(C_737, B_738) | ~r2_hidden(C_737, k4_xboole_0(A_739, B_738)))), inference(resolution, [status(thm)], [c_26, c_6443])).
% 6.25/2.25  tff(c_6467, plain, (~r2_hidden('#skF_9', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_6331, c_6453])).
% 6.25/2.25  tff(c_6473, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_6467])).
% 6.25/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.25/2.25  
% 6.25/2.25  Inference rules
% 6.25/2.25  ----------------------
% 6.25/2.25  #Ref     : 0
% 6.25/2.25  #Sup     : 1561
% 6.25/2.25  #Fact    : 0
% 6.25/2.25  #Define  : 0
% 6.25/2.25  #Split   : 8
% 6.25/2.25  #Chain   : 0
% 6.25/2.25  #Close   : 0
% 6.25/2.25  
% 6.25/2.25  Ordering : KBO
% 6.25/2.25  
% 6.25/2.25  Simplification rules
% 6.25/2.25  ----------------------
% 6.25/2.25  #Subsume      : 116
% 6.25/2.25  #Demod        : 527
% 6.25/2.25  #Tautology    : 503
% 6.25/2.25  #SimpNegUnit  : 11
% 6.25/2.25  #BackRed      : 3
% 6.25/2.25  
% 6.25/2.25  #Partial instantiations: 0
% 6.25/2.25  #Strategies tried      : 1
% 6.25/2.25  
% 6.25/2.25  Timing (in seconds)
% 6.25/2.25  ----------------------
% 6.25/2.25  Preprocessing        : 0.33
% 6.25/2.25  Parsing              : 0.17
% 6.25/2.25  CNF conversion       : 0.02
% 6.25/2.25  Main loop            : 1.16
% 6.25/2.25  Inferencing          : 0.39
% 6.25/2.25  Reduction            : 0.43
% 6.25/2.25  Demodulation         : 0.33
% 6.25/2.25  BG Simplification    : 0.05
% 6.25/2.26  Subsumption          : 0.21
% 6.25/2.26  Abstraction          : 0.06
% 6.25/2.26  MUC search           : 0.00
% 6.25/2.26  Cooper               : 0.00
% 6.25/2.26  Total                : 1.53
% 6.25/2.26  Index Insertion      : 0.00
% 6.25/2.26  Index Deletion       : 0.00
% 6.25/2.26  Index Matching       : 0.00
% 6.25/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
