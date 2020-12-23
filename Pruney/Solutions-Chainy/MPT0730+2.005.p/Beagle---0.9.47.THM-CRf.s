%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:00 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 203 expanded)
%              Number of leaves         :   31 (  80 expanded)
%              Depth                    :    7
%              Number of atoms          :  150 ( 349 expanded)
%              Number of equality atoms :   50 ( 138 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_6 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_97,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,k1_ordinal1(B))
      <=> ( r2_hidden(A,B)
          | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(c_44,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_755,plain,(
    ! [A_342,B_343] : k1_enumset1(A_342,A_342,B_343) = k2_tarski(A_342,B_343) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [E_13,A_7,C_9] : r2_hidden(E_13,k1_enumset1(A_7,E_13,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_773,plain,(
    ! [A_344,B_345] : r2_hidden(A_344,k2_tarski(A_344,B_345)) ),
    inference(superposition,[status(thm),theory(equality)],[c_755,c_24])).

tff(c_776,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_773])).

tff(c_114,plain,(
    ! [A_56] : k2_xboole_0(A_56,k1_tarski(A_56)) = k1_ordinal1(A_56) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_815,plain,(
    ! [D_352,B_353,A_354] :
      ( ~ r2_hidden(D_352,B_353)
      | r2_hidden(D_352,k2_xboole_0(A_354,B_353)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_835,plain,(
    ! [D_360,A_361] :
      ( ~ r2_hidden(D_360,k1_tarski(A_361))
      | r2_hidden(D_360,k1_ordinal1(A_361)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_815])).

tff(c_839,plain,(
    ! [A_14] : r2_hidden(A_14,k1_ordinal1(A_14)) ),
    inference(resolution,[status(thm)],[c_776,c_835])).

tff(c_551,plain,(
    ! [A_287,B_288] : k1_enumset1(A_287,A_287,B_288) = k2_tarski(A_287,B_288) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [E_13,B_8,C_9] : r2_hidden(E_13,k1_enumset1(E_13,B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_576,plain,(
    ! [A_292,B_293] : r2_hidden(A_292,k2_tarski(A_292,B_293)) ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_26])).

tff(c_579,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_576])).

tff(c_569,plain,(
    ! [D_289,B_290,A_291] :
      ( ~ r2_hidden(D_289,B_290)
      | r2_hidden(D_289,k2_xboole_0(A_291,B_290)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_633,plain,(
    ! [D_309,A_310] :
      ( ~ r2_hidden(D_309,k1_tarski(A_310))
      | r2_hidden(D_309,k1_ordinal1(A_310)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_569])).

tff(c_637,plain,(
    ! [A_14] : r2_hidden(A_14,k1_ordinal1(A_14)) ),
    inference(resolution,[status(thm)],[c_579,c_633])).

tff(c_120,plain,
    ( ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8'))
    | ~ r2_hidden('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_149,plain,(
    ~ r2_hidden('#skF_9','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_116,plain,
    ( ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8'))
    | '#skF_10' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_136,plain,(
    '#skF_10' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_179,plain,(
    ! [A_71,B_72] : k1_enumset1(A_71,A_71,B_72) = k2_tarski(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_197,plain,(
    ! [A_73,B_74] : r2_hidden(A_73,k2_tarski(A_73,B_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_26])).

tff(c_200,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_197])).

tff(c_202,plain,(
    ! [D_76,B_77,A_78] :
      ( ~ r2_hidden(D_76,B_77)
      | r2_hidden(D_76,k2_xboole_0(A_78,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_228,plain,(
    ! [D_86,A_87] :
      ( ~ r2_hidden(D_86,k1_tarski(A_87))
      | r2_hidden(D_86,k1_ordinal1(A_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_202])).

tff(c_232,plain,(
    ! [A_14] : r2_hidden(A_14,k1_ordinal1(A_14)) ),
    inference(resolution,[status(thm)],[c_200,c_228])).

tff(c_216,plain,(
    ! [D_81,A_82,B_83] :
      ( ~ r2_hidden(D_81,A_82)
      | r2_hidden(D_81,k2_xboole_0(A_82,B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_223,plain,(
    ! [D_84,A_85] :
      ( ~ r2_hidden(D_84,A_85)
      | r2_hidden(D_84,k1_ordinal1(A_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_216])).

tff(c_124,plain,
    ( ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8'))
    | r2_hidden('#skF_9',k1_ordinal1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_215,plain,(
    ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_227,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_223,c_215])).

tff(c_126,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_7','#skF_8')
    | r2_hidden('#skF_9',k1_ordinal1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_233,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_9',k1_ordinal1('#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_126])).

tff(c_234,plain,(
    r2_hidden('#skF_9',k1_ordinal1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_233])).

tff(c_249,plain,(
    ! [D_94,B_95,A_96] :
      ( r2_hidden(D_94,B_95)
      | r2_hidden(D_94,A_96)
      | ~ r2_hidden(D_94,k2_xboole_0(A_96,B_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_261,plain,(
    ! [D_94,A_56] :
      ( r2_hidden(D_94,k1_tarski(A_56))
      | r2_hidden(D_94,A_56)
      | ~ r2_hidden(D_94,k1_ordinal1(A_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_249])).

tff(c_46,plain,(
    ! [A_15,B_16] : k1_enumset1(A_15,A_15,B_16) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_294,plain,(
    ! [E_169,C_170,B_171,A_172] :
      ( E_169 = C_170
      | E_169 = B_171
      | E_169 = A_172
      | ~ r2_hidden(E_169,k1_enumset1(A_172,B_171,C_170)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_313,plain,(
    ! [E_173,B_174,A_175] :
      ( E_173 = B_174
      | E_173 = A_175
      | E_173 = A_175
      | ~ r2_hidden(E_173,k2_tarski(A_175,B_174)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_294])).

tff(c_336,plain,(
    ! [E_181,A_182] :
      ( E_181 = A_182
      | E_181 = A_182
      | E_181 = A_182
      | ~ r2_hidden(E_181,k1_tarski(A_182)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_313])).

tff(c_346,plain,(
    ! [D_183,A_184] :
      ( D_183 = A_184
      | r2_hidden(D_183,A_184)
      | ~ r2_hidden(D_183,k1_ordinal1(A_184)) ) ),
    inference(resolution,[status(thm)],[c_261,c_336])).

tff(c_352,plain,
    ( '#skF_10' = '#skF_9'
    | r2_hidden('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_234,c_346])).

tff(c_361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_136,c_352])).

tff(c_362,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_233])).

tff(c_365,plain,(
    ~ r2_hidden('#skF_8',k1_ordinal1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_215])).

tff(c_380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_365])).

tff(c_381,plain,(
    r2_hidden('#skF_9',k1_ordinal1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_411,plain,(
    ! [D_198,B_199,A_200] :
      ( r2_hidden(D_198,B_199)
      | r2_hidden(D_198,A_200)
      | ~ r2_hidden(D_198,k2_xboole_0(A_200,B_199)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_423,plain,(
    ! [D_198,A_56] :
      ( r2_hidden(D_198,k1_tarski(A_56))
      | r2_hidden(D_198,A_56)
      | ~ r2_hidden(D_198,k1_ordinal1(A_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_411])).

tff(c_456,plain,(
    ! [E_273,C_274,B_275,A_276] :
      ( E_273 = C_274
      | E_273 = B_275
      | E_273 = A_276
      | ~ r2_hidden(E_273,k1_enumset1(A_276,B_275,C_274)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_475,plain,(
    ! [E_277,B_278,A_279] :
      ( E_277 = B_278
      | E_277 = A_279
      | E_277 = A_279
      | ~ r2_hidden(E_277,k2_tarski(A_279,B_278)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_456])).

tff(c_489,plain,(
    ! [E_280,A_281] :
      ( E_280 = A_281
      | E_280 = A_281
      | E_280 = A_281
      | ~ r2_hidden(E_280,k1_tarski(A_281)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_475])).

tff(c_499,plain,(
    ! [D_282,A_283] :
      ( D_282 = A_283
      | r2_hidden(D_282,A_283)
      | ~ r2_hidden(D_282,k1_ordinal1(A_283)) ) ),
    inference(resolution,[status(thm)],[c_423,c_489])).

tff(c_511,plain,
    ( '#skF_10' = '#skF_9'
    | r2_hidden('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_381,c_499])).

tff(c_519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_136,c_511])).

tff(c_521,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_122,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_583,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_122])).

tff(c_584,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_583])).

tff(c_590,plain,(
    ! [D_297,A_298,B_299] :
      ( ~ r2_hidden(D_297,A_298)
      | r2_hidden(D_297,k2_xboole_0(A_298,B_299)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_597,plain,(
    ! [D_300,A_301] :
      ( ~ r2_hidden(D_300,A_301)
      | r2_hidden(D_300,k1_ordinal1(A_301)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_590])).

tff(c_520,plain,(
    ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_600,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_597,c_520])).

tff(c_604,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_600])).

tff(c_605,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_583])).

tff(c_607,plain,(
    ~ r2_hidden('#skF_8',k1_ordinal1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_520])).

tff(c_640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_637,c_607])).

tff(c_642,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_118,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_7','#skF_8')
    | '#skF_10' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_659,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_642,c_118])).

tff(c_660,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_659])).

tff(c_730,plain,(
    ! [D_334,A_335,B_336] :
      ( ~ r2_hidden(D_334,A_335)
      | r2_hidden(D_334,k2_xboole_0(A_335,B_336)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_737,plain,(
    ! [D_337,A_338] :
      ( ~ r2_hidden(D_337,A_338)
      | r2_hidden(D_337,k1_ordinal1(A_338)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_730])).

tff(c_641,plain,(
    ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_740,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_737,c_641])).

tff(c_744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_660,c_740])).

tff(c_745,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_659])).

tff(c_747,plain,(
    ~ r2_hidden('#skF_8',k1_ordinal1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_641])).

tff(c_842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_747])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:11:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.50  
% 3.37/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.51  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_1 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_6 > #skF_5 > #skF_3
% 3.37/1.51  
% 3.37/1.51  %Foreground sorts:
% 3.37/1.51  
% 3.37/1.51  
% 3.37/1.51  %Background operators:
% 3.37/1.51  
% 3.37/1.51  
% 3.37/1.51  %Foreground operators:
% 3.37/1.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.37/1.51  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.37/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.37/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.37/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.37/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.37/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.37/1.51  tff('#skF_10', type, '#skF_10': $i).
% 3.37/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.37/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.37/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.37/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.51  tff('#skF_9', type, '#skF_9': $i).
% 3.37/1.51  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.37/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.51  tff('#skF_8', type, '#skF_8': $i).
% 3.37/1.51  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.37/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.51  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.37/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.37/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.51  
% 3.37/1.52  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.37/1.52  tff(f_53, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.37/1.52  tff(f_49, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.37/1.52  tff(f_97, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 3.37/1.52  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.37/1.52  tff(f_104, negated_conjecture, ~(![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 3.37/1.52  tff(c_44, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.37/1.52  tff(c_755, plain, (![A_342, B_343]: (k1_enumset1(A_342, A_342, B_343)=k2_tarski(A_342, B_343))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.37/1.52  tff(c_24, plain, (![E_13, A_7, C_9]: (r2_hidden(E_13, k1_enumset1(A_7, E_13, C_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.37/1.52  tff(c_773, plain, (![A_344, B_345]: (r2_hidden(A_344, k2_tarski(A_344, B_345)))), inference(superposition, [status(thm), theory('equality')], [c_755, c_24])).
% 3.37/1.52  tff(c_776, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_773])).
% 3.37/1.52  tff(c_114, plain, (![A_56]: (k2_xboole_0(A_56, k1_tarski(A_56))=k1_ordinal1(A_56))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.37/1.52  tff(c_815, plain, (![D_352, B_353, A_354]: (~r2_hidden(D_352, B_353) | r2_hidden(D_352, k2_xboole_0(A_354, B_353)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.37/1.52  tff(c_835, plain, (![D_360, A_361]: (~r2_hidden(D_360, k1_tarski(A_361)) | r2_hidden(D_360, k1_ordinal1(A_361)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_815])).
% 3.37/1.52  tff(c_839, plain, (![A_14]: (r2_hidden(A_14, k1_ordinal1(A_14)))), inference(resolution, [status(thm)], [c_776, c_835])).
% 3.37/1.52  tff(c_551, plain, (![A_287, B_288]: (k1_enumset1(A_287, A_287, B_288)=k2_tarski(A_287, B_288))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.37/1.52  tff(c_26, plain, (![E_13, B_8, C_9]: (r2_hidden(E_13, k1_enumset1(E_13, B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.37/1.52  tff(c_576, plain, (![A_292, B_293]: (r2_hidden(A_292, k2_tarski(A_292, B_293)))), inference(superposition, [status(thm), theory('equality')], [c_551, c_26])).
% 3.37/1.52  tff(c_579, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_576])).
% 3.37/1.52  tff(c_569, plain, (![D_289, B_290, A_291]: (~r2_hidden(D_289, B_290) | r2_hidden(D_289, k2_xboole_0(A_291, B_290)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.37/1.52  tff(c_633, plain, (![D_309, A_310]: (~r2_hidden(D_309, k1_tarski(A_310)) | r2_hidden(D_309, k1_ordinal1(A_310)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_569])).
% 3.37/1.52  tff(c_637, plain, (![A_14]: (r2_hidden(A_14, k1_ordinal1(A_14)))), inference(resolution, [status(thm)], [c_579, c_633])).
% 3.37/1.52  tff(c_120, plain, (~r2_hidden('#skF_7', k1_ordinal1('#skF_8')) | ~r2_hidden('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.37/1.52  tff(c_149, plain, (~r2_hidden('#skF_9', '#skF_10')), inference(splitLeft, [status(thm)], [c_120])).
% 3.37/1.52  tff(c_116, plain, (~r2_hidden('#skF_7', k1_ordinal1('#skF_8')) | '#skF_10'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.37/1.52  tff(c_136, plain, ('#skF_10'!='#skF_9'), inference(splitLeft, [status(thm)], [c_116])).
% 3.37/1.52  tff(c_179, plain, (![A_71, B_72]: (k1_enumset1(A_71, A_71, B_72)=k2_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.37/1.52  tff(c_197, plain, (![A_73, B_74]: (r2_hidden(A_73, k2_tarski(A_73, B_74)))), inference(superposition, [status(thm), theory('equality')], [c_179, c_26])).
% 3.37/1.52  tff(c_200, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_197])).
% 3.37/1.52  tff(c_202, plain, (![D_76, B_77, A_78]: (~r2_hidden(D_76, B_77) | r2_hidden(D_76, k2_xboole_0(A_78, B_77)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.37/1.52  tff(c_228, plain, (![D_86, A_87]: (~r2_hidden(D_86, k1_tarski(A_87)) | r2_hidden(D_86, k1_ordinal1(A_87)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_202])).
% 3.37/1.52  tff(c_232, plain, (![A_14]: (r2_hidden(A_14, k1_ordinal1(A_14)))), inference(resolution, [status(thm)], [c_200, c_228])).
% 3.37/1.52  tff(c_216, plain, (![D_81, A_82, B_83]: (~r2_hidden(D_81, A_82) | r2_hidden(D_81, k2_xboole_0(A_82, B_83)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.37/1.52  tff(c_223, plain, (![D_84, A_85]: (~r2_hidden(D_84, A_85) | r2_hidden(D_84, k1_ordinal1(A_85)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_216])).
% 3.37/1.52  tff(c_124, plain, (~r2_hidden('#skF_7', k1_ordinal1('#skF_8')) | r2_hidden('#skF_9', k1_ordinal1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.37/1.52  tff(c_215, plain, (~r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(splitLeft, [status(thm)], [c_124])).
% 3.37/1.52  tff(c_227, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_223, c_215])).
% 3.37/1.52  tff(c_126, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_7', '#skF_8') | r2_hidden('#skF_9', k1_ordinal1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.37/1.52  tff(c_233, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_9', k1_ordinal1('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_227, c_126])).
% 3.37/1.52  tff(c_234, plain, (r2_hidden('#skF_9', k1_ordinal1('#skF_10'))), inference(splitLeft, [status(thm)], [c_233])).
% 3.37/1.52  tff(c_249, plain, (![D_94, B_95, A_96]: (r2_hidden(D_94, B_95) | r2_hidden(D_94, A_96) | ~r2_hidden(D_94, k2_xboole_0(A_96, B_95)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.37/1.52  tff(c_261, plain, (![D_94, A_56]: (r2_hidden(D_94, k1_tarski(A_56)) | r2_hidden(D_94, A_56) | ~r2_hidden(D_94, k1_ordinal1(A_56)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_249])).
% 3.37/1.52  tff(c_46, plain, (![A_15, B_16]: (k1_enumset1(A_15, A_15, B_16)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.37/1.52  tff(c_294, plain, (![E_169, C_170, B_171, A_172]: (E_169=C_170 | E_169=B_171 | E_169=A_172 | ~r2_hidden(E_169, k1_enumset1(A_172, B_171, C_170)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.37/1.52  tff(c_313, plain, (![E_173, B_174, A_175]: (E_173=B_174 | E_173=A_175 | E_173=A_175 | ~r2_hidden(E_173, k2_tarski(A_175, B_174)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_294])).
% 3.37/1.52  tff(c_336, plain, (![E_181, A_182]: (E_181=A_182 | E_181=A_182 | E_181=A_182 | ~r2_hidden(E_181, k1_tarski(A_182)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_313])).
% 3.37/1.52  tff(c_346, plain, (![D_183, A_184]: (D_183=A_184 | r2_hidden(D_183, A_184) | ~r2_hidden(D_183, k1_ordinal1(A_184)))), inference(resolution, [status(thm)], [c_261, c_336])).
% 3.37/1.52  tff(c_352, plain, ('#skF_10'='#skF_9' | r2_hidden('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_234, c_346])).
% 3.37/1.52  tff(c_361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_136, c_352])).
% 3.37/1.52  tff(c_362, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_233])).
% 3.37/1.52  tff(c_365, plain, (~r2_hidden('#skF_8', k1_ordinal1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_362, c_215])).
% 3.37/1.52  tff(c_380, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_365])).
% 3.37/1.52  tff(c_381, plain, (r2_hidden('#skF_9', k1_ordinal1('#skF_10'))), inference(splitRight, [status(thm)], [c_124])).
% 3.37/1.52  tff(c_411, plain, (![D_198, B_199, A_200]: (r2_hidden(D_198, B_199) | r2_hidden(D_198, A_200) | ~r2_hidden(D_198, k2_xboole_0(A_200, B_199)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.37/1.52  tff(c_423, plain, (![D_198, A_56]: (r2_hidden(D_198, k1_tarski(A_56)) | r2_hidden(D_198, A_56) | ~r2_hidden(D_198, k1_ordinal1(A_56)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_411])).
% 3.37/1.52  tff(c_456, plain, (![E_273, C_274, B_275, A_276]: (E_273=C_274 | E_273=B_275 | E_273=A_276 | ~r2_hidden(E_273, k1_enumset1(A_276, B_275, C_274)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.37/1.52  tff(c_475, plain, (![E_277, B_278, A_279]: (E_277=B_278 | E_277=A_279 | E_277=A_279 | ~r2_hidden(E_277, k2_tarski(A_279, B_278)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_456])).
% 3.37/1.52  tff(c_489, plain, (![E_280, A_281]: (E_280=A_281 | E_280=A_281 | E_280=A_281 | ~r2_hidden(E_280, k1_tarski(A_281)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_475])).
% 3.37/1.52  tff(c_499, plain, (![D_282, A_283]: (D_282=A_283 | r2_hidden(D_282, A_283) | ~r2_hidden(D_282, k1_ordinal1(A_283)))), inference(resolution, [status(thm)], [c_423, c_489])).
% 3.37/1.52  tff(c_511, plain, ('#skF_10'='#skF_9' | r2_hidden('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_381, c_499])).
% 3.37/1.52  tff(c_519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_136, c_511])).
% 3.37/1.52  tff(c_521, plain, (r2_hidden('#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_120])).
% 3.37/1.52  tff(c_122, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.37/1.52  tff(c_583, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_521, c_122])).
% 3.37/1.52  tff(c_584, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_583])).
% 3.37/1.52  tff(c_590, plain, (![D_297, A_298, B_299]: (~r2_hidden(D_297, A_298) | r2_hidden(D_297, k2_xboole_0(A_298, B_299)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.37/1.52  tff(c_597, plain, (![D_300, A_301]: (~r2_hidden(D_300, A_301) | r2_hidden(D_300, k1_ordinal1(A_301)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_590])).
% 3.37/1.52  tff(c_520, plain, (~r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(splitRight, [status(thm)], [c_120])).
% 3.37/1.52  tff(c_600, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_597, c_520])).
% 3.37/1.52  tff(c_604, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_584, c_600])).
% 3.37/1.52  tff(c_605, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_583])).
% 3.37/1.52  tff(c_607, plain, (~r2_hidden('#skF_8', k1_ordinal1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_605, c_520])).
% 3.37/1.52  tff(c_640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_637, c_607])).
% 3.37/1.52  tff(c_642, plain, ('#skF_10'='#skF_9'), inference(splitRight, [status(thm)], [c_116])).
% 3.37/1.52  tff(c_118, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_7', '#skF_8') | '#skF_10'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.37/1.52  tff(c_659, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_642, c_118])).
% 3.37/1.52  tff(c_660, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_659])).
% 3.37/1.52  tff(c_730, plain, (![D_334, A_335, B_336]: (~r2_hidden(D_334, A_335) | r2_hidden(D_334, k2_xboole_0(A_335, B_336)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.37/1.52  tff(c_737, plain, (![D_337, A_338]: (~r2_hidden(D_337, A_338) | r2_hidden(D_337, k1_ordinal1(A_338)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_730])).
% 3.37/1.52  tff(c_641, plain, (~r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(splitRight, [status(thm)], [c_116])).
% 3.37/1.52  tff(c_740, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_737, c_641])).
% 3.37/1.52  tff(c_744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_660, c_740])).
% 3.37/1.52  tff(c_745, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_659])).
% 3.37/1.52  tff(c_747, plain, (~r2_hidden('#skF_8', k1_ordinal1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_745, c_641])).
% 3.37/1.52  tff(c_842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_839, c_747])).
% 3.37/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.52  
% 3.37/1.52  Inference rules
% 3.37/1.52  ----------------------
% 3.37/1.52  #Ref     : 0
% 3.37/1.52  #Sup     : 153
% 3.37/1.52  #Fact    : 0
% 3.37/1.52  #Define  : 0
% 3.37/1.52  #Split   : 6
% 3.37/1.52  #Chain   : 0
% 3.37/1.52  #Close   : 0
% 3.37/1.52  
% 3.37/1.52  Ordering : KBO
% 3.37/1.52  
% 3.37/1.52  Simplification rules
% 3.37/1.52  ----------------------
% 3.37/1.52  #Subsume      : 18
% 3.37/1.52  #Demod        : 37
% 3.37/1.52  #Tautology    : 92
% 3.37/1.52  #SimpNegUnit  : 5
% 3.37/1.52  #BackRed      : 7
% 3.37/1.52  
% 3.37/1.52  #Partial instantiations: 0
% 3.37/1.52  #Strategies tried      : 1
% 3.37/1.52  
% 3.37/1.52  Timing (in seconds)
% 3.37/1.52  ----------------------
% 3.37/1.53  Preprocessing        : 0.36
% 3.37/1.53  Parsing              : 0.17
% 3.37/1.53  CNF conversion       : 0.03
% 3.37/1.53  Main loop            : 0.39
% 3.37/1.53  Inferencing          : 0.13
% 3.37/1.53  Reduction            : 0.11
% 3.37/1.53  Demodulation         : 0.08
% 3.37/1.53  BG Simplification    : 0.03
% 3.37/1.53  Subsumption          : 0.10
% 3.37/1.53  Abstraction          : 0.02
% 3.37/1.53  MUC search           : 0.00
% 3.37/1.53  Cooper               : 0.00
% 3.37/1.53  Total                : 0.79
% 3.37/1.53  Index Insertion      : 0.00
% 3.37/1.53  Index Deletion       : 0.00
% 3.37/1.53  Index Matching       : 0.00
% 3.37/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
