%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:00 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 187 expanded)
%              Number of leaves         :   29 (  74 expanded)
%              Depth                    :    7
%              Number of atoms          :  126 ( 319 expanded)
%              Number of equality atoms :   34 ( 113 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_6 > #skF_3 > #skF_5

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_89,axiom,(
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

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,k1_ordinal1(B))
      <=> ( r2_hidden(A,B)
          | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(c_38,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_128,plain,(
    ! [D_55,B_56] : r2_hidden(D_55,k2_tarski(D_55,B_56)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_131,plain,(
    ! [A_13] : r2_hidden(A_13,k1_tarski(A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_128])).

tff(c_106,plain,(
    ! [A_53] : k2_xboole_0(A_53,k1_tarski(A_53)) = k1_ordinal1(A_53) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_517,plain,(
    ! [D_284,B_285,A_286] :
      ( ~ r2_hidden(D_284,B_285)
      | r2_hidden(D_284,k2_xboole_0(A_286,B_285)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_521,plain,(
    ! [D_287,A_288] :
      ( ~ r2_hidden(D_287,k1_tarski(A_288))
      | r2_hidden(D_287,k1_ordinal1(A_288)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_517])).

tff(c_525,plain,(
    ! [A_13] : r2_hidden(A_13,k1_ordinal1(A_13)) ),
    inference(resolution,[status(thm)],[c_131,c_521])).

tff(c_426,plain,(
    ! [D_258,B_259,A_260] :
      ( ~ r2_hidden(D_258,B_259)
      | r2_hidden(D_258,k2_xboole_0(A_260,B_259)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_441,plain,(
    ! [D_266,A_267] :
      ( ~ r2_hidden(D_266,k1_tarski(A_267))
      | r2_hidden(D_266,k1_ordinal1(A_267)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_426])).

tff(c_445,plain,(
    ! [A_13] : r2_hidden(A_13,k1_ordinal1(A_13)) ),
    inference(resolution,[status(thm)],[c_131,c_441])).

tff(c_112,plain,
    ( ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8'))
    | ~ r2_hidden('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_148,plain,(
    ~ r2_hidden('#skF_9','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_108,plain,
    ( ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8'))
    | '#skF_10' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_138,plain,(
    '#skF_10' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_158,plain,(
    ! [D_63,B_64,A_65] :
      ( ~ r2_hidden(D_63,B_64)
      | r2_hidden(D_63,k2_xboole_0(A_65,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_172,plain,(
    ! [D_71,A_72] :
      ( ~ r2_hidden(D_71,k1_tarski(A_72))
      | r2_hidden(D_71,k1_ordinal1(A_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_158])).

tff(c_176,plain,(
    ! [A_13] : r2_hidden(A_13,k1_ordinal1(A_13)) ),
    inference(resolution,[status(thm)],[c_131,c_172])).

tff(c_162,plain,(
    ! [D_66,A_67,B_68] :
      ( ~ r2_hidden(D_66,A_67)
      | r2_hidden(D_66,k2_xboole_0(A_67,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_165,plain,(
    ! [D_66,A_53] :
      ( ~ r2_hidden(D_66,A_53)
      | r2_hidden(D_66,k1_ordinal1(A_53)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_162])).

tff(c_116,plain,
    ( ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8'))
    | r2_hidden('#skF_9',k1_ordinal1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_167,plain,(
    ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_171,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_165,c_167])).

tff(c_118,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_7','#skF_8')
    | r2_hidden('#skF_9',k1_ordinal1('#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_177,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_9',k1_ordinal1('#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_118])).

tff(c_178,plain,(
    r2_hidden('#skF_9',k1_ordinal1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_216,plain,(
    ! [D_138,B_139,A_140] :
      ( r2_hidden(D_138,B_139)
      | r2_hidden(D_138,A_140)
      | ~ r2_hidden(D_138,k2_xboole_0(A_140,B_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_247,plain,(
    ! [D_158,A_159] :
      ( r2_hidden(D_158,k1_tarski(A_159))
      | r2_hidden(D_158,A_159)
      | ~ r2_hidden(D_158,k1_ordinal1(A_159)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_216])).

tff(c_180,plain,(
    ! [D_74,B_75,A_76] :
      ( D_74 = B_75
      | D_74 = A_76
      | ~ r2_hidden(D_74,k2_tarski(A_76,B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_189,plain,(
    ! [D_74,A_13] :
      ( D_74 = A_13
      | D_74 = A_13
      | ~ r2_hidden(D_74,k1_tarski(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_180])).

tff(c_256,plain,(
    ! [D_160,A_161] :
      ( D_160 = A_161
      | r2_hidden(D_160,A_161)
      | ~ r2_hidden(D_160,k1_ordinal1(A_161)) ) ),
    inference(resolution,[status(thm)],[c_247,c_189])).

tff(c_262,plain,
    ( '#skF_10' = '#skF_9'
    | r2_hidden('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_178,c_256])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_138,c_262])).

tff(c_272,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_275,plain,(
    ~ r2_hidden('#skF_8',k1_ordinal1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_167])).

tff(c_290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_275])).

tff(c_291,plain,(
    r2_hidden('#skF_9',k1_ordinal1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_338,plain,(
    ! [D_177,B_178,A_179] :
      ( r2_hidden(D_177,B_178)
      | r2_hidden(D_177,A_179)
      | ~ r2_hidden(D_177,k2_xboole_0(A_179,B_178)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_358,plain,(
    ! [D_244,A_245] :
      ( r2_hidden(D_244,k1_tarski(A_245))
      | r2_hidden(D_244,A_245)
      | ~ r2_hidden(D_244,k1_ordinal1(A_245)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_338])).

tff(c_308,plain,(
    ! [D_168,B_169,A_170] :
      ( D_168 = B_169
      | D_168 = A_170
      | ~ r2_hidden(D_168,k2_tarski(A_170,B_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_317,plain,(
    ! [D_168,A_13] :
      ( D_168 = A_13
      | D_168 = A_13
      | ~ r2_hidden(D_168,k1_tarski(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_308])).

tff(c_367,plain,(
    ! [D_246,A_247] :
      ( D_246 = A_247
      | r2_hidden(D_246,A_247)
      | ~ r2_hidden(D_246,k1_ordinal1(A_247)) ) ),
    inference(resolution,[status(thm)],[c_358,c_317])).

tff(c_376,plain,
    ( '#skF_10' = '#skF_9'
    | r2_hidden('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_291,c_367])).

tff(c_386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_138,c_376])).

tff(c_388,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_114,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_399,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_114])).

tff(c_400,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_399])).

tff(c_406,plain,(
    ! [D_253,A_254,B_255] :
      ( ~ r2_hidden(D_253,A_254)
      | r2_hidden(D_253,k2_xboole_0(A_254,B_255)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_410,plain,(
    ! [D_256,A_257] :
      ( ~ r2_hidden(D_256,A_257)
      | r2_hidden(D_256,k1_ordinal1(A_257)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_406])).

tff(c_387,plain,(
    ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_413,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_410,c_387])).

tff(c_417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_413])).

tff(c_418,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_399])).

tff(c_420,plain,(
    ~ r2_hidden('#skF_8',k1_ordinal1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_387])).

tff(c_448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_420])).

tff(c_450,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_110,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_7','#skF_8')
    | '#skF_10' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_475,plain,
    ( '#skF_7' = '#skF_8'
    | r2_hidden('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_110])).

tff(c_476,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_475])).

tff(c_483,plain,(
    ! [D_274,A_275,B_276] :
      ( ~ r2_hidden(D_274,A_275)
      | r2_hidden(D_274,k2_xboole_0(A_275,B_276)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_488,plain,(
    ! [D_277,A_278] :
      ( ~ r2_hidden(D_277,A_278)
      | r2_hidden(D_277,k1_ordinal1(A_278)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_483])).

tff(c_449,plain,(
    ~ r2_hidden('#skF_7',k1_ordinal1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_491,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_488,c_449])).

tff(c_495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_491])).

tff(c_496,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_475])).

tff(c_498,plain,(
    ~ r2_hidden('#skF_8',k1_ordinal1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_449])).

tff(c_528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_498])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:18:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.44  
% 3.17/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.45  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_6 > #skF_3 > #skF_5
% 3.17/1.45  
% 3.17/1.45  %Foreground sorts:
% 3.17/1.45  
% 3.17/1.45  
% 3.17/1.45  %Background operators:
% 3.17/1.45  
% 3.17/1.45  
% 3.17/1.45  %Foreground operators:
% 3.17/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.17/1.45  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.17/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.17/1.45  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.17/1.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.17/1.45  tff('#skF_7', type, '#skF_7': $i).
% 3.17/1.45  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.17/1.45  tff('#skF_10', type, '#skF_10': $i).
% 3.17/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.17/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.17/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.17/1.45  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.17/1.45  tff('#skF_9', type, '#skF_9': $i).
% 3.17/1.45  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.17/1.45  tff('#skF_8', type, '#skF_8': $i).
% 3.17/1.45  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.17/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.17/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.45  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.17/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.17/1.45  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.17/1.45  
% 3.32/1.46  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.32/1.46  tff(f_43, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.32/1.46  tff(f_89, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 3.32/1.46  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.32/1.46  tff(f_96, negated_conjecture, ~(![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 3.32/1.46  tff(c_38, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.32/1.46  tff(c_128, plain, (![D_55, B_56]: (r2_hidden(D_55, k2_tarski(D_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.32/1.46  tff(c_131, plain, (![A_13]: (r2_hidden(A_13, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_128])).
% 3.32/1.46  tff(c_106, plain, (![A_53]: (k2_xboole_0(A_53, k1_tarski(A_53))=k1_ordinal1(A_53))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.32/1.46  tff(c_517, plain, (![D_284, B_285, A_286]: (~r2_hidden(D_284, B_285) | r2_hidden(D_284, k2_xboole_0(A_286, B_285)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.32/1.46  tff(c_521, plain, (![D_287, A_288]: (~r2_hidden(D_287, k1_tarski(A_288)) | r2_hidden(D_287, k1_ordinal1(A_288)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_517])).
% 3.32/1.46  tff(c_525, plain, (![A_13]: (r2_hidden(A_13, k1_ordinal1(A_13)))), inference(resolution, [status(thm)], [c_131, c_521])).
% 3.32/1.46  tff(c_426, plain, (![D_258, B_259, A_260]: (~r2_hidden(D_258, B_259) | r2_hidden(D_258, k2_xboole_0(A_260, B_259)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.32/1.46  tff(c_441, plain, (![D_266, A_267]: (~r2_hidden(D_266, k1_tarski(A_267)) | r2_hidden(D_266, k1_ordinal1(A_267)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_426])).
% 3.32/1.46  tff(c_445, plain, (![A_13]: (r2_hidden(A_13, k1_ordinal1(A_13)))), inference(resolution, [status(thm)], [c_131, c_441])).
% 3.32/1.46  tff(c_112, plain, (~r2_hidden('#skF_7', k1_ordinal1('#skF_8')) | ~r2_hidden('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.32/1.46  tff(c_148, plain, (~r2_hidden('#skF_9', '#skF_10')), inference(splitLeft, [status(thm)], [c_112])).
% 3.32/1.46  tff(c_108, plain, (~r2_hidden('#skF_7', k1_ordinal1('#skF_8')) | '#skF_10'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.32/1.46  tff(c_138, plain, ('#skF_10'!='#skF_9'), inference(splitLeft, [status(thm)], [c_108])).
% 3.32/1.46  tff(c_158, plain, (![D_63, B_64, A_65]: (~r2_hidden(D_63, B_64) | r2_hidden(D_63, k2_xboole_0(A_65, B_64)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.32/1.46  tff(c_172, plain, (![D_71, A_72]: (~r2_hidden(D_71, k1_tarski(A_72)) | r2_hidden(D_71, k1_ordinal1(A_72)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_158])).
% 3.32/1.46  tff(c_176, plain, (![A_13]: (r2_hidden(A_13, k1_ordinal1(A_13)))), inference(resolution, [status(thm)], [c_131, c_172])).
% 3.32/1.46  tff(c_162, plain, (![D_66, A_67, B_68]: (~r2_hidden(D_66, A_67) | r2_hidden(D_66, k2_xboole_0(A_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.32/1.46  tff(c_165, plain, (![D_66, A_53]: (~r2_hidden(D_66, A_53) | r2_hidden(D_66, k1_ordinal1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_162])).
% 3.32/1.46  tff(c_116, plain, (~r2_hidden('#skF_7', k1_ordinal1('#skF_8')) | r2_hidden('#skF_9', k1_ordinal1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.32/1.46  tff(c_167, plain, (~r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(splitLeft, [status(thm)], [c_116])).
% 3.32/1.46  tff(c_171, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_165, c_167])).
% 3.32/1.46  tff(c_118, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_7', '#skF_8') | r2_hidden('#skF_9', k1_ordinal1('#skF_10'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.32/1.46  tff(c_177, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_9', k1_ordinal1('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_171, c_118])).
% 3.32/1.46  tff(c_178, plain, (r2_hidden('#skF_9', k1_ordinal1('#skF_10'))), inference(splitLeft, [status(thm)], [c_177])).
% 3.32/1.46  tff(c_216, plain, (![D_138, B_139, A_140]: (r2_hidden(D_138, B_139) | r2_hidden(D_138, A_140) | ~r2_hidden(D_138, k2_xboole_0(A_140, B_139)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.32/1.46  tff(c_247, plain, (![D_158, A_159]: (r2_hidden(D_158, k1_tarski(A_159)) | r2_hidden(D_158, A_159) | ~r2_hidden(D_158, k1_ordinal1(A_159)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_216])).
% 3.32/1.46  tff(c_180, plain, (![D_74, B_75, A_76]: (D_74=B_75 | D_74=A_76 | ~r2_hidden(D_74, k2_tarski(A_76, B_75)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.32/1.46  tff(c_189, plain, (![D_74, A_13]: (D_74=A_13 | D_74=A_13 | ~r2_hidden(D_74, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_180])).
% 3.32/1.46  tff(c_256, plain, (![D_160, A_161]: (D_160=A_161 | r2_hidden(D_160, A_161) | ~r2_hidden(D_160, k1_ordinal1(A_161)))), inference(resolution, [status(thm)], [c_247, c_189])).
% 3.32/1.46  tff(c_262, plain, ('#skF_10'='#skF_9' | r2_hidden('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_178, c_256])).
% 3.32/1.46  tff(c_271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_138, c_262])).
% 3.32/1.46  tff(c_272, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_177])).
% 3.32/1.46  tff(c_275, plain, (~r2_hidden('#skF_8', k1_ordinal1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_167])).
% 3.32/1.46  tff(c_290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_176, c_275])).
% 3.32/1.46  tff(c_291, plain, (r2_hidden('#skF_9', k1_ordinal1('#skF_10'))), inference(splitRight, [status(thm)], [c_116])).
% 3.32/1.46  tff(c_338, plain, (![D_177, B_178, A_179]: (r2_hidden(D_177, B_178) | r2_hidden(D_177, A_179) | ~r2_hidden(D_177, k2_xboole_0(A_179, B_178)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.32/1.46  tff(c_358, plain, (![D_244, A_245]: (r2_hidden(D_244, k1_tarski(A_245)) | r2_hidden(D_244, A_245) | ~r2_hidden(D_244, k1_ordinal1(A_245)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_338])).
% 3.32/1.46  tff(c_308, plain, (![D_168, B_169, A_170]: (D_168=B_169 | D_168=A_170 | ~r2_hidden(D_168, k2_tarski(A_170, B_169)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.32/1.46  tff(c_317, plain, (![D_168, A_13]: (D_168=A_13 | D_168=A_13 | ~r2_hidden(D_168, k1_tarski(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_308])).
% 3.32/1.46  tff(c_367, plain, (![D_246, A_247]: (D_246=A_247 | r2_hidden(D_246, A_247) | ~r2_hidden(D_246, k1_ordinal1(A_247)))), inference(resolution, [status(thm)], [c_358, c_317])).
% 3.32/1.46  tff(c_376, plain, ('#skF_10'='#skF_9' | r2_hidden('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_291, c_367])).
% 3.32/1.46  tff(c_386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_138, c_376])).
% 3.32/1.46  tff(c_388, plain, (r2_hidden('#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_112])).
% 3.32/1.46  tff(c_114, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_7', '#skF_8') | ~r2_hidden('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.32/1.46  tff(c_399, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_388, c_114])).
% 3.32/1.46  tff(c_400, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_399])).
% 3.32/1.46  tff(c_406, plain, (![D_253, A_254, B_255]: (~r2_hidden(D_253, A_254) | r2_hidden(D_253, k2_xboole_0(A_254, B_255)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.32/1.46  tff(c_410, plain, (![D_256, A_257]: (~r2_hidden(D_256, A_257) | r2_hidden(D_256, k1_ordinal1(A_257)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_406])).
% 3.32/1.46  tff(c_387, plain, (~r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(splitRight, [status(thm)], [c_112])).
% 3.32/1.46  tff(c_413, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_410, c_387])).
% 3.32/1.46  tff(c_417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_400, c_413])).
% 3.32/1.46  tff(c_418, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_399])).
% 3.32/1.46  tff(c_420, plain, (~r2_hidden('#skF_8', k1_ordinal1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_387])).
% 3.32/1.46  tff(c_448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_445, c_420])).
% 3.32/1.46  tff(c_450, plain, ('#skF_10'='#skF_9'), inference(splitRight, [status(thm)], [c_108])).
% 3.32/1.46  tff(c_110, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_7', '#skF_8') | '#skF_10'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.32/1.46  tff(c_475, plain, ('#skF_7'='#skF_8' | r2_hidden('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_450, c_110])).
% 3.32/1.46  tff(c_476, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_475])).
% 3.32/1.46  tff(c_483, plain, (![D_274, A_275, B_276]: (~r2_hidden(D_274, A_275) | r2_hidden(D_274, k2_xboole_0(A_275, B_276)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.32/1.46  tff(c_488, plain, (![D_277, A_278]: (~r2_hidden(D_277, A_278) | r2_hidden(D_277, k1_ordinal1(A_278)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_483])).
% 3.32/1.46  tff(c_449, plain, (~r2_hidden('#skF_7', k1_ordinal1('#skF_8'))), inference(splitRight, [status(thm)], [c_108])).
% 3.32/1.46  tff(c_491, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_488, c_449])).
% 3.32/1.46  tff(c_495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_476, c_491])).
% 3.32/1.46  tff(c_496, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_475])).
% 3.32/1.46  tff(c_498, plain, (~r2_hidden('#skF_8', k1_ordinal1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_496, c_449])).
% 3.32/1.46  tff(c_528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_525, c_498])).
% 3.32/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.46  
% 3.32/1.46  Inference rules
% 3.32/1.46  ----------------------
% 3.32/1.46  #Ref     : 0
% 3.32/1.46  #Sup     : 78
% 3.32/1.46  #Fact    : 0
% 3.32/1.46  #Define  : 0
% 3.32/1.46  #Split   : 8
% 3.32/1.46  #Chain   : 0
% 3.32/1.46  #Close   : 0
% 3.32/1.46  
% 3.32/1.46  Ordering : KBO
% 3.32/1.46  
% 3.32/1.46  Simplification rules
% 3.32/1.46  ----------------------
% 3.32/1.46  #Subsume      : 11
% 3.32/1.46  #Demod        : 28
% 3.32/1.46  #Tautology    : 50
% 3.32/1.46  #SimpNegUnit  : 5
% 3.32/1.46  #BackRed      : 7
% 3.32/1.46  
% 3.32/1.46  #Partial instantiations: 0
% 3.32/1.46  #Strategies tried      : 1
% 3.32/1.46  
% 3.32/1.46  Timing (in seconds)
% 3.32/1.46  ----------------------
% 3.32/1.47  Preprocessing        : 0.37
% 3.32/1.47  Parsing              : 0.16
% 3.32/1.47  CNF conversion       : 0.03
% 3.32/1.47  Main loop            : 0.33
% 3.32/1.47  Inferencing          : 0.10
% 3.32/1.47  Reduction            : 0.09
% 3.32/1.47  Demodulation         : 0.07
% 3.32/1.47  BG Simplification    : 0.03
% 3.32/1.47  Subsumption          : 0.09
% 3.32/1.47  Abstraction          : 0.02
% 3.32/1.47  MUC search           : 0.00
% 3.32/1.47  Cooper               : 0.00
% 3.32/1.47  Total                : 0.73
% 3.32/1.47  Index Insertion      : 0.00
% 3.32/1.47  Index Deletion       : 0.00
% 3.32/1.47  Index Matching       : 0.00
% 3.32/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
