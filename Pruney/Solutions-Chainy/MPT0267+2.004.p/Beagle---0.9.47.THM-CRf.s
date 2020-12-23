%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:32 EST 2020

% Result     : Theorem 5.73s
% Output     : CNFRefutation 5.84s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 282 expanded)
%              Number of leaves         :   33 ( 103 expanded)
%              Depth                    :   12
%              Number of atoms          :  203 ( 521 expanded)
%              Number of equality atoms :   31 ( 148 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
      <=> ( r2_hidden(A,B)
          & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_30,plain,(
    ! [C_21] : r2_hidden(C_21,k1_tarski(C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_62,plain,
    ( '#skF_6' != '#skF_4'
    | r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_167,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_233,plain,(
    r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_125,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k3_xboole_0(A_60,B_61)) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_137,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_125])).

tff(c_26,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_263,plain,(
    ! [A_76,B_77,C_78] :
      ( ~ r1_xboole_0(A_76,B_77)
      | ~ r2_hidden(C_78,B_77)
      | ~ r2_hidden(C_78,A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_282,plain,(
    ! [C_82,B_83,A_84] :
      ( ~ r2_hidden(C_82,B_83)
      | ~ r2_hidden(C_82,k4_xboole_0(A_84,B_83)) ) ),
    inference(resolution,[status(thm)],[c_26,c_263])).

tff(c_352,plain,(
    ! [C_95,B_96,A_97] :
      ( ~ r2_hidden(C_95,k3_xboole_0(B_96,A_97))
      | ~ r2_hidden(C_95,k4_xboole_0(A_97,B_96)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_282])).

tff(c_355,plain,(
    ~ r2_hidden('#skF_7',k3_xboole_0(k1_tarski('#skF_9'),'#skF_8')) ),
    inference(resolution,[status(thm)],[c_233,c_352])).

tff(c_371,plain,(
    ~ r2_hidden('#skF_7',k3_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_355])).

tff(c_56,plain,
    ( '#skF_6' != '#skF_4'
    | '#skF_7' = '#skF_9'
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_124,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_22,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_446,plain,(
    ! [A_114,B_115,C_116] :
      ( r2_hidden(A_114,B_115)
      | r2_hidden(A_114,C_116)
      | ~ r2_hidden(A_114,k5_xboole_0(B_115,C_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1095,plain,(
    ! [A_194,A_195,B_196] :
      ( r2_hidden(A_194,A_195)
      | r2_hidden(A_194,k3_xboole_0(A_195,B_196))
      | ~ r2_hidden(A_194,k4_xboole_0(A_195,B_196)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_446])).

tff(c_1109,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | r2_hidden('#skF_7',k3_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(resolution,[status(thm)],[c_233,c_1095])).

tff(c_1130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_371,c_124,c_1109])).

tff(c_1131,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1342,plain,(
    ! [A_237,C_238,B_239] :
      ( r2_hidden(A_237,C_238)
      | ~ r2_hidden(A_237,B_239)
      | r2_hidden(A_237,k5_xboole_0(B_239,C_238)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1994,plain,(
    ! [A_320,A_321,B_322] :
      ( r2_hidden(A_320,k3_xboole_0(A_321,B_322))
      | ~ r2_hidden(A_320,A_321)
      | r2_hidden(A_320,k4_xboole_0(A_321,B_322)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1342])).

tff(c_1132,plain,(
    ~ r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_60,plain,
    ( ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1239,plain,(
    ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1132,c_60])).

tff(c_2023,plain,
    ( r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_1994,c_1239])).

tff(c_2043,plain,(
    r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1131,c_2023])).

tff(c_1264,plain,(
    ! [A_219,B_220,C_221] :
      ( r2_hidden(A_219,B_220)
      | ~ r2_hidden(A_219,C_221)
      | r2_hidden(A_219,k5_xboole_0(B_220,C_221)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1888,plain,(
    ! [A_311,A_312,B_313] :
      ( r2_hidden(A_311,A_312)
      | ~ r2_hidden(A_311,k3_xboole_0(A_312,B_313))
      | r2_hidden(A_311,k4_xboole_0(A_312,B_313)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1264])).

tff(c_131,plain,(
    ! [A_60,B_61] : r1_xboole_0(k4_xboole_0(A_60,B_61),k3_xboole_0(A_60,B_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_26])).

tff(c_1162,plain,(
    ! [A_199,B_200,C_201] :
      ( ~ r1_xboole_0(A_199,B_200)
      | ~ r2_hidden(C_201,B_200)
      | ~ r2_hidden(C_201,A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1170,plain,(
    ! [C_201,A_60,B_61] :
      ( ~ r2_hidden(C_201,k3_xboole_0(A_60,B_61))
      | ~ r2_hidden(C_201,k4_xboole_0(A_60,B_61)) ) ),
    inference(resolution,[status(thm)],[c_131,c_1162])).

tff(c_1940,plain,(
    ! [A_314,A_315,B_316] :
      ( r2_hidden(A_314,A_315)
      | ~ r2_hidden(A_314,k3_xboole_0(A_315,B_316)) ) ),
    inference(resolution,[status(thm)],[c_1888,c_1170])).

tff(c_1959,plain,(
    ! [A_314,A_1,B_2] :
      ( r2_hidden(A_314,A_1)
      | ~ r2_hidden(A_314,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1940])).

tff(c_2054,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_2043,c_1959])).

tff(c_28,plain,(
    ! [C_21,A_17] :
      ( C_21 = A_17
      | ~ r2_hidden(C_21,k1_tarski(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2067,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2054,c_28])).

tff(c_2074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_2067])).

tff(c_2075,plain,(
    r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2187,plain,(
    ! [A_336,B_337,C_338] :
      ( ~ r1_xboole_0(A_336,B_337)
      | ~ r2_hidden(C_338,B_337)
      | ~ r2_hidden(C_338,A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2274,plain,(
    ! [C_353,A_354,B_355] :
      ( ~ r2_hidden(C_353,k3_xboole_0(A_354,B_355))
      | ~ r2_hidden(C_353,k4_xboole_0(A_354,B_355)) ) ),
    inference(resolution,[status(thm)],[c_131,c_2187])).

tff(c_2294,plain,(
    ~ r2_hidden('#skF_7',k3_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(resolution,[status(thm)],[c_2075,c_2274])).

tff(c_2326,plain,(
    ! [A_362,B_363,C_364] :
      ( r2_hidden(A_362,B_363)
      | r2_hidden(A_362,C_364)
      | ~ r2_hidden(A_362,k5_xboole_0(B_363,C_364)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2743,plain,(
    ! [A_427,A_428,B_429] :
      ( r2_hidden(A_427,A_428)
      | r2_hidden(A_427,k3_xboole_0(A_428,B_429))
      | ~ r2_hidden(A_427,k4_xboole_0(A_428,B_429)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2326])).

tff(c_2765,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | r2_hidden('#skF_7',k3_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(resolution,[status(thm)],[c_2075,c_2743])).

tff(c_2776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2294,c_124,c_2765])).

tff(c_2777,plain,
    ( '#skF_6' != '#skF_4'
    | '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2779,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2777])).

tff(c_2778,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_58,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | '#skF_7' = '#skF_9'
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2781,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | '#skF_7' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2778,c_58])).

tff(c_2782,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_2781])).

tff(c_2935,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2782,c_64])).

tff(c_2936,plain,(
    r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_2935])).

tff(c_2925,plain,(
    ! [A_446,B_447,C_448] :
      ( ~ r1_xboole_0(A_446,B_447)
      | ~ r2_hidden(C_448,B_447)
      | ~ r2_hidden(C_448,A_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2937,plain,(
    ! [C_449,B_450,A_451] :
      ( ~ r2_hidden(C_449,B_450)
      | ~ r2_hidden(C_449,k4_xboole_0(A_451,B_450)) ) ),
    inference(resolution,[status(thm)],[c_26,c_2925])).

tff(c_2940,plain,(
    ~ r2_hidden('#skF_9',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_2936,c_2937])).

tff(c_2958,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2940])).

tff(c_2959,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_2935])).

tff(c_3084,plain,(
    ! [A_476,C_477,B_478] :
      ( r2_hidden(A_476,C_477)
      | ~ r2_hidden(A_476,B_478)
      | r2_hidden(A_476,k5_xboole_0(B_478,C_477)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3544,plain,(
    ! [A_545,A_546,B_547] :
      ( r2_hidden(A_545,k3_xboole_0(A_546,B_547))
      | ~ r2_hidden(A_545,A_546)
      | r2_hidden(A_545,k4_xboole_0(A_546,B_547)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_3084])).

tff(c_2960,plain,(
    ~ r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_2935])).

tff(c_3043,plain,
    ( ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2782,c_60])).

tff(c_3044,plain,(
    ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2960,c_3043])).

tff(c_3566,plain,
    ( r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_3544,c_3044])).

tff(c_3584,plain,(
    r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2959,c_3566])).

tff(c_3113,plain,(
    ! [A_484,B_485,C_486] :
      ( r2_hidden(A_484,B_485)
      | ~ r2_hidden(A_484,C_486)
      | r2_hidden(A_484,k5_xboole_0(B_485,C_486)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3653,plain,(
    ! [A_555,A_556,B_557] :
      ( r2_hidden(A_555,A_556)
      | ~ r2_hidden(A_555,k3_xboole_0(A_556,B_557))
      | r2_hidden(A_555,k4_xboole_0(A_556,B_557)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_3113])).

tff(c_2788,plain,(
    ! [A_430,B_431] : k4_xboole_0(A_430,k3_xboole_0(A_430,B_431)) = k4_xboole_0(A_430,B_431) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2794,plain,(
    ! [A_430,B_431] : r1_xboole_0(k4_xboole_0(A_430,B_431),k3_xboole_0(A_430,B_431)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2788,c_26])).

tff(c_2933,plain,(
    ! [C_448,A_430,B_431] :
      ( ~ r2_hidden(C_448,k3_xboole_0(A_430,B_431))
      | ~ r2_hidden(C_448,k4_xboole_0(A_430,B_431)) ) ),
    inference(resolution,[status(thm)],[c_2794,c_2925])).

tff(c_3697,plain,(
    ! [A_558,A_559,B_560] :
      ( r2_hidden(A_558,A_559)
      | ~ r2_hidden(A_558,k3_xboole_0(A_559,B_560)) ) ),
    inference(resolution,[status(thm)],[c_3653,c_2933])).

tff(c_3742,plain,(
    ! [A_561,A_562,B_563] :
      ( r2_hidden(A_561,A_562)
      | ~ r2_hidden(A_561,k3_xboole_0(B_563,A_562)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3697])).

tff(c_3781,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_3584,c_3742])).

tff(c_3793,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3781,c_28])).

tff(c_3799,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2779,c_3793])).

tff(c_3800,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_2781])).

tff(c_4120,plain,(
    ! [A_616,C_617,B_618] :
      ( r2_hidden(A_616,C_617)
      | ~ r2_hidden(A_616,B_618)
      | r2_hidden(A_616,k5_xboole_0(B_618,C_617)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4605,plain,(
    ! [A_684,A_685,B_686] :
      ( r2_hidden(A_684,k3_xboole_0(A_685,B_686))
      | ~ r2_hidden(A_684,A_685)
      | r2_hidden(A_684,k4_xboole_0(A_685,B_686)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4120])).

tff(c_3801,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_2781])).

tff(c_54,plain,
    ( ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | '#skF_7' = '#skF_9'
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3984,plain,
    ( ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | '#skF_7' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2778,c_54])).

tff(c_3985,plain,(
    ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_3801,c_3984])).

tff(c_4631,plain,
    ( r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_4605,c_3985])).

tff(c_4647,plain,(
    r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3800,c_4631])).

tff(c_4079,plain,(
    ! [A_606,B_607,C_608] :
      ( r2_hidden(A_606,B_607)
      | ~ r2_hidden(A_606,C_608)
      | r2_hidden(A_606,k5_xboole_0(B_607,C_608)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4828,plain,(
    ! [A_704,A_705,B_706] :
      ( r2_hidden(A_704,A_705)
      | ~ r2_hidden(A_704,k3_xboole_0(A_705,B_706))
      | r2_hidden(A_704,k4_xboole_0(A_705,B_706)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4079])).

tff(c_24,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3939,plain,(
    ! [A_580,B_581,C_582] :
      ( ~ r1_xboole_0(A_580,B_581)
      | ~ r2_hidden(C_582,B_581)
      | ~ r2_hidden(C_582,A_580) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3958,plain,(
    ! [C_586,B_587,A_588] :
      ( ~ r2_hidden(C_586,B_587)
      | ~ r2_hidden(C_586,k4_xboole_0(A_588,B_587)) ) ),
    inference(resolution,[status(thm)],[c_26,c_3939])).

tff(c_3968,plain,(
    ! [C_586,A_13,B_14] :
      ( ~ r2_hidden(C_586,k3_xboole_0(A_13,B_14))
      | ~ r2_hidden(C_586,k4_xboole_0(A_13,B_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3958])).

tff(c_4875,plain,(
    ! [A_707,A_708,B_709] :
      ( r2_hidden(A_707,A_708)
      | ~ r2_hidden(A_707,k3_xboole_0(A_708,B_709)) ) ),
    inference(resolution,[status(thm)],[c_4828,c_3968])).

tff(c_4915,plain,(
    ! [A_710,A_711,B_712] :
      ( r2_hidden(A_710,A_711)
      | ~ r2_hidden(A_710,k3_xboole_0(B_712,A_711)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4875])).

tff(c_4949,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_4647,c_4915])).

tff(c_4963,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4949,c_28])).

tff(c_4970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2779,c_4963])).

tff(c_4971,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_2777])).

tff(c_4972,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2777])).

tff(c_5014,plain,(
    r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4971,c_4972,c_62])).

tff(c_5134,plain,(
    ! [A_732,B_733,C_734] :
      ( ~ r1_xboole_0(A_732,B_733)
      | ~ r2_hidden(C_734,B_733)
      | ~ r2_hidden(C_734,A_732) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_5146,plain,(
    ! [C_735,B_736,A_737] :
      ( ~ r2_hidden(C_735,B_736)
      | ~ r2_hidden(C_735,k4_xboole_0(A_737,B_736)) ) ),
    inference(resolution,[status(thm)],[c_26,c_5134])).

tff(c_5155,plain,(
    ~ r2_hidden('#skF_9',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_5014,c_5146])).

tff(c_5167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_5155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.73/2.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.73/2.12  
% 5.73/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.73/2.13  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 5.73/2.13  
% 5.73/2.13  %Foreground sorts:
% 5.73/2.13  
% 5.73/2.13  
% 5.73/2.13  %Background operators:
% 5.73/2.13  
% 5.73/2.13  
% 5.73/2.13  %Foreground operators:
% 5.73/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.73/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.73/2.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.73/2.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.73/2.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.73/2.13  tff('#skF_7', type, '#skF_7': $i).
% 5.73/2.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.73/2.13  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.73/2.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.73/2.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.73/2.13  tff('#skF_5', type, '#skF_5': $i).
% 5.73/2.13  tff('#skF_6', type, '#skF_6': $i).
% 5.73/2.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.73/2.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.73/2.13  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.73/2.13  tff('#skF_9', type, '#skF_9': $i).
% 5.73/2.13  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.73/2.13  tff('#skF_8', type, '#skF_8': $i).
% 5.73/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.73/2.13  tff('#skF_4', type, '#skF_4': $i).
% 5.73/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.73/2.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.73/2.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.73/2.13  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.73/2.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.73/2.13  
% 5.84/2.15  tff(f_65, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 5.84/2.15  tff(f_87, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 5.84/2.15  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.84/2.15  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.84/2.15  tff(f_58, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.84/2.15  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.84/2.15  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.84/2.15  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 5.84/2.15  tff(c_30, plain, (![C_21]: (r2_hidden(C_21, k1_tarski(C_21)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.84/2.15  tff(c_62, plain, ('#skF_6'!='#skF_4' | r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.84/2.15  tff(c_167, plain, ('#skF_6'!='#skF_4'), inference(splitLeft, [status(thm)], [c_62])).
% 5.84/2.15  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.84/2.15  tff(c_64, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.84/2.15  tff(c_233, plain, (r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitLeft, [status(thm)], [c_64])).
% 5.84/2.15  tff(c_125, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k3_xboole_0(A_60, B_61))=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.84/2.15  tff(c_137, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_125])).
% 5.84/2.15  tff(c_26, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.84/2.15  tff(c_263, plain, (![A_76, B_77, C_78]: (~r1_xboole_0(A_76, B_77) | ~r2_hidden(C_78, B_77) | ~r2_hidden(C_78, A_76))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.84/2.15  tff(c_282, plain, (![C_82, B_83, A_84]: (~r2_hidden(C_82, B_83) | ~r2_hidden(C_82, k4_xboole_0(A_84, B_83)))), inference(resolution, [status(thm)], [c_26, c_263])).
% 5.84/2.15  tff(c_352, plain, (![C_95, B_96, A_97]: (~r2_hidden(C_95, k3_xboole_0(B_96, A_97)) | ~r2_hidden(C_95, k4_xboole_0(A_97, B_96)))), inference(superposition, [status(thm), theory('equality')], [c_137, c_282])).
% 5.84/2.15  tff(c_355, plain, (~r2_hidden('#skF_7', k3_xboole_0(k1_tarski('#skF_9'), '#skF_8'))), inference(resolution, [status(thm)], [c_233, c_352])).
% 5.84/2.15  tff(c_371, plain, (~r2_hidden('#skF_7', k3_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_355])).
% 5.84/2.15  tff(c_56, plain, ('#skF_6'!='#skF_4' | '#skF_7'='#skF_9' | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.84/2.15  tff(c_124, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_56])).
% 5.84/2.15  tff(c_22, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.84/2.15  tff(c_446, plain, (![A_114, B_115, C_116]: (r2_hidden(A_114, B_115) | r2_hidden(A_114, C_116) | ~r2_hidden(A_114, k5_xboole_0(B_115, C_116)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.84/2.15  tff(c_1095, plain, (![A_194, A_195, B_196]: (r2_hidden(A_194, A_195) | r2_hidden(A_194, k3_xboole_0(A_195, B_196)) | ~r2_hidden(A_194, k4_xboole_0(A_195, B_196)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_446])).
% 5.84/2.15  tff(c_1109, plain, (r2_hidden('#skF_7', '#skF_8') | r2_hidden('#skF_7', k3_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(resolution, [status(thm)], [c_233, c_1095])).
% 5.84/2.15  tff(c_1130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_371, c_124, c_1109])).
% 5.84/2.15  tff(c_1131, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_64])).
% 5.84/2.15  tff(c_1342, plain, (![A_237, C_238, B_239]: (r2_hidden(A_237, C_238) | ~r2_hidden(A_237, B_239) | r2_hidden(A_237, k5_xboole_0(B_239, C_238)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.84/2.15  tff(c_1994, plain, (![A_320, A_321, B_322]: (r2_hidden(A_320, k3_xboole_0(A_321, B_322)) | ~r2_hidden(A_320, A_321) | r2_hidden(A_320, k4_xboole_0(A_321, B_322)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1342])).
% 5.84/2.15  tff(c_1132, plain, (~r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_64])).
% 5.84/2.15  tff(c_60, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6'))) | r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.84/2.15  tff(c_1239, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_1132, c_60])).
% 5.84/2.15  tff(c_2023, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6'))) | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_1994, c_1239])).
% 5.84/2.15  tff(c_2043, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_1131, c_2023])).
% 5.84/2.15  tff(c_1264, plain, (![A_219, B_220, C_221]: (r2_hidden(A_219, B_220) | ~r2_hidden(A_219, C_221) | r2_hidden(A_219, k5_xboole_0(B_220, C_221)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.84/2.15  tff(c_1888, plain, (![A_311, A_312, B_313]: (r2_hidden(A_311, A_312) | ~r2_hidden(A_311, k3_xboole_0(A_312, B_313)) | r2_hidden(A_311, k4_xboole_0(A_312, B_313)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1264])).
% 5.84/2.15  tff(c_131, plain, (![A_60, B_61]: (r1_xboole_0(k4_xboole_0(A_60, B_61), k3_xboole_0(A_60, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_125, c_26])).
% 5.84/2.15  tff(c_1162, plain, (![A_199, B_200, C_201]: (~r1_xboole_0(A_199, B_200) | ~r2_hidden(C_201, B_200) | ~r2_hidden(C_201, A_199))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.84/2.15  tff(c_1170, plain, (![C_201, A_60, B_61]: (~r2_hidden(C_201, k3_xboole_0(A_60, B_61)) | ~r2_hidden(C_201, k4_xboole_0(A_60, B_61)))), inference(resolution, [status(thm)], [c_131, c_1162])).
% 5.84/2.15  tff(c_1940, plain, (![A_314, A_315, B_316]: (r2_hidden(A_314, A_315) | ~r2_hidden(A_314, k3_xboole_0(A_315, B_316)))), inference(resolution, [status(thm)], [c_1888, c_1170])).
% 5.84/2.15  tff(c_1959, plain, (![A_314, A_1, B_2]: (r2_hidden(A_314, A_1) | ~r2_hidden(A_314, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1940])).
% 5.84/2.15  tff(c_2054, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_2043, c_1959])).
% 5.84/2.15  tff(c_28, plain, (![C_21, A_17]: (C_21=A_17 | ~r2_hidden(C_21, k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.84/2.15  tff(c_2067, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_2054, c_28])).
% 5.84/2.15  tff(c_2074, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_2067])).
% 5.84/2.15  tff(c_2075, plain, (r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_62])).
% 5.84/2.15  tff(c_2187, plain, (![A_336, B_337, C_338]: (~r1_xboole_0(A_336, B_337) | ~r2_hidden(C_338, B_337) | ~r2_hidden(C_338, A_336))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.84/2.15  tff(c_2274, plain, (![C_353, A_354, B_355]: (~r2_hidden(C_353, k3_xboole_0(A_354, B_355)) | ~r2_hidden(C_353, k4_xboole_0(A_354, B_355)))), inference(resolution, [status(thm)], [c_131, c_2187])).
% 5.84/2.15  tff(c_2294, plain, (~r2_hidden('#skF_7', k3_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(resolution, [status(thm)], [c_2075, c_2274])).
% 5.84/2.15  tff(c_2326, plain, (![A_362, B_363, C_364]: (r2_hidden(A_362, B_363) | r2_hidden(A_362, C_364) | ~r2_hidden(A_362, k5_xboole_0(B_363, C_364)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.84/2.15  tff(c_2743, plain, (![A_427, A_428, B_429]: (r2_hidden(A_427, A_428) | r2_hidden(A_427, k3_xboole_0(A_428, B_429)) | ~r2_hidden(A_427, k4_xboole_0(A_428, B_429)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2326])).
% 5.84/2.15  tff(c_2765, plain, (r2_hidden('#skF_7', '#skF_8') | r2_hidden('#skF_7', k3_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(resolution, [status(thm)], [c_2075, c_2743])).
% 5.84/2.15  tff(c_2776, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2294, c_124, c_2765])).
% 5.84/2.15  tff(c_2777, plain, ('#skF_6'!='#skF_4' | '#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_56])).
% 5.84/2.15  tff(c_2779, plain, ('#skF_6'!='#skF_4'), inference(splitLeft, [status(thm)], [c_2777])).
% 5.84/2.15  tff(c_2778, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_56])).
% 5.84/2.15  tff(c_58, plain, (r2_hidden('#skF_4', '#skF_5') | '#skF_7'='#skF_9' | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.84/2.15  tff(c_2781, plain, (r2_hidden('#skF_4', '#skF_5') | '#skF_7'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2778, c_58])).
% 5.84/2.15  tff(c_2782, plain, ('#skF_7'='#skF_9'), inference(splitLeft, [status(thm)], [c_2781])).
% 5.84/2.15  tff(c_2935, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_2782, c_64])).
% 5.84/2.15  tff(c_2936, plain, (r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitLeft, [status(thm)], [c_2935])).
% 5.84/2.15  tff(c_2925, plain, (![A_446, B_447, C_448]: (~r1_xboole_0(A_446, B_447) | ~r2_hidden(C_448, B_447) | ~r2_hidden(C_448, A_446))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.84/2.15  tff(c_2937, plain, (![C_449, B_450, A_451]: (~r2_hidden(C_449, B_450) | ~r2_hidden(C_449, k4_xboole_0(A_451, B_450)))), inference(resolution, [status(thm)], [c_26, c_2925])).
% 5.84/2.15  tff(c_2940, plain, (~r2_hidden('#skF_9', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_2936, c_2937])).
% 5.84/2.15  tff(c_2958, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_2940])).
% 5.84/2.15  tff(c_2959, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_2935])).
% 5.84/2.15  tff(c_3084, plain, (![A_476, C_477, B_478]: (r2_hidden(A_476, C_477) | ~r2_hidden(A_476, B_478) | r2_hidden(A_476, k5_xboole_0(B_478, C_477)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.84/2.15  tff(c_3544, plain, (![A_545, A_546, B_547]: (r2_hidden(A_545, k3_xboole_0(A_546, B_547)) | ~r2_hidden(A_545, A_546) | r2_hidden(A_545, k4_xboole_0(A_546, B_547)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_3084])).
% 5.84/2.15  tff(c_2960, plain, (~r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_2935])).
% 5.84/2.15  tff(c_3043, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6'))) | r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_2782, c_60])).
% 5.84/2.15  tff(c_3044, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_2960, c_3043])).
% 5.84/2.15  tff(c_3566, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6'))) | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_3544, c_3044])).
% 5.84/2.15  tff(c_3584, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_2959, c_3566])).
% 5.84/2.15  tff(c_3113, plain, (![A_484, B_485, C_486]: (r2_hidden(A_484, B_485) | ~r2_hidden(A_484, C_486) | r2_hidden(A_484, k5_xboole_0(B_485, C_486)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.84/2.15  tff(c_3653, plain, (![A_555, A_556, B_557]: (r2_hidden(A_555, A_556) | ~r2_hidden(A_555, k3_xboole_0(A_556, B_557)) | r2_hidden(A_555, k4_xboole_0(A_556, B_557)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_3113])).
% 5.84/2.15  tff(c_2788, plain, (![A_430, B_431]: (k4_xboole_0(A_430, k3_xboole_0(A_430, B_431))=k4_xboole_0(A_430, B_431))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.84/2.15  tff(c_2794, plain, (![A_430, B_431]: (r1_xboole_0(k4_xboole_0(A_430, B_431), k3_xboole_0(A_430, B_431)))), inference(superposition, [status(thm), theory('equality')], [c_2788, c_26])).
% 5.84/2.15  tff(c_2933, plain, (![C_448, A_430, B_431]: (~r2_hidden(C_448, k3_xboole_0(A_430, B_431)) | ~r2_hidden(C_448, k4_xboole_0(A_430, B_431)))), inference(resolution, [status(thm)], [c_2794, c_2925])).
% 5.84/2.15  tff(c_3697, plain, (![A_558, A_559, B_560]: (r2_hidden(A_558, A_559) | ~r2_hidden(A_558, k3_xboole_0(A_559, B_560)))), inference(resolution, [status(thm)], [c_3653, c_2933])).
% 5.84/2.15  tff(c_3742, plain, (![A_561, A_562, B_563]: (r2_hidden(A_561, A_562) | ~r2_hidden(A_561, k3_xboole_0(B_563, A_562)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3697])).
% 5.84/2.15  tff(c_3781, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_3584, c_3742])).
% 5.84/2.15  tff(c_3793, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_3781, c_28])).
% 5.84/2.15  tff(c_3799, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2779, c_3793])).
% 5.84/2.15  tff(c_3800, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_2781])).
% 5.84/2.15  tff(c_4120, plain, (![A_616, C_617, B_618]: (r2_hidden(A_616, C_617) | ~r2_hidden(A_616, B_618) | r2_hidden(A_616, k5_xboole_0(B_618, C_617)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.84/2.15  tff(c_4605, plain, (![A_684, A_685, B_686]: (r2_hidden(A_684, k3_xboole_0(A_685, B_686)) | ~r2_hidden(A_684, A_685) | r2_hidden(A_684, k4_xboole_0(A_685, B_686)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_4120])).
% 5.84/2.15  tff(c_3801, plain, ('#skF_7'!='#skF_9'), inference(splitRight, [status(thm)], [c_2781])).
% 5.84/2.15  tff(c_54, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6'))) | '#skF_7'='#skF_9' | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.84/2.15  tff(c_3984, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6'))) | '#skF_7'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2778, c_54])).
% 5.84/2.15  tff(c_3985, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_3801, c_3984])).
% 5.84/2.15  tff(c_4631, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6'))) | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_4605, c_3985])).
% 5.84/2.15  tff(c_4647, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_3800, c_4631])).
% 5.84/2.15  tff(c_4079, plain, (![A_606, B_607, C_608]: (r2_hidden(A_606, B_607) | ~r2_hidden(A_606, C_608) | r2_hidden(A_606, k5_xboole_0(B_607, C_608)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.84/2.15  tff(c_4828, plain, (![A_704, A_705, B_706]: (r2_hidden(A_704, A_705) | ~r2_hidden(A_704, k3_xboole_0(A_705, B_706)) | r2_hidden(A_704, k4_xboole_0(A_705, B_706)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_4079])).
% 5.84/2.15  tff(c_24, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.84/2.15  tff(c_3939, plain, (![A_580, B_581, C_582]: (~r1_xboole_0(A_580, B_581) | ~r2_hidden(C_582, B_581) | ~r2_hidden(C_582, A_580))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.84/2.15  tff(c_3958, plain, (![C_586, B_587, A_588]: (~r2_hidden(C_586, B_587) | ~r2_hidden(C_586, k4_xboole_0(A_588, B_587)))), inference(resolution, [status(thm)], [c_26, c_3939])).
% 5.84/2.15  tff(c_3968, plain, (![C_586, A_13, B_14]: (~r2_hidden(C_586, k3_xboole_0(A_13, B_14)) | ~r2_hidden(C_586, k4_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_3958])).
% 5.84/2.15  tff(c_4875, plain, (![A_707, A_708, B_709]: (r2_hidden(A_707, A_708) | ~r2_hidden(A_707, k3_xboole_0(A_708, B_709)))), inference(resolution, [status(thm)], [c_4828, c_3968])).
% 5.84/2.15  tff(c_4915, plain, (![A_710, A_711, B_712]: (r2_hidden(A_710, A_711) | ~r2_hidden(A_710, k3_xboole_0(B_712, A_711)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4875])).
% 5.84/2.15  tff(c_4949, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_4647, c_4915])).
% 5.84/2.15  tff(c_4963, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_4949, c_28])).
% 5.84/2.15  tff(c_4970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2779, c_4963])).
% 5.84/2.15  tff(c_4971, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_2777])).
% 5.84/2.15  tff(c_4972, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_2777])).
% 5.84/2.15  tff(c_5014, plain, (r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_4971, c_4972, c_62])).
% 5.84/2.15  tff(c_5134, plain, (![A_732, B_733, C_734]: (~r1_xboole_0(A_732, B_733) | ~r2_hidden(C_734, B_733) | ~r2_hidden(C_734, A_732))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.84/2.15  tff(c_5146, plain, (![C_735, B_736, A_737]: (~r2_hidden(C_735, B_736) | ~r2_hidden(C_735, k4_xboole_0(A_737, B_736)))), inference(resolution, [status(thm)], [c_26, c_5134])).
% 5.84/2.15  tff(c_5155, plain, (~r2_hidden('#skF_9', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_5014, c_5146])).
% 5.84/2.15  tff(c_5167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_5155])).
% 5.84/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.15  
% 5.84/2.15  Inference rules
% 5.84/2.15  ----------------------
% 5.84/2.15  #Ref     : 0
% 5.84/2.15  #Sup     : 1202
% 5.84/2.15  #Fact    : 0
% 5.84/2.15  #Define  : 0
% 5.84/2.15  #Split   : 8
% 5.84/2.15  #Chain   : 0
% 5.84/2.15  #Close   : 0
% 5.84/2.15  
% 5.84/2.15  Ordering : KBO
% 5.84/2.15  
% 5.84/2.15  Simplification rules
% 5.84/2.15  ----------------------
% 5.84/2.15  #Subsume      : 123
% 5.84/2.15  #Demod        : 343
% 5.84/2.15  #Tautology    : 439
% 5.84/2.15  #SimpNegUnit  : 10
% 5.84/2.15  #BackRed      : 2
% 5.84/2.15  
% 5.84/2.15  #Partial instantiations: 0
% 5.84/2.15  #Strategies tried      : 1
% 5.84/2.15  
% 5.84/2.15  Timing (in seconds)
% 5.84/2.15  ----------------------
% 5.84/2.15  Preprocessing        : 0.32
% 5.84/2.15  Parsing              : 0.16
% 5.84/2.15  CNF conversion       : 0.03
% 5.84/2.15  Main loop            : 1.01
% 5.84/2.15  Inferencing          : 0.36
% 5.84/2.15  Reduction            : 0.34
% 5.84/2.15  Demodulation         : 0.26
% 5.84/2.15  BG Simplification    : 0.04
% 5.84/2.15  Subsumption          : 0.19
% 5.84/2.15  Abstraction          : 0.05
% 5.84/2.15  MUC search           : 0.00
% 5.84/2.15  Cooper               : 0.00
% 5.84/2.15  Total                : 1.37
% 5.84/2.15  Index Insertion      : 0.00
% 5.84/2.15  Index Deletion       : 0.00
% 5.84/2.15  Index Matching       : 0.00
% 5.84/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
