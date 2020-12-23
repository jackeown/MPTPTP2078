%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:32 EST 2020

% Result     : Theorem 9.41s
% Output     : CNFRefutation 9.84s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 356 expanded)
%              Number of leaves         :   36 ( 127 expanded)
%              Depth                    :   12
%              Number of atoms          :  243 ( 621 expanded)
%              Number of equality atoms :   46 ( 194 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1

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

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
      <=> ( r2_hidden(A,B)
          & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

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

tff(f_64,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_34,plain,(
    ! [C_25] : r2_hidden(C_25,k1_tarski(C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_60,plain,
    ( '#skF_6' != '#skF_4'
    | '#skF_7' = '#skF_9'
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_145,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_66,plain,
    ( '#skF_6' != '#skF_4'
    | r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_194,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_68,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_391,plain,(
    r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_24,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1350,plain,(
    ! [A_129,B_130,C_131] :
      ( r2_hidden(A_129,B_130)
      | r2_hidden(A_129,C_131)
      | ~ r2_hidden(A_129,k5_xboole_0(B_130,C_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2805,plain,(
    ! [A_205,A_206,B_207] :
      ( r2_hidden(A_205,A_206)
      | r2_hidden(A_205,k3_xboole_0(A_206,B_207))
      | ~ r2_hidden(A_205,k4_xboole_0(A_206,B_207)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1350])).

tff(c_2828,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | r2_hidden('#skF_7',k3_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(resolution,[status(thm)],[c_391,c_2805])).

tff(c_2845,plain,(
    r2_hidden('#skF_7',k3_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_2828])).

tff(c_26,plain,(
    ! [A_15,B_16] : r1_tarski(k3_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_153,plain,(
    ! [A_70,B_71] :
      ( k3_xboole_0(A_70,B_71) = A_70
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_242,plain,(
    ! [A_82,B_83] : k3_xboole_0(k3_xboole_0(A_82,B_83),A_82) = k3_xboole_0(A_82,B_83) ),
    inference(resolution,[status(thm)],[c_26,c_153])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_266,plain,(
    ! [A_82,B_83] : k3_xboole_0(A_82,k3_xboole_0(A_82,B_83)) = k3_xboole_0(A_82,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_2])).

tff(c_22,plain,(
    ! [A_11,B_12] : r1_xboole_0(k3_xboole_0(A_11,B_12),k5_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_310,plain,(
    ! [A_86,B_87,C_88] :
      ( ~ r1_xboole_0(A_86,B_87)
      | ~ r2_hidden(C_88,B_87)
      | ~ r2_hidden(C_88,A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2327,plain,(
    ! [C_185,A_186,B_187] :
      ( ~ r2_hidden(C_185,k5_xboole_0(A_186,B_187))
      | ~ r2_hidden(C_185,k3_xboole_0(A_186,B_187)) ) ),
    inference(resolution,[status(thm)],[c_22,c_310])).

tff(c_2355,plain,(
    ! [C_185,A_13,B_14] :
      ( ~ r2_hidden(C_185,k4_xboole_0(A_13,B_14))
      | ~ r2_hidden(C_185,k3_xboole_0(A_13,k3_xboole_0(A_13,B_14))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2327])).

tff(c_3160,plain,(
    ! [C_221,A_222,B_223] :
      ( ~ r2_hidden(C_221,k4_xboole_0(A_222,B_223))
      | ~ r2_hidden(C_221,k3_xboole_0(A_222,B_223)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_2355])).

tff(c_3199,plain,(
    ~ r2_hidden('#skF_7',k3_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(resolution,[status(thm)],[c_391,c_3160])).

tff(c_3221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2845,c_3199])).

tff(c_3222,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_4173,plain,(
    ! [A_259,C_260,B_261] :
      ( r2_hidden(A_259,C_260)
      | ~ r2_hidden(A_259,B_261)
      | r2_hidden(A_259,k5_xboole_0(B_261,C_260)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_5198,plain,(
    ! [A_317,A_318,B_319] :
      ( r2_hidden(A_317,k3_xboole_0(A_318,B_319))
      | ~ r2_hidden(A_317,A_318)
      | r2_hidden(A_317,k4_xboole_0(A_318,B_319)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4173])).

tff(c_3223,plain,(
    ~ r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_64,plain,
    ( ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3590,plain,(
    ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_3223,c_64])).

tff(c_5205,plain,
    ( r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_5198,c_3590])).

tff(c_5221,plain,(
    r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3222,c_5205])).

tff(c_87,plain,(
    ! [B_62,A_63] : k3_xboole_0(B_62,A_63) = k3_xboole_0(A_63,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_102,plain,(
    ! [B_62,A_63] : r1_tarski(k3_xboole_0(B_62,A_63),A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_26])).

tff(c_3314,plain,(
    ! [B_229,A_230] : k3_xboole_0(k3_xboole_0(B_229,A_230),A_230) = k3_xboole_0(B_229,A_230) ),
    inference(resolution,[status(thm)],[c_102,c_153])).

tff(c_3395,plain,(
    ! [B_2,B_229] : k3_xboole_0(B_2,k3_xboole_0(B_229,B_2)) = k3_xboole_0(B_229,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3314])).

tff(c_4189,plain,(
    ! [A_262,B_263,C_264] :
      ( r2_hidden(A_262,B_263)
      | ~ r2_hidden(A_262,C_264)
      | r2_hidden(A_262,k5_xboole_0(B_263,C_264)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4198,plain,(
    ! [A_262,A_13,B_14] :
      ( r2_hidden(A_262,A_13)
      | ~ r2_hidden(A_262,k3_xboole_0(A_13,B_14))
      | r2_hidden(A_262,k4_xboole_0(A_13,B_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4189])).

tff(c_292,plain,(
    ! [A_1,B_83] : k3_xboole_0(A_1,k3_xboole_0(A_1,B_83)) = k3_xboole_0(A_1,B_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_242])).

tff(c_4988,plain,(
    ! [C_310,A_311,B_312] :
      ( ~ r2_hidden(C_310,k5_xboole_0(A_311,B_312))
      | ~ r2_hidden(C_310,k3_xboole_0(A_311,B_312)) ) ),
    inference(resolution,[status(thm)],[c_22,c_310])).

tff(c_5016,plain,(
    ! [C_310,A_13,B_14] :
      ( ~ r2_hidden(C_310,k4_xboole_0(A_13,B_14))
      | ~ r2_hidden(C_310,k3_xboole_0(A_13,k3_xboole_0(A_13,B_14))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4988])).

tff(c_5919,plain,(
    ! [C_350,A_351,B_352] :
      ( ~ r2_hidden(C_350,k4_xboole_0(A_351,B_352))
      | ~ r2_hidden(C_350,k3_xboole_0(A_351,B_352)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_5016])).

tff(c_6001,plain,(
    ! [A_356,A_357,B_358] :
      ( r2_hidden(A_356,A_357)
      | ~ r2_hidden(A_356,k3_xboole_0(A_357,B_358)) ) ),
    inference(resolution,[status(thm)],[c_4198,c_5919])).

tff(c_6067,plain,(
    ! [A_359,B_360,B_361] :
      ( r2_hidden(A_359,B_360)
      | ~ r2_hidden(A_359,k3_xboole_0(B_361,B_360)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3395,c_6001])).

tff(c_6127,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_5221,c_6067])).

tff(c_32,plain,(
    ! [C_25,A_21] :
      ( C_25 = A_21
      | ~ r2_hidden(C_25,k1_tarski(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6134,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6127,c_32])).

tff(c_6138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_6134])).

tff(c_6139,plain,(
    r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_7326,plain,(
    ! [A_422,B_423,C_424] :
      ( r2_hidden(A_422,B_423)
      | r2_hidden(A_422,C_424)
      | ~ r2_hidden(A_422,k5_xboole_0(B_423,C_424)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8325,plain,(
    ! [A_474,A_475,B_476] :
      ( r2_hidden(A_474,A_475)
      | r2_hidden(A_474,k3_xboole_0(A_475,B_476))
      | ~ r2_hidden(A_474,k4_xboole_0(A_475,B_476)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_7326])).

tff(c_8350,plain,
    ( r2_hidden('#skF_7','#skF_8')
    | r2_hidden('#skF_7',k3_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(resolution,[status(thm)],[c_6139,c_8325])).

tff(c_8359,plain,(
    r2_hidden('#skF_7',k3_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_8350])).

tff(c_6201,plain,(
    ! [A_371,B_372] : k3_xboole_0(k3_xboole_0(A_371,B_372),A_371) = k3_xboole_0(A_371,B_372) ),
    inference(resolution,[status(thm)],[c_26,c_153])).

tff(c_6228,plain,(
    ! [A_371,B_372] : k3_xboole_0(A_371,k3_xboole_0(A_371,B_372)) = k3_xboole_0(A_371,B_372) ),
    inference(superposition,[status(thm),theory(equality)],[c_6201,c_2])).

tff(c_6191,plain,(
    ! [A_368,B_369,C_370] :
      ( ~ r1_xboole_0(A_368,B_369)
      | ~ r2_hidden(C_370,B_369)
      | ~ r2_hidden(C_370,A_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8196,plain,(
    ! [C_469,A_470,B_471] :
      ( ~ r2_hidden(C_469,k5_xboole_0(A_470,B_471))
      | ~ r2_hidden(C_469,k3_xboole_0(A_470,B_471)) ) ),
    inference(resolution,[status(thm)],[c_22,c_6191])).

tff(c_8224,plain,(
    ! [C_469,A_13,B_14] :
      ( ~ r2_hidden(C_469,k4_xboole_0(A_13,B_14))
      | ~ r2_hidden(C_469,k3_xboole_0(A_13,k3_xboole_0(A_13,B_14))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_8196])).

tff(c_9073,plain,(
    ! [C_510,A_511,B_512] :
      ( ~ r2_hidden(C_510,k4_xboole_0(A_511,B_512))
      | ~ r2_hidden(C_510,k3_xboole_0(A_511,B_512)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6228,c_8224])).

tff(c_9112,plain,(
    ~ r2_hidden('#skF_7',k3_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(resolution,[status(thm)],[c_6139,c_9073])).

tff(c_9126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8359,c_9112])).

tff(c_9127,plain,
    ( '#skF_6' != '#skF_4'
    | '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_9129,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_9127])).

tff(c_9128,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_62,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | '#skF_7' = '#skF_9'
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_9180,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | '#skF_7' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9128,c_62])).

tff(c_9181,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_9180])).

tff(c_9187,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9181,c_68])).

tff(c_9188,plain,(
    r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_9187])).

tff(c_30,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_9382,plain,(
    ! [A_540,B_541,C_542] :
      ( ~ r1_xboole_0(A_540,B_541)
      | ~ r2_hidden(C_542,B_541)
      | ~ r2_hidden(C_542,A_540) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_9400,plain,(
    ! [C_543,B_544,A_545] :
      ( ~ r2_hidden(C_543,B_544)
      | ~ r2_hidden(C_543,k4_xboole_0(A_545,B_544)) ) ),
    inference(resolution,[status(thm)],[c_30,c_9382])).

tff(c_9411,plain,(
    ~ r2_hidden('#skF_9',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_9188,c_9400])).

tff(c_9417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_9411])).

tff(c_9418,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_9187])).

tff(c_10599,plain,(
    ! [A_606,C_607,B_608] :
      ( r2_hidden(A_606,C_607)
      | ~ r2_hidden(A_606,B_608)
      | r2_hidden(A_606,k5_xboole_0(B_608,C_607)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_11705,plain,(
    ! [A_663,A_664,B_665] :
      ( r2_hidden(A_663,k3_xboole_0(A_664,B_665))
      | ~ r2_hidden(A_663,A_664)
      | r2_hidden(A_663,k4_xboole_0(A_664,B_665)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_10599])).

tff(c_9419,plain,(
    ~ r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_9187])).

tff(c_9535,plain,
    ( ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9181,c_64])).

tff(c_9536,plain,(
    ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_9419,c_9535])).

tff(c_11718,plain,
    ( r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_11705,c_9536])).

tff(c_11733,plain,(
    r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9418,c_11718])).

tff(c_9131,plain,(
    ! [A_513,B_514] :
      ( k3_xboole_0(A_513,B_514) = A_513
      | ~ r1_tarski(A_513,B_514) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_9843,plain,(
    ! [B_589,A_590] : k3_xboole_0(k3_xboole_0(B_589,A_590),A_590) = k3_xboole_0(B_589,A_590) ),
    inference(resolution,[status(thm)],[c_102,c_9131])).

tff(c_9904,plain,(
    ! [A_590,B_589] : k3_xboole_0(A_590,k3_xboole_0(B_589,A_590)) = k3_xboole_0(B_589,A_590) ),
    inference(superposition,[status(thm),theory(equality)],[c_9843,c_2])).

tff(c_10150,plain,(
    ! [A_595,B_596,C_597] :
      ( r2_hidden(A_595,B_596)
      | ~ r2_hidden(A_595,C_597)
      | r2_hidden(A_595,k5_xboole_0(B_596,C_597)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10162,plain,(
    ! [A_595,A_13,B_14] :
      ( r2_hidden(A_595,A_13)
      | ~ r2_hidden(A_595,k3_xboole_0(A_13,B_14))
      | r2_hidden(A_595,k4_xboole_0(A_13,B_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_10150])).

tff(c_9443,plain,(
    ! [A_553,B_554] : k3_xboole_0(k3_xboole_0(A_553,B_554),A_553) = k3_xboole_0(A_553,B_554) ),
    inference(resolution,[status(thm)],[c_26,c_9131])).

tff(c_9464,plain,(
    ! [A_553,B_554] : k3_xboole_0(A_553,k3_xboole_0(A_553,B_554)) = k3_xboole_0(A_553,B_554) ),
    inference(superposition,[status(thm),theory(equality)],[c_9443,c_2])).

tff(c_9433,plain,(
    ! [A_550,B_551,C_552] :
      ( ~ r1_xboole_0(A_550,B_551)
      | ~ r2_hidden(C_552,B_551)
      | ~ r2_hidden(C_552,A_550) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_11297,plain,(
    ! [C_649,A_650,B_651] :
      ( ~ r2_hidden(C_649,k5_xboole_0(A_650,B_651))
      | ~ r2_hidden(C_649,k3_xboole_0(A_650,B_651)) ) ),
    inference(resolution,[status(thm)],[c_22,c_9433])).

tff(c_11325,plain,(
    ! [C_649,A_13,B_14] :
      ( ~ r2_hidden(C_649,k4_xboole_0(A_13,B_14))
      | ~ r2_hidden(C_649,k3_xboole_0(A_13,k3_xboole_0(A_13,B_14))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_11297])).

tff(c_12430,plain,(
    ! [C_694,A_695,B_696] :
      ( ~ r2_hidden(C_694,k4_xboole_0(A_695,B_696))
      | ~ r2_hidden(C_694,k3_xboole_0(A_695,B_696)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9464,c_11325])).

tff(c_12487,plain,(
    ! [A_697,A_698,B_699] :
      ( r2_hidden(A_697,A_698)
      | ~ r2_hidden(A_697,k3_xboole_0(A_698,B_699)) ) ),
    inference(resolution,[status(thm)],[c_10162,c_12430])).

tff(c_12568,plain,(
    ! [A_700,A_701,B_702] :
      ( r2_hidden(A_700,A_701)
      | ~ r2_hidden(A_700,k3_xboole_0(B_702,A_701)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9904,c_12487])).

tff(c_12643,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_11733,c_12568])).

tff(c_12650,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12643,c_32])).

tff(c_12654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9129,c_12650])).

tff(c_12655,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_9180])).

tff(c_13281,plain,(
    ! [A_740,C_741,B_742] :
      ( r2_hidden(A_740,C_741)
      | ~ r2_hidden(A_740,B_742)
      | r2_hidden(A_740,k5_xboole_0(B_742,C_741)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_15271,plain,(
    ! [A_832,A_833,B_834] :
      ( r2_hidden(A_832,k3_xboole_0(A_833,B_834))
      | ~ r2_hidden(A_832,A_833)
      | r2_hidden(A_832,k4_xboole_0(A_833,B_834)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_13281])).

tff(c_12656,plain,(
    '#skF_7' != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_9180])).

tff(c_58,plain,
    ( ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | '#skF_7' = '#skF_9'
    | ~ r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12856,plain,
    ( ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | '#skF_7' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9128,c_58])).

tff(c_12857,plain,(
    ~ r2_hidden('#skF_4',k4_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_12656,c_12856])).

tff(c_15287,plain,
    ( r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6')))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_15271,c_12857])).

tff(c_15300,plain,(
    r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12655,c_15287])).

tff(c_13152,plain,(
    ! [B_738,A_739] : k3_xboole_0(k3_xboole_0(B_738,A_739),A_739) = k3_xboole_0(B_738,A_739) ),
    inference(resolution,[status(thm)],[c_102,c_9131])).

tff(c_13219,plain,(
    ! [A_739,B_738] : k3_xboole_0(A_739,k3_xboole_0(B_738,A_739)) = k3_xboole_0(B_738,A_739) ),
    inference(superposition,[status(thm),theory(equality)],[c_13152,c_2])).

tff(c_13502,plain,(
    ! [A_750,B_751,C_752] :
      ( r2_hidden(A_750,B_751)
      | ~ r2_hidden(A_750,C_752)
      | r2_hidden(A_750,k5_xboole_0(B_751,C_752)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_13511,plain,(
    ! [A_750,A_13,B_14] :
      ( r2_hidden(A_750,A_13)
      | ~ r2_hidden(A_750,k3_xboole_0(A_13,B_14))
      | r2_hidden(A_750,k4_xboole_0(A_13,B_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_13502])).

tff(c_12705,plain,(
    ! [A_709,B_710] : k3_xboole_0(k3_xboole_0(A_709,B_710),A_709) = k3_xboole_0(A_709,B_710) ),
    inference(resolution,[status(thm)],[c_26,c_9131])).

tff(c_12732,plain,(
    ! [A_709,B_710] : k3_xboole_0(A_709,k3_xboole_0(A_709,B_710)) = k3_xboole_0(A_709,B_710) ),
    inference(superposition,[status(thm),theory(equality)],[c_12705,c_2])).

tff(c_12798,plain,(
    ! [A_715,B_716,C_717] :
      ( ~ r1_xboole_0(A_715,B_716)
      | ~ r2_hidden(C_717,B_716)
      | ~ r2_hidden(C_717,A_715) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14702,plain,(
    ! [C_810,A_811,B_812] :
      ( ~ r2_hidden(C_810,k5_xboole_0(A_811,B_812))
      | ~ r2_hidden(C_810,k3_xboole_0(A_811,B_812)) ) ),
    inference(resolution,[status(thm)],[c_22,c_12798])).

tff(c_14730,plain,(
    ! [C_810,A_13,B_14] :
      ( ~ r2_hidden(C_810,k4_xboole_0(A_13,B_14))
      | ~ r2_hidden(C_810,k3_xboole_0(A_13,k3_xboole_0(A_13,B_14))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_14702])).

tff(c_15616,plain,(
    ! [C_848,A_849,B_850] :
      ( ~ r2_hidden(C_848,k4_xboole_0(A_849,B_850))
      | ~ r2_hidden(C_848,k3_xboole_0(A_849,B_850)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12732,c_14730])).

tff(c_15712,plain,(
    ! [A_854,A_855,B_856] :
      ( r2_hidden(A_854,A_855)
      | ~ r2_hidden(A_854,k3_xboole_0(A_855,B_856)) ) ),
    inference(resolution,[status(thm)],[c_13511,c_15616])).

tff(c_15788,plain,(
    ! [A_857,A_858,B_859] :
      ( r2_hidden(A_857,A_858)
      | ~ r2_hidden(A_857,k3_xboole_0(B_859,A_858)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13219,c_15712])).

tff(c_15858,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_15300,c_15788])).

tff(c_15865,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_15858,c_32])).

tff(c_15869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9129,c_15865])).

tff(c_15870,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_9127])).

tff(c_15871,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9127])).

tff(c_15872,plain,(
    '#skF_6' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_15883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15871,c_15872])).

tff(c_15884,plain,(
    r2_hidden('#skF_7',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_15896,plain,(
    r2_hidden('#skF_9',k4_xboole_0('#skF_8',k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15870,c_15884])).

tff(c_16443,plain,(
    ! [A_893,B_894,C_895] :
      ( ~ r1_xboole_0(A_893,B_894)
      | ~ r2_hidden(C_895,B_894)
      | ~ r2_hidden(C_895,A_893) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16459,plain,(
    ! [C_896,B_897,A_898] :
      ( ~ r2_hidden(C_896,B_897)
      | ~ r2_hidden(C_896,k4_xboole_0(A_898,B_897)) ) ),
    inference(resolution,[status(thm)],[c_30,c_16443])).

tff(c_16470,plain,(
    ~ r2_hidden('#skF_9',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_15896,c_16459])).

tff(c_16476,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16470])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:45:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.41/3.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.41/3.10  
% 9.41/3.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.41/3.11  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 9.41/3.11  
% 9.41/3.11  %Foreground sorts:
% 9.41/3.11  
% 9.41/3.11  
% 9.41/3.11  %Background operators:
% 9.41/3.11  
% 9.41/3.11  
% 9.41/3.11  %Foreground operators:
% 9.41/3.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.41/3.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.41/3.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.41/3.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.41/3.11  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.41/3.11  tff('#skF_7', type, '#skF_7': $i).
% 9.41/3.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.41/3.11  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.41/3.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.41/3.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.41/3.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.41/3.11  tff('#skF_5', type, '#skF_5': $i).
% 9.41/3.11  tff('#skF_6', type, '#skF_6': $i).
% 9.41/3.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.41/3.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.41/3.11  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.41/3.11  tff('#skF_9', type, '#skF_9': $i).
% 9.41/3.11  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 9.41/3.11  tff('#skF_8', type, '#skF_8': $i).
% 9.41/3.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.41/3.11  tff('#skF_4', type, '#skF_4': $i).
% 9.41/3.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.41/3.11  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.41/3.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.41/3.11  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 9.41/3.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.41/3.11  
% 9.84/3.15  tff(f_71, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 9.84/3.15  tff(f_93, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 9.84/3.15  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.84/3.15  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 9.84/3.15  tff(f_58, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 9.84/3.15  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.84/3.15  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.84/3.15  tff(f_54, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 9.84/3.15  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 9.84/3.15  tff(f_64, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 9.84/3.15  tff(c_34, plain, (![C_25]: (r2_hidden(C_25, k1_tarski(C_25)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.84/3.15  tff(c_60, plain, ('#skF_6'!='#skF_4' | '#skF_7'='#skF_9' | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.84/3.15  tff(c_145, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_60])).
% 9.84/3.15  tff(c_66, plain, ('#skF_6'!='#skF_4' | r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.84/3.15  tff(c_194, plain, ('#skF_6'!='#skF_4'), inference(splitLeft, [status(thm)], [c_66])).
% 9.84/3.15  tff(c_68, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.84/3.15  tff(c_391, plain, (r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitLeft, [status(thm)], [c_68])).
% 9.84/3.15  tff(c_24, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.84/3.15  tff(c_1350, plain, (![A_129, B_130, C_131]: (r2_hidden(A_129, B_130) | r2_hidden(A_129, C_131) | ~r2_hidden(A_129, k5_xboole_0(B_130, C_131)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.84/3.15  tff(c_2805, plain, (![A_205, A_206, B_207]: (r2_hidden(A_205, A_206) | r2_hidden(A_205, k3_xboole_0(A_206, B_207)) | ~r2_hidden(A_205, k4_xboole_0(A_206, B_207)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1350])).
% 9.84/3.15  tff(c_2828, plain, (r2_hidden('#skF_7', '#skF_8') | r2_hidden('#skF_7', k3_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(resolution, [status(thm)], [c_391, c_2805])).
% 9.84/3.15  tff(c_2845, plain, (r2_hidden('#skF_7', k3_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_145, c_2828])).
% 9.84/3.15  tff(c_26, plain, (![A_15, B_16]: (r1_tarski(k3_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.84/3.15  tff(c_153, plain, (![A_70, B_71]: (k3_xboole_0(A_70, B_71)=A_70 | ~r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.84/3.15  tff(c_242, plain, (![A_82, B_83]: (k3_xboole_0(k3_xboole_0(A_82, B_83), A_82)=k3_xboole_0(A_82, B_83))), inference(resolution, [status(thm)], [c_26, c_153])).
% 9.84/3.15  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.84/3.15  tff(c_266, plain, (![A_82, B_83]: (k3_xboole_0(A_82, k3_xboole_0(A_82, B_83))=k3_xboole_0(A_82, B_83))), inference(superposition, [status(thm), theory('equality')], [c_242, c_2])).
% 9.84/3.15  tff(c_22, plain, (![A_11, B_12]: (r1_xboole_0(k3_xboole_0(A_11, B_12), k5_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.84/3.15  tff(c_310, plain, (![A_86, B_87, C_88]: (~r1_xboole_0(A_86, B_87) | ~r2_hidden(C_88, B_87) | ~r2_hidden(C_88, A_86))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.84/3.15  tff(c_2327, plain, (![C_185, A_186, B_187]: (~r2_hidden(C_185, k5_xboole_0(A_186, B_187)) | ~r2_hidden(C_185, k3_xboole_0(A_186, B_187)))), inference(resolution, [status(thm)], [c_22, c_310])).
% 9.84/3.15  tff(c_2355, plain, (![C_185, A_13, B_14]: (~r2_hidden(C_185, k4_xboole_0(A_13, B_14)) | ~r2_hidden(C_185, k3_xboole_0(A_13, k3_xboole_0(A_13, B_14))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2327])).
% 9.84/3.15  tff(c_3160, plain, (![C_221, A_222, B_223]: (~r2_hidden(C_221, k4_xboole_0(A_222, B_223)) | ~r2_hidden(C_221, k3_xboole_0(A_222, B_223)))), inference(demodulation, [status(thm), theory('equality')], [c_266, c_2355])).
% 9.84/3.15  tff(c_3199, plain, (~r2_hidden('#skF_7', k3_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(resolution, [status(thm)], [c_391, c_3160])).
% 9.84/3.15  tff(c_3221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2845, c_3199])).
% 9.84/3.15  tff(c_3222, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_68])).
% 9.84/3.15  tff(c_4173, plain, (![A_259, C_260, B_261]: (r2_hidden(A_259, C_260) | ~r2_hidden(A_259, B_261) | r2_hidden(A_259, k5_xboole_0(B_261, C_260)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.84/3.15  tff(c_5198, plain, (![A_317, A_318, B_319]: (r2_hidden(A_317, k3_xboole_0(A_318, B_319)) | ~r2_hidden(A_317, A_318) | r2_hidden(A_317, k4_xboole_0(A_318, B_319)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_4173])).
% 9.84/3.15  tff(c_3223, plain, (~r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_68])).
% 9.84/3.15  tff(c_64, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6'))) | r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.84/3.15  tff(c_3590, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_3223, c_64])).
% 9.84/3.15  tff(c_5205, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6'))) | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_5198, c_3590])).
% 9.84/3.15  tff(c_5221, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_3222, c_5205])).
% 9.84/3.15  tff(c_87, plain, (![B_62, A_63]: (k3_xboole_0(B_62, A_63)=k3_xboole_0(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.84/3.15  tff(c_102, plain, (![B_62, A_63]: (r1_tarski(k3_xboole_0(B_62, A_63), A_63))), inference(superposition, [status(thm), theory('equality')], [c_87, c_26])).
% 9.84/3.15  tff(c_3314, plain, (![B_229, A_230]: (k3_xboole_0(k3_xboole_0(B_229, A_230), A_230)=k3_xboole_0(B_229, A_230))), inference(resolution, [status(thm)], [c_102, c_153])).
% 9.84/3.15  tff(c_3395, plain, (![B_2, B_229]: (k3_xboole_0(B_2, k3_xboole_0(B_229, B_2))=k3_xboole_0(B_229, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3314])).
% 9.84/3.15  tff(c_4189, plain, (![A_262, B_263, C_264]: (r2_hidden(A_262, B_263) | ~r2_hidden(A_262, C_264) | r2_hidden(A_262, k5_xboole_0(B_263, C_264)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.84/3.15  tff(c_4198, plain, (![A_262, A_13, B_14]: (r2_hidden(A_262, A_13) | ~r2_hidden(A_262, k3_xboole_0(A_13, B_14)) | r2_hidden(A_262, k4_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_4189])).
% 9.84/3.15  tff(c_292, plain, (![A_1, B_83]: (k3_xboole_0(A_1, k3_xboole_0(A_1, B_83))=k3_xboole_0(A_1, B_83))), inference(superposition, [status(thm), theory('equality')], [c_2, c_242])).
% 9.84/3.15  tff(c_4988, plain, (![C_310, A_311, B_312]: (~r2_hidden(C_310, k5_xboole_0(A_311, B_312)) | ~r2_hidden(C_310, k3_xboole_0(A_311, B_312)))), inference(resolution, [status(thm)], [c_22, c_310])).
% 9.84/3.15  tff(c_5016, plain, (![C_310, A_13, B_14]: (~r2_hidden(C_310, k4_xboole_0(A_13, B_14)) | ~r2_hidden(C_310, k3_xboole_0(A_13, k3_xboole_0(A_13, B_14))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_4988])).
% 9.84/3.15  tff(c_5919, plain, (![C_350, A_351, B_352]: (~r2_hidden(C_350, k4_xboole_0(A_351, B_352)) | ~r2_hidden(C_350, k3_xboole_0(A_351, B_352)))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_5016])).
% 9.84/3.15  tff(c_6001, plain, (![A_356, A_357, B_358]: (r2_hidden(A_356, A_357) | ~r2_hidden(A_356, k3_xboole_0(A_357, B_358)))), inference(resolution, [status(thm)], [c_4198, c_5919])).
% 9.84/3.15  tff(c_6067, plain, (![A_359, B_360, B_361]: (r2_hidden(A_359, B_360) | ~r2_hidden(A_359, k3_xboole_0(B_361, B_360)))), inference(superposition, [status(thm), theory('equality')], [c_3395, c_6001])).
% 9.84/3.15  tff(c_6127, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_5221, c_6067])).
% 9.84/3.15  tff(c_32, plain, (![C_25, A_21]: (C_25=A_21 | ~r2_hidden(C_25, k1_tarski(A_21)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.84/3.15  tff(c_6134, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_6127, c_32])).
% 9.84/3.15  tff(c_6138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_6134])).
% 9.84/3.15  tff(c_6139, plain, (r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_66])).
% 9.84/3.15  tff(c_7326, plain, (![A_422, B_423, C_424]: (r2_hidden(A_422, B_423) | r2_hidden(A_422, C_424) | ~r2_hidden(A_422, k5_xboole_0(B_423, C_424)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.84/3.15  tff(c_8325, plain, (![A_474, A_475, B_476]: (r2_hidden(A_474, A_475) | r2_hidden(A_474, k3_xboole_0(A_475, B_476)) | ~r2_hidden(A_474, k4_xboole_0(A_475, B_476)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_7326])).
% 9.84/3.15  tff(c_8350, plain, (r2_hidden('#skF_7', '#skF_8') | r2_hidden('#skF_7', k3_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(resolution, [status(thm)], [c_6139, c_8325])).
% 9.84/3.15  tff(c_8359, plain, (r2_hidden('#skF_7', k3_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_145, c_8350])).
% 9.84/3.15  tff(c_6201, plain, (![A_371, B_372]: (k3_xboole_0(k3_xboole_0(A_371, B_372), A_371)=k3_xboole_0(A_371, B_372))), inference(resolution, [status(thm)], [c_26, c_153])).
% 9.84/3.15  tff(c_6228, plain, (![A_371, B_372]: (k3_xboole_0(A_371, k3_xboole_0(A_371, B_372))=k3_xboole_0(A_371, B_372))), inference(superposition, [status(thm), theory('equality')], [c_6201, c_2])).
% 9.84/3.15  tff(c_6191, plain, (![A_368, B_369, C_370]: (~r1_xboole_0(A_368, B_369) | ~r2_hidden(C_370, B_369) | ~r2_hidden(C_370, A_368))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.84/3.15  tff(c_8196, plain, (![C_469, A_470, B_471]: (~r2_hidden(C_469, k5_xboole_0(A_470, B_471)) | ~r2_hidden(C_469, k3_xboole_0(A_470, B_471)))), inference(resolution, [status(thm)], [c_22, c_6191])).
% 9.84/3.15  tff(c_8224, plain, (![C_469, A_13, B_14]: (~r2_hidden(C_469, k4_xboole_0(A_13, B_14)) | ~r2_hidden(C_469, k3_xboole_0(A_13, k3_xboole_0(A_13, B_14))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_8196])).
% 9.84/3.15  tff(c_9073, plain, (![C_510, A_511, B_512]: (~r2_hidden(C_510, k4_xboole_0(A_511, B_512)) | ~r2_hidden(C_510, k3_xboole_0(A_511, B_512)))), inference(demodulation, [status(thm), theory('equality')], [c_6228, c_8224])).
% 9.84/3.15  tff(c_9112, plain, (~r2_hidden('#skF_7', k3_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(resolution, [status(thm)], [c_6139, c_9073])).
% 9.84/3.15  tff(c_9126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8359, c_9112])).
% 9.84/3.15  tff(c_9127, plain, ('#skF_6'!='#skF_4' | '#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_60])).
% 9.84/3.15  tff(c_9129, plain, ('#skF_6'!='#skF_4'), inference(splitLeft, [status(thm)], [c_9127])).
% 9.84/3.15  tff(c_9128, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_60])).
% 9.84/3.15  tff(c_62, plain, (r2_hidden('#skF_4', '#skF_5') | '#skF_7'='#skF_9' | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.84/3.15  tff(c_9180, plain, (r2_hidden('#skF_4', '#skF_5') | '#skF_7'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9128, c_62])).
% 9.84/3.15  tff(c_9181, plain, ('#skF_7'='#skF_9'), inference(splitLeft, [status(thm)], [c_9180])).
% 9.84/3.15  tff(c_9187, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_9181, c_68])).
% 9.84/3.15  tff(c_9188, plain, (r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitLeft, [status(thm)], [c_9187])).
% 9.84/3.15  tff(c_30, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.84/3.15  tff(c_9382, plain, (![A_540, B_541, C_542]: (~r1_xboole_0(A_540, B_541) | ~r2_hidden(C_542, B_541) | ~r2_hidden(C_542, A_540))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.84/3.15  tff(c_9400, plain, (![C_543, B_544, A_545]: (~r2_hidden(C_543, B_544) | ~r2_hidden(C_543, k4_xboole_0(A_545, B_544)))), inference(resolution, [status(thm)], [c_30, c_9382])).
% 9.84/3.15  tff(c_9411, plain, (~r2_hidden('#skF_9', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_9188, c_9400])).
% 9.84/3.15  tff(c_9417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_9411])).
% 9.84/3.15  tff(c_9418, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_9187])).
% 9.84/3.15  tff(c_10599, plain, (![A_606, C_607, B_608]: (r2_hidden(A_606, C_607) | ~r2_hidden(A_606, B_608) | r2_hidden(A_606, k5_xboole_0(B_608, C_607)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.84/3.15  tff(c_11705, plain, (![A_663, A_664, B_665]: (r2_hidden(A_663, k3_xboole_0(A_664, B_665)) | ~r2_hidden(A_663, A_664) | r2_hidden(A_663, k4_xboole_0(A_664, B_665)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_10599])).
% 9.84/3.15  tff(c_9419, plain, (~r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_9187])).
% 9.84/3.15  tff(c_9535, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6'))) | r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_9181, c_64])).
% 9.84/3.15  tff(c_9536, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_9419, c_9535])).
% 9.84/3.15  tff(c_11718, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6'))) | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_11705, c_9536])).
% 9.84/3.15  tff(c_11733, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_9418, c_11718])).
% 9.84/3.15  tff(c_9131, plain, (![A_513, B_514]: (k3_xboole_0(A_513, B_514)=A_513 | ~r1_tarski(A_513, B_514))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.84/3.15  tff(c_9843, plain, (![B_589, A_590]: (k3_xboole_0(k3_xboole_0(B_589, A_590), A_590)=k3_xboole_0(B_589, A_590))), inference(resolution, [status(thm)], [c_102, c_9131])).
% 9.84/3.15  tff(c_9904, plain, (![A_590, B_589]: (k3_xboole_0(A_590, k3_xboole_0(B_589, A_590))=k3_xboole_0(B_589, A_590))), inference(superposition, [status(thm), theory('equality')], [c_9843, c_2])).
% 9.84/3.15  tff(c_10150, plain, (![A_595, B_596, C_597]: (r2_hidden(A_595, B_596) | ~r2_hidden(A_595, C_597) | r2_hidden(A_595, k5_xboole_0(B_596, C_597)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.84/3.15  tff(c_10162, plain, (![A_595, A_13, B_14]: (r2_hidden(A_595, A_13) | ~r2_hidden(A_595, k3_xboole_0(A_13, B_14)) | r2_hidden(A_595, k4_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_10150])).
% 9.84/3.15  tff(c_9443, plain, (![A_553, B_554]: (k3_xboole_0(k3_xboole_0(A_553, B_554), A_553)=k3_xboole_0(A_553, B_554))), inference(resolution, [status(thm)], [c_26, c_9131])).
% 9.84/3.15  tff(c_9464, plain, (![A_553, B_554]: (k3_xboole_0(A_553, k3_xboole_0(A_553, B_554))=k3_xboole_0(A_553, B_554))), inference(superposition, [status(thm), theory('equality')], [c_9443, c_2])).
% 9.84/3.15  tff(c_9433, plain, (![A_550, B_551, C_552]: (~r1_xboole_0(A_550, B_551) | ~r2_hidden(C_552, B_551) | ~r2_hidden(C_552, A_550))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.84/3.15  tff(c_11297, plain, (![C_649, A_650, B_651]: (~r2_hidden(C_649, k5_xboole_0(A_650, B_651)) | ~r2_hidden(C_649, k3_xboole_0(A_650, B_651)))), inference(resolution, [status(thm)], [c_22, c_9433])).
% 9.84/3.15  tff(c_11325, plain, (![C_649, A_13, B_14]: (~r2_hidden(C_649, k4_xboole_0(A_13, B_14)) | ~r2_hidden(C_649, k3_xboole_0(A_13, k3_xboole_0(A_13, B_14))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_11297])).
% 9.84/3.15  tff(c_12430, plain, (![C_694, A_695, B_696]: (~r2_hidden(C_694, k4_xboole_0(A_695, B_696)) | ~r2_hidden(C_694, k3_xboole_0(A_695, B_696)))), inference(demodulation, [status(thm), theory('equality')], [c_9464, c_11325])).
% 9.84/3.15  tff(c_12487, plain, (![A_697, A_698, B_699]: (r2_hidden(A_697, A_698) | ~r2_hidden(A_697, k3_xboole_0(A_698, B_699)))), inference(resolution, [status(thm)], [c_10162, c_12430])).
% 9.84/3.15  tff(c_12568, plain, (![A_700, A_701, B_702]: (r2_hidden(A_700, A_701) | ~r2_hidden(A_700, k3_xboole_0(B_702, A_701)))), inference(superposition, [status(thm), theory('equality')], [c_9904, c_12487])).
% 9.84/3.15  tff(c_12643, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_11733, c_12568])).
% 9.84/3.15  tff(c_12650, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_12643, c_32])).
% 9.84/3.15  tff(c_12654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9129, c_12650])).
% 9.84/3.15  tff(c_12655, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_9180])).
% 9.84/3.15  tff(c_13281, plain, (![A_740, C_741, B_742]: (r2_hidden(A_740, C_741) | ~r2_hidden(A_740, B_742) | r2_hidden(A_740, k5_xboole_0(B_742, C_741)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.84/3.15  tff(c_15271, plain, (![A_832, A_833, B_834]: (r2_hidden(A_832, k3_xboole_0(A_833, B_834)) | ~r2_hidden(A_832, A_833) | r2_hidden(A_832, k4_xboole_0(A_833, B_834)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_13281])).
% 9.84/3.15  tff(c_12656, plain, ('#skF_7'!='#skF_9'), inference(splitRight, [status(thm)], [c_9180])).
% 9.84/3.15  tff(c_58, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6'))) | '#skF_7'='#skF_9' | ~r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.84/3.15  tff(c_12856, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6'))) | '#skF_7'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9128, c_58])).
% 9.84/3.15  tff(c_12857, plain, (~r2_hidden('#skF_4', k4_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_12656, c_12856])).
% 9.84/3.15  tff(c_15287, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6'))) | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_15271, c_12857])).
% 9.84/3.15  tff(c_15300, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_12655, c_15287])).
% 9.84/3.15  tff(c_13152, plain, (![B_738, A_739]: (k3_xboole_0(k3_xboole_0(B_738, A_739), A_739)=k3_xboole_0(B_738, A_739))), inference(resolution, [status(thm)], [c_102, c_9131])).
% 9.84/3.15  tff(c_13219, plain, (![A_739, B_738]: (k3_xboole_0(A_739, k3_xboole_0(B_738, A_739))=k3_xboole_0(B_738, A_739))), inference(superposition, [status(thm), theory('equality')], [c_13152, c_2])).
% 9.84/3.15  tff(c_13502, plain, (![A_750, B_751, C_752]: (r2_hidden(A_750, B_751) | ~r2_hidden(A_750, C_752) | r2_hidden(A_750, k5_xboole_0(B_751, C_752)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.84/3.15  tff(c_13511, plain, (![A_750, A_13, B_14]: (r2_hidden(A_750, A_13) | ~r2_hidden(A_750, k3_xboole_0(A_13, B_14)) | r2_hidden(A_750, k4_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_13502])).
% 9.84/3.15  tff(c_12705, plain, (![A_709, B_710]: (k3_xboole_0(k3_xboole_0(A_709, B_710), A_709)=k3_xboole_0(A_709, B_710))), inference(resolution, [status(thm)], [c_26, c_9131])).
% 9.84/3.15  tff(c_12732, plain, (![A_709, B_710]: (k3_xboole_0(A_709, k3_xboole_0(A_709, B_710))=k3_xboole_0(A_709, B_710))), inference(superposition, [status(thm), theory('equality')], [c_12705, c_2])).
% 9.84/3.15  tff(c_12798, plain, (![A_715, B_716, C_717]: (~r1_xboole_0(A_715, B_716) | ~r2_hidden(C_717, B_716) | ~r2_hidden(C_717, A_715))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.84/3.15  tff(c_14702, plain, (![C_810, A_811, B_812]: (~r2_hidden(C_810, k5_xboole_0(A_811, B_812)) | ~r2_hidden(C_810, k3_xboole_0(A_811, B_812)))), inference(resolution, [status(thm)], [c_22, c_12798])).
% 9.84/3.15  tff(c_14730, plain, (![C_810, A_13, B_14]: (~r2_hidden(C_810, k4_xboole_0(A_13, B_14)) | ~r2_hidden(C_810, k3_xboole_0(A_13, k3_xboole_0(A_13, B_14))))), inference(superposition, [status(thm), theory('equality')], [c_24, c_14702])).
% 9.84/3.15  tff(c_15616, plain, (![C_848, A_849, B_850]: (~r2_hidden(C_848, k4_xboole_0(A_849, B_850)) | ~r2_hidden(C_848, k3_xboole_0(A_849, B_850)))), inference(demodulation, [status(thm), theory('equality')], [c_12732, c_14730])).
% 9.84/3.15  tff(c_15712, plain, (![A_854, A_855, B_856]: (r2_hidden(A_854, A_855) | ~r2_hidden(A_854, k3_xboole_0(A_855, B_856)))), inference(resolution, [status(thm)], [c_13511, c_15616])).
% 9.84/3.15  tff(c_15788, plain, (![A_857, A_858, B_859]: (r2_hidden(A_857, A_858) | ~r2_hidden(A_857, k3_xboole_0(B_859, A_858)))), inference(superposition, [status(thm), theory('equality')], [c_13219, c_15712])).
% 9.84/3.15  tff(c_15858, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_15300, c_15788])).
% 9.84/3.15  tff(c_15865, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_15858, c_32])).
% 9.84/3.15  tff(c_15869, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9129, c_15865])).
% 9.84/3.15  tff(c_15870, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_9127])).
% 9.84/3.15  tff(c_15871, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_9127])).
% 9.84/3.15  tff(c_15872, plain, ('#skF_6'!='#skF_4'), inference(splitLeft, [status(thm)], [c_66])).
% 9.84/3.15  tff(c_15883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15871, c_15872])).
% 9.84/3.15  tff(c_15884, plain, (r2_hidden('#skF_7', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(splitRight, [status(thm)], [c_66])).
% 9.84/3.15  tff(c_15896, plain, (r2_hidden('#skF_9', k4_xboole_0('#skF_8', k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_15870, c_15884])).
% 9.84/3.15  tff(c_16443, plain, (![A_893, B_894, C_895]: (~r1_xboole_0(A_893, B_894) | ~r2_hidden(C_895, B_894) | ~r2_hidden(C_895, A_893))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.84/3.15  tff(c_16459, plain, (![C_896, B_897, A_898]: (~r2_hidden(C_896, B_897) | ~r2_hidden(C_896, k4_xboole_0(A_898, B_897)))), inference(resolution, [status(thm)], [c_30, c_16443])).
% 9.84/3.15  tff(c_16470, plain, (~r2_hidden('#skF_9', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_15896, c_16459])).
% 9.84/3.15  tff(c_16476, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_16470])).
% 9.84/3.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.84/3.15  
% 9.84/3.15  Inference rules
% 9.84/3.15  ----------------------
% 9.84/3.15  #Ref     : 0
% 9.84/3.15  #Sup     : 3923
% 9.84/3.15  #Fact    : 16
% 9.84/3.15  #Define  : 0
% 9.84/3.15  #Split   : 8
% 9.84/3.15  #Chain   : 0
% 9.84/3.15  #Close   : 0
% 9.84/3.15  
% 9.84/3.15  Ordering : KBO
% 9.84/3.15  
% 9.84/3.15  Simplification rules
% 9.84/3.15  ----------------------
% 9.84/3.15  #Subsume      : 242
% 9.84/3.15  #Demod        : 4162
% 9.84/3.15  #Tautology    : 2130
% 9.84/3.15  #SimpNegUnit  : 9
% 9.84/3.15  #BackRed      : 3
% 9.84/3.15  
% 9.84/3.15  #Partial instantiations: 0
% 9.84/3.15  #Strategies tried      : 1
% 9.84/3.15  
% 9.84/3.15  Timing (in seconds)
% 9.84/3.15  ----------------------
% 9.84/3.16  Preprocessing        : 0.33
% 9.84/3.16  Parsing              : 0.17
% 9.84/3.16  CNF conversion       : 0.02
% 9.84/3.16  Main loop            : 2.00
% 9.84/3.16  Inferencing          : 0.51
% 9.84/3.16  Reduction            : 0.97
% 9.84/3.16  Demodulation         : 0.82
% 9.84/3.16  BG Simplification    : 0.07
% 9.84/3.16  Subsumption          : 0.32
% 9.84/3.16  Abstraction          : 0.09
% 9.84/3.16  MUC search           : 0.00
% 9.84/3.16  Cooper               : 0.00
% 9.84/3.16  Total                : 2.41
% 9.84/3.16  Index Insertion      : 0.00
% 9.84/3.16  Index Deletion       : 0.00
% 9.84/3.16  Index Matching       : 0.00
% 9.84/3.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
