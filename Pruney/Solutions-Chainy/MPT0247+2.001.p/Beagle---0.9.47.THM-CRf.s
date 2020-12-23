%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:04 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 475 expanded)
%              Number of leaves         :   15 ( 133 expanded)
%              Depth                    :    8
%              Number of atoms          :  205 (1298 expanded)
%              Number of equality atoms :  125 ( 984 expanded)
%              Maximal formula depth    :   11 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k2_tarski(B,C))
      <=> ~ ( A != k1_xboole_0
            & A != k1_tarski(B)
            & A != k1_tarski(C)
            & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(c_24,plain,
    ( ~ r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3'))
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_20,plain,
    ( ~ r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3'))
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_16,plain,
    ( ~ r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3'))
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_37,plain,(
    k1_tarski('#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_12,plain,
    ( ~ r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3'))
    | k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,(
    k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_30,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | r1_tarski('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_61,plain,(
    r1_tarski('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_2,plain,(
    ! [B_2,C_3,A_1] :
      ( k2_tarski(B_2,C_3) = A_1
      | k1_tarski(C_3) = A_1
      | k1_tarski(B_2) = A_1
      | k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k2_tarski(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_64,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_61,c_2])).

tff(c_68,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_36,c_37,c_38,c_64])).

tff(c_69,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_71,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_28,plain,
    ( ~ r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3'))
    | r1_tarski('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_39,plain,(
    ~ r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_72,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_39])).

tff(c_4,plain,(
    ! [B_2,C_3] : r1_tarski(k2_tarski(B_2,C_3),k2_tarski(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_79,plain,(
    r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_4])).

tff(c_94,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_79])).

tff(c_97,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_94])).

tff(c_98,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_100,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_10,plain,(
    ! [B_2,C_3] : r1_tarski(k1_xboole_0,k2_tarski(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_103,plain,(
    ! [B_2,C_3] : r1_tarski('#skF_1',k2_tarski(B_2,C_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_10])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_39])).

tff(c_111,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_113,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_6,plain,(
    ! [C_3,B_2] : r1_tarski(k1_tarski(C_3),k2_tarski(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_117,plain,(
    ! [B_2] : r1_tarski('#skF_1',k2_tarski(B_2,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_6])).

tff(c_126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_39])).

tff(c_127,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_8,plain,(
    ! [B_2,C_3] : r1_tarski(k1_tarski(B_2),k2_tarski(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_135,plain,(
    ! [C_3] : r1_tarski('#skF_1',k2_tarski('#skF_2',C_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_8])).

tff(c_148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_39])).

tff(c_149,plain,(
    r1_tarski('#skF_4',k2_tarski('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_151,plain,(
    ! [B_16,C_17,A_18] :
      ( k2_tarski(B_16,C_17) = A_18
      | k1_tarski(C_17) = A_18
      | k1_tarski(B_16) = A_18
      | k1_xboole_0 = A_18
      | ~ r1_tarski(A_18,k2_tarski(B_16,C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_157,plain,
    ( k2_tarski('#skF_5','#skF_6') = '#skF_4'
    | k1_tarski('#skF_6') = '#skF_4'
    | k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_149,c_151])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_36,c_37,c_38,c_157])).

tff(c_175,plain,(
    ~ r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_176,plain,(
    k2_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_14,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k2_tarski('#skF_5','#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_201,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_14])).

tff(c_202,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_205,plain,(
    ! [B_2,C_3] : r1_tarski('#skF_1',k2_tarski(B_2,C_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_10])).

tff(c_197,plain,
    ( ~ r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3'))
    | r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_28])).

tff(c_198,plain,(
    ~ r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_198])).

tff(c_213,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_215,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_216,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_198])).

tff(c_223,plain,(
    r1_tarski(k2_tarski('#skF_2','#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_4])).

tff(c_235,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_223])).

tff(c_239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_216,c_235])).

tff(c_240,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_242,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_240])).

tff(c_249,plain,(
    ! [C_3] : r1_tarski('#skF_1',k2_tarski('#skF_2',C_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_8])).

tff(c_258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_198])).

tff(c_259,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_266,plain,(
    ! [B_2] : r1_tarski('#skF_1',k2_tarski(B_2,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_6])).

tff(c_275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_198])).

tff(c_277,plain,(
    r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_277])).

tff(c_282,plain,(
    k1_tarski('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_18,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_297,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_18])).

tff(c_298,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_297])).

tff(c_300,plain,(
    ! [B_2,C_3] : r1_tarski('#skF_1',k2_tarski(B_2,C_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_10])).

tff(c_281,plain,(
    ~ r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_281])).

tff(c_308,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_297])).

tff(c_310,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_308])).

tff(c_311,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_281])).

tff(c_315,plain,(
    r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_4])).

tff(c_329,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_315])).

tff(c_332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_311,c_329])).

tff(c_333,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_337,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_333])).

tff(c_344,plain,(
    ! [C_3] : r1_tarski('#skF_1',k2_tarski('#skF_2',C_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_8])).

tff(c_351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_281])).

tff(c_352,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_333])).

tff(c_357,plain,(
    ! [B_2] : r1_tarski('#skF_1',k2_tarski(B_2,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_6])).

tff(c_367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_281])).

tff(c_369,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_22,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_385,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_22])).

tff(c_386,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_385])).

tff(c_388,plain,(
    ! [B_2,C_3] : r1_tarski('#skF_1',k2_tarski(B_2,C_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_10])).

tff(c_368,plain,(
    ~ r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_368])).

tff(c_396,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_385])).

tff(c_398,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_396])).

tff(c_399,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_368])).

tff(c_403,plain,(
    r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_4])).

tff(c_417,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_403])).

tff(c_420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_399,c_417])).

tff(c_421,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_396])).

tff(c_424,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_421])).

tff(c_431,plain,(
    ! [C_3] : r1_tarski('#skF_1',k2_tarski('#skF_2',C_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_8])).

tff(c_438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_368])).

tff(c_439,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_444,plain,(
    ! [B_2] : r1_tarski('#skF_1',k2_tarski(B_2,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_6])).

tff(c_453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_368])).

tff(c_455,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_456,plain,(
    ! [B_2,C_3] : r1_tarski('#skF_4',k2_tarski(B_2,C_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_10])).

tff(c_26,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_466,plain,
    ( k2_tarski('#skF_2','#skF_3') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1'
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_455,c_26])).

tff(c_467,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_466])).

tff(c_454,plain,(
    ~ r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_468,plain,(
    ~ r1_tarski('#skF_4',k2_tarski('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_454])).

tff(c_471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_468])).

tff(c_472,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_tarski('#skF_3') = '#skF_1'
    | k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_466])).

tff(c_475,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_476,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_454])).

tff(c_480,plain,(
    r1_tarski('#skF_1',k2_tarski('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_4])).

tff(c_494,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_480])).

tff(c_499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_476,c_494])).

tff(c_500,plain,
    ( k1_tarski('#skF_3') = '#skF_1'
    | k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_502,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_500])).

tff(c_512,plain,(
    ! [C_3] : r1_tarski('#skF_1',k2_tarski('#skF_2',C_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_502,c_8])).

tff(c_519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_454])).

tff(c_520,plain,(
    k1_tarski('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_500])).

tff(c_525,plain,(
    ! [B_2] : r1_tarski('#skF_1',k2_tarski(B_2,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_6])).

tff(c_534,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_454])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:30:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.37  
% 2.49/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.38  %$ r1_tarski > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.49/1.38  
% 2.49/1.38  %Foreground sorts:
% 2.49/1.38  
% 2.49/1.38  
% 2.49/1.38  %Background operators:
% 2.49/1.38  
% 2.49/1.38  
% 2.49/1.38  %Foreground operators:
% 2.49/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.49/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.49/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.49/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.38  
% 2.49/1.40  tff(f_56, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_zfmisc_1)).
% 2.49/1.40  tff(f_40, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.49/1.40  tff(c_24, plain, (~r1_tarski('#skF_1', k2_tarski('#skF_2', '#skF_3')) | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.49/1.40  tff(c_34, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_24])).
% 2.49/1.40  tff(c_20, plain, (~r1_tarski('#skF_1', k2_tarski('#skF_2', '#skF_3')) | k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.49/1.40  tff(c_36, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_20])).
% 2.49/1.40  tff(c_16, plain, (~r1_tarski('#skF_1', k2_tarski('#skF_2', '#skF_3')) | k1_tarski('#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.49/1.40  tff(c_37, plain, (k1_tarski('#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_16])).
% 2.49/1.40  tff(c_12, plain, (~r1_tarski('#skF_1', k2_tarski('#skF_2', '#skF_3')) | k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.49/1.40  tff(c_38, plain, (k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_12])).
% 2.49/1.40  tff(c_30, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | r1_tarski('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.49/1.40  tff(c_61, plain, (r1_tarski('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_30])).
% 2.49/1.40  tff(c_2, plain, (![B_2, C_3, A_1]: (k2_tarski(B_2, C_3)=A_1 | k1_tarski(C_3)=A_1 | k1_tarski(B_2)=A_1 | k1_xboole_0=A_1 | ~r1_tarski(A_1, k2_tarski(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.49/1.40  tff(c_64, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_61, c_2])).
% 2.49/1.40  tff(c_68, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_36, c_37, c_38, c_64])).
% 2.49/1.40  tff(c_69, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_30])).
% 2.49/1.40  tff(c_71, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_69])).
% 2.49/1.40  tff(c_28, plain, (~r1_tarski('#skF_1', k2_tarski('#skF_2', '#skF_3')) | r1_tarski('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.49/1.40  tff(c_39, plain, (~r1_tarski('#skF_1', k2_tarski('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_28])).
% 2.49/1.40  tff(c_72, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_39])).
% 2.49/1.40  tff(c_4, plain, (![B_2, C_3]: (r1_tarski(k2_tarski(B_2, C_3), k2_tarski(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.49/1.40  tff(c_79, plain, (r1_tarski('#skF_1', k2_tarski('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_71, c_4])).
% 2.49/1.40  tff(c_94, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_79])).
% 2.49/1.40  tff(c_97, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_94])).
% 2.49/1.40  tff(c_98, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_69])).
% 2.49/1.40  tff(c_100, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_98])).
% 2.49/1.40  tff(c_10, plain, (![B_2, C_3]: (r1_tarski(k1_xboole_0, k2_tarski(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.49/1.40  tff(c_103, plain, (![B_2, C_3]: (r1_tarski('#skF_1', k2_tarski(B_2, C_3)))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_10])).
% 2.49/1.40  tff(c_110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_39])).
% 2.49/1.40  tff(c_111, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_98])).
% 2.49/1.40  tff(c_113, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_111])).
% 2.49/1.40  tff(c_6, plain, (![C_3, B_2]: (r1_tarski(k1_tarski(C_3), k2_tarski(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.49/1.40  tff(c_117, plain, (![B_2]: (r1_tarski('#skF_1', k2_tarski(B_2, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_113, c_6])).
% 2.49/1.40  tff(c_126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_39])).
% 2.49/1.40  tff(c_127, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_111])).
% 2.49/1.40  tff(c_8, plain, (![B_2, C_3]: (r1_tarski(k1_tarski(B_2), k2_tarski(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.49/1.40  tff(c_135, plain, (![C_3]: (r1_tarski('#skF_1', k2_tarski('#skF_2', C_3)))), inference(superposition, [status(thm), theory('equality')], [c_127, c_8])).
% 2.49/1.40  tff(c_148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_135, c_39])).
% 2.49/1.40  tff(c_149, plain, (r1_tarski('#skF_4', k2_tarski('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_28])).
% 2.49/1.40  tff(c_151, plain, (![B_16, C_17, A_18]: (k2_tarski(B_16, C_17)=A_18 | k1_tarski(C_17)=A_18 | k1_tarski(B_16)=A_18 | k1_xboole_0=A_18 | ~r1_tarski(A_18, k2_tarski(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.49/1.40  tff(c_157, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4' | k1_tarski('#skF_6')='#skF_4' | k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_149, c_151])).
% 2.49/1.40  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_36, c_37, c_38, c_157])).
% 2.49/1.40  tff(c_175, plain, (~r1_tarski('#skF_1', k2_tarski('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_12])).
% 2.49/1.40  tff(c_176, plain, (k2_tarski('#skF_5', '#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_12])).
% 2.49/1.40  tff(c_14, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k2_tarski('#skF_5', '#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.49/1.40  tff(c_201, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_176, c_14])).
% 2.49/1.40  tff(c_202, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_201])).
% 2.49/1.40  tff(c_205, plain, (![B_2, C_3]: (r1_tarski('#skF_1', k2_tarski(B_2, C_3)))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_10])).
% 2.49/1.40  tff(c_197, plain, (~r1_tarski('#skF_1', k2_tarski('#skF_2', '#skF_3')) | r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_28])).
% 2.49/1.40  tff(c_198, plain, (~r1_tarski('#skF_1', k2_tarski('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_197])).
% 2.49/1.40  tff(c_212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_198])).
% 2.49/1.40  tff(c_213, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_201])).
% 2.49/1.40  tff(c_215, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_213])).
% 2.49/1.40  tff(c_216, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_198])).
% 2.49/1.40  tff(c_223, plain, (r1_tarski(k2_tarski('#skF_2', '#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_215, c_4])).
% 2.49/1.40  tff(c_235, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_223])).
% 2.49/1.40  tff(c_239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_216, c_235])).
% 2.49/1.40  tff(c_240, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_213])).
% 2.49/1.40  tff(c_242, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_240])).
% 2.49/1.40  tff(c_249, plain, (![C_3]: (r1_tarski('#skF_1', k2_tarski('#skF_2', C_3)))), inference(superposition, [status(thm), theory('equality')], [c_242, c_8])).
% 2.49/1.40  tff(c_258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_249, c_198])).
% 2.49/1.40  tff(c_259, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_240])).
% 2.49/1.40  tff(c_266, plain, (![B_2]: (r1_tarski('#skF_1', k2_tarski(B_2, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_259, c_6])).
% 2.49/1.40  tff(c_275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_266, c_198])).
% 2.49/1.40  tff(c_277, plain, (r1_tarski('#skF_1', k2_tarski('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_197])).
% 2.49/1.40  tff(c_280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_175, c_277])).
% 2.49/1.40  tff(c_282, plain, (k1_tarski('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_16])).
% 2.49/1.40  tff(c_18, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.49/1.40  tff(c_297, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_282, c_18])).
% 2.49/1.40  tff(c_298, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_297])).
% 2.49/1.40  tff(c_300, plain, (![B_2, C_3]: (r1_tarski('#skF_1', k2_tarski(B_2, C_3)))), inference(demodulation, [status(thm), theory('equality')], [c_298, c_10])).
% 2.49/1.40  tff(c_281, plain, (~r1_tarski('#skF_1', k2_tarski('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_16])).
% 2.49/1.40  tff(c_307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_300, c_281])).
% 2.49/1.40  tff(c_308, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_297])).
% 2.49/1.40  tff(c_310, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_308])).
% 2.49/1.40  tff(c_311, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_310, c_281])).
% 2.49/1.40  tff(c_315, plain, (r1_tarski('#skF_1', k2_tarski('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_310, c_4])).
% 2.49/1.40  tff(c_329, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_310, c_315])).
% 2.49/1.40  tff(c_332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_311, c_329])).
% 2.49/1.40  tff(c_333, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_308])).
% 2.49/1.40  tff(c_337, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_333])).
% 2.49/1.40  tff(c_344, plain, (![C_3]: (r1_tarski('#skF_1', k2_tarski('#skF_2', C_3)))), inference(superposition, [status(thm), theory('equality')], [c_337, c_8])).
% 2.49/1.40  tff(c_351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_344, c_281])).
% 2.49/1.40  tff(c_352, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_333])).
% 2.49/1.40  tff(c_357, plain, (![B_2]: (r1_tarski('#skF_1', k2_tarski(B_2, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_352, c_6])).
% 2.49/1.40  tff(c_367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_357, c_281])).
% 2.49/1.40  tff(c_369, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_20])).
% 2.49/1.40  tff(c_22, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.49/1.40  tff(c_385, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_369, c_22])).
% 2.49/1.40  tff(c_386, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_385])).
% 2.49/1.40  tff(c_388, plain, (![B_2, C_3]: (r1_tarski('#skF_1', k2_tarski(B_2, C_3)))), inference(demodulation, [status(thm), theory('equality')], [c_386, c_10])).
% 2.49/1.40  tff(c_368, plain, (~r1_tarski('#skF_1', k2_tarski('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_20])).
% 2.49/1.40  tff(c_395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_388, c_368])).
% 2.49/1.40  tff(c_396, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_385])).
% 2.49/1.40  tff(c_398, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_396])).
% 2.49/1.40  tff(c_399, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_398, c_368])).
% 2.49/1.40  tff(c_403, plain, (r1_tarski('#skF_1', k2_tarski('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_398, c_4])).
% 2.49/1.40  tff(c_417, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_398, c_403])).
% 2.49/1.40  tff(c_420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_399, c_417])).
% 2.49/1.40  tff(c_421, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_396])).
% 2.49/1.40  tff(c_424, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_421])).
% 2.49/1.40  tff(c_431, plain, (![C_3]: (r1_tarski('#skF_1', k2_tarski('#skF_2', C_3)))), inference(superposition, [status(thm), theory('equality')], [c_424, c_8])).
% 2.49/1.40  tff(c_438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_431, c_368])).
% 2.49/1.40  tff(c_439, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_421])).
% 2.49/1.40  tff(c_444, plain, (![B_2]: (r1_tarski('#skF_1', k2_tarski(B_2, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_439, c_6])).
% 2.49/1.40  tff(c_453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_444, c_368])).
% 2.49/1.40  tff(c_455, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_24])).
% 2.49/1.40  tff(c_456, plain, (![B_2, C_3]: (r1_tarski('#skF_4', k2_tarski(B_2, C_3)))), inference(demodulation, [status(thm), theory('equality')], [c_455, c_10])).
% 2.49/1.40  tff(c_26, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.49/1.40  tff(c_466, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1' | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_455, c_455, c_26])).
% 2.49/1.40  tff(c_467, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_466])).
% 2.49/1.40  tff(c_454, plain, (~r1_tarski('#skF_1', k2_tarski('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_24])).
% 2.49/1.40  tff(c_468, plain, (~r1_tarski('#skF_4', k2_tarski('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_467, c_454])).
% 2.49/1.40  tff(c_471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_456, c_468])).
% 2.49/1.40  tff(c_472, plain, (k1_tarski('#skF_2')='#skF_1' | k1_tarski('#skF_3')='#skF_1' | k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_466])).
% 2.49/1.40  tff(c_475, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_472])).
% 2.49/1.40  tff(c_476, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_475, c_454])).
% 2.49/1.40  tff(c_480, plain, (r1_tarski('#skF_1', k2_tarski('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_475, c_4])).
% 2.49/1.40  tff(c_494, plain, (r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_475, c_480])).
% 2.49/1.40  tff(c_499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_476, c_494])).
% 2.49/1.40  tff(c_500, plain, (k1_tarski('#skF_3')='#skF_1' | k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_472])).
% 2.49/1.40  tff(c_502, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_500])).
% 2.49/1.40  tff(c_512, plain, (![C_3]: (r1_tarski('#skF_1', k2_tarski('#skF_2', C_3)))), inference(superposition, [status(thm), theory('equality')], [c_502, c_8])).
% 2.49/1.40  tff(c_519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_512, c_454])).
% 2.49/1.40  tff(c_520, plain, (k1_tarski('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_500])).
% 2.49/1.40  tff(c_525, plain, (![B_2]: (r1_tarski('#skF_1', k2_tarski(B_2, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_520, c_6])).
% 2.49/1.40  tff(c_534, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_525, c_454])).
% 2.49/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.40  
% 2.49/1.40  Inference rules
% 2.49/1.40  ----------------------
% 2.49/1.40  #Ref     : 0
% 2.49/1.40  #Sup     : 113
% 2.49/1.40  #Fact    : 0
% 2.49/1.40  #Define  : 0
% 2.49/1.40  #Split   : 26
% 2.49/1.40  #Chain   : 0
% 2.49/1.40  #Close   : 0
% 2.49/1.40  
% 2.49/1.40  Ordering : KBO
% 2.49/1.40  
% 2.49/1.40  Simplification rules
% 2.49/1.40  ----------------------
% 2.49/1.40  #Subsume      : 26
% 2.49/1.40  #Demod        : 70
% 2.49/1.40  #Tautology    : 58
% 2.49/1.40  #SimpNegUnit  : 16
% 2.49/1.40  #BackRed      : 31
% 2.49/1.40  
% 2.49/1.40  #Partial instantiations: 0
% 2.49/1.40  #Strategies tried      : 1
% 2.49/1.40  
% 2.49/1.40  Timing (in seconds)
% 2.49/1.40  ----------------------
% 2.49/1.40  Preprocessing        : 0.28
% 2.49/1.40  Parsing              : 0.15
% 2.49/1.40  CNF conversion       : 0.02
% 2.49/1.40  Main loop            : 0.28
% 2.49/1.40  Inferencing          : 0.08
% 2.49/1.40  Reduction            : 0.10
% 2.49/1.40  Demodulation         : 0.06
% 2.49/1.40  BG Simplification    : 0.02
% 2.49/1.40  Subsumption          : 0.05
% 2.49/1.40  Abstraction          : 0.01
% 2.49/1.40  MUC search           : 0.00
% 2.49/1.40  Cooper               : 0.00
% 2.49/1.40  Total                : 0.61
% 2.49/1.40  Index Insertion      : 0.00
% 2.49/1.40  Index Deletion       : 0.00
% 2.49/1.40  Index Matching       : 0.00
% 2.49/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
