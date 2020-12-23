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
% DateTime   : Thu Dec  3 09:53:39 EST 2020

% Result     : Theorem 9.40s
% Output     : CNFRefutation 9.40s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 730 expanded)
%              Number of leaves         :   38 ( 235 expanded)
%              Depth                    :   13
%              Number of atoms          :  208 (1394 expanded)
%              Number of equality atoms :   85 (1069 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_15 > #skF_1 > #skF_12 > #skF_3 > #skF_16 > #skF_14 > #skF_13 > #skF_11 > #skF_7 > #skF_9 > #skF_2 > #skF_8 > #skF_5 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_185,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_71,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_146,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_118,plain,
    ( k2_zfmisc_1('#skF_13','#skF_14') != k1_xboole_0
    | k1_xboole_0 != '#skF_16' ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_207,plain,(
    k1_xboole_0 != '#skF_16' ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_24,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_4'(A_18),A_18)
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_122,plain,
    ( k2_zfmisc_1('#skF_13','#skF_14') != k1_xboole_0
    | k1_xboole_0 != '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_178,plain,(
    k1_xboole_0 != '#skF_15' ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_14,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_128,plain,
    ( k1_xboole_0 = '#skF_14'
    | k1_xboole_0 = '#skF_13'
    | k2_zfmisc_1('#skF_15','#skF_16') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_403,plain,(
    k2_zfmisc_1('#skF_15','#skF_16') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_1826,plain,(
    ! [E_245,F_246,A_247,B_248] :
      ( r2_hidden(k4_tarski(E_245,F_246),k2_zfmisc_1(A_247,B_248))
      | ~ r2_hidden(F_246,B_248)
      | ~ r2_hidden(E_245,A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1984,plain,(
    ! [E_257,F_258] :
      ( r2_hidden(k4_tarski(E_257,F_258),k1_xboole_0)
      | ~ r2_hidden(F_258,'#skF_16')
      | ~ r2_hidden(E_257,'#skF_15') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_1826])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1991,plain,(
    ! [F_258,E_257] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(F_258,'#skF_16')
      | ~ r2_hidden(E_257,'#skF_15') ) ),
    inference(resolution,[status(thm)],[c_1984,c_4])).

tff(c_1998,plain,(
    ! [F_258,E_257] :
      ( ~ r2_hidden(F_258,'#skF_16')
      | ~ r2_hidden(E_257,'#skF_15') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1991])).

tff(c_2056,plain,(
    ! [E_261] : ~ r2_hidden(E_261,'#skF_15') ),
    inference(splitLeft,[status(thm)],[c_1998])).

tff(c_2084,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(resolution,[status(thm)],[c_24,c_2056])).

tff(c_2098,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_2084])).

tff(c_2100,plain,(
    ! [F_262] : ~ r2_hidden(F_262,'#skF_16') ),
    inference(splitRight,[status(thm)],[c_1998])).

tff(c_2128,plain,(
    k1_xboole_0 = '#skF_16' ),
    inference(resolution,[status(thm)],[c_24,c_2100])).

tff(c_2142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_2128])).

tff(c_2143,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_2145,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_2143])).

tff(c_2150,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_4'(A_18),A_18)
      | A_18 = '#skF_14' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2145,c_24])).

tff(c_74,plain,(
    ! [A_55,B_56,D_82] :
      ( r2_hidden('#skF_12'(A_55,B_56,k2_zfmisc_1(A_55,B_56),D_82),B_56)
      | ~ r2_hidden(D_82,k2_zfmisc_1(A_55,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2161,plain,(
    v1_xboole_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2145,c_14])).

tff(c_3952,plain,(
    ! [A_397,B_398,D_399] :
      ( r2_hidden('#skF_11'(A_397,B_398,k2_zfmisc_1(A_397,B_398),D_399),A_397)
      | ~ r2_hidden(D_399,k2_zfmisc_1(A_397,B_398)) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_4255,plain,(
    ! [A_422,D_423,B_424] :
      ( ~ v1_xboole_0(A_422)
      | ~ r2_hidden(D_423,k2_zfmisc_1(A_422,B_424)) ) ),
    inference(resolution,[status(thm)],[c_3952,c_4])).

tff(c_4368,plain,(
    ! [A_430,B_431] :
      ( ~ v1_xboole_0(A_430)
      | k2_zfmisc_1(A_430,B_431) = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_2150,c_4255])).

tff(c_4378,plain,(
    ! [B_432] : k2_zfmisc_1('#skF_14',B_432) = '#skF_14' ),
    inference(resolution,[status(thm)],[c_2161,c_4368])).

tff(c_3968,plain,(
    ! [A_397,D_399,B_398] :
      ( ~ v1_xboole_0(A_397)
      | ~ r2_hidden(D_399,k2_zfmisc_1(A_397,B_398)) ) ),
    inference(resolution,[status(thm)],[c_3952,c_4])).

tff(c_4386,plain,(
    ! [D_399] :
      ( ~ v1_xboole_0('#skF_14')
      | ~ r2_hidden(D_399,'#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4378,c_3968])).

tff(c_4407,plain,(
    ! [D_433] : ~ r2_hidden(D_433,'#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2161,c_4386])).

tff(c_4499,plain,(
    ! [D_440,A_441] : ~ r2_hidden(D_440,k2_zfmisc_1(A_441,'#skF_14')) ),
    inference(resolution,[status(thm)],[c_74,c_4407])).

tff(c_4576,plain,(
    ! [A_441] : k2_zfmisc_1(A_441,'#skF_14') = '#skF_14' ),
    inference(resolution,[status(thm)],[c_2150,c_4499])).

tff(c_126,plain,
    ( k2_zfmisc_1('#skF_13','#skF_14') != k1_xboole_0
    | k2_zfmisc_1('#skF_15','#skF_16') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_309,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_2149,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2145,c_309])).

tff(c_4581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4576,c_2149])).

tff(c_4582,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_2143])).

tff(c_4601,plain,(
    v1_xboole_0('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4582,c_14])).

tff(c_4590,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_4'(A_18),A_18)
      | A_18 = '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4582,c_24])).

tff(c_6532,plain,(
    ! [A_597,B_598,D_599] :
      ( r2_hidden('#skF_11'(A_597,B_598,k2_zfmisc_1(A_597,B_598),D_599),A_597)
      | ~ r2_hidden(D_599,k2_zfmisc_1(A_597,B_598)) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_6657,plain,(
    ! [A_610,D_611,B_612] :
      ( ~ v1_xboole_0(A_610)
      | ~ r2_hidden(D_611,k2_zfmisc_1(A_610,B_612)) ) ),
    inference(resolution,[status(thm)],[c_6532,c_4])).

tff(c_6737,plain,(
    ! [A_618,B_619] :
      ( ~ v1_xboole_0(A_618)
      | k2_zfmisc_1(A_618,B_619) = '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_4590,c_6657])).

tff(c_6746,plain,(
    ! [B_619] : k2_zfmisc_1('#skF_13',B_619) = '#skF_13' ),
    inference(resolution,[status(thm)],[c_4601,c_6737])).

tff(c_4589,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4582,c_309])).

tff(c_6749,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6746,c_4589])).

tff(c_6750,plain,(
    k2_zfmisc_1('#skF_15','#skF_16') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_8101,plain,(
    ! [E_716,F_717,A_718,B_719] :
      ( r2_hidden(k4_tarski(E_716,F_717),k2_zfmisc_1(A_718,B_719))
      | ~ r2_hidden(F_717,B_719)
      | ~ r2_hidden(E_716,A_718) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_8118,plain,(
    ! [E_720,F_721] :
      ( r2_hidden(k4_tarski(E_720,F_721),k1_xboole_0)
      | ~ r2_hidden(F_721,'#skF_16')
      | ~ r2_hidden(E_720,'#skF_15') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6750,c_8101])).

tff(c_8125,plain,(
    ! [F_721,E_720] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(F_721,'#skF_16')
      | ~ r2_hidden(E_720,'#skF_15') ) ),
    inference(resolution,[status(thm)],[c_8118,c_4])).

tff(c_8132,plain,(
    ! [F_721,E_720] :
      ( ~ r2_hidden(F_721,'#skF_16')
      | ~ r2_hidden(E_720,'#skF_15') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_8125])).

tff(c_8346,plain,(
    ! [E_734] : ~ r2_hidden(E_734,'#skF_15') ),
    inference(splitLeft,[status(thm)],[c_8132])).

tff(c_8370,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(resolution,[status(thm)],[c_24,c_8346])).

tff(c_8383,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_8370])).

tff(c_8385,plain,(
    ! [F_735] : ~ r2_hidden(F_735,'#skF_16') ),
    inference(splitRight,[status(thm)],[c_8132])).

tff(c_8409,plain,(
    k1_xboole_0 = '#skF_16' ),
    inference(resolution,[status(thm)],[c_24,c_8385])).

tff(c_8422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207,c_8409])).

tff(c_8424,plain,(
    k1_xboole_0 = '#skF_16' ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_120,plain,
    ( k1_xboole_0 = '#skF_14'
    | k1_xboole_0 = '#skF_13'
    | k1_xboole_0 != '#skF_16' ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_8543,plain,
    ( '#skF_16' = '#skF_14'
    | '#skF_16' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8424,c_8424,c_8424,c_120])).

tff(c_8544,plain,(
    '#skF_16' = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_8543])).

tff(c_8423,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_8455,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_16' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8424,c_8423])).

tff(c_8550,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8544,c_8455])).

tff(c_8531,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_4'(A_18),A_18)
      | A_18 = '#skF_16' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8424,c_24])).

tff(c_8545,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_4'(A_18),A_18)
      | A_18 = '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8544,c_8531])).

tff(c_76,plain,(
    ! [A_55,B_56,D_82] :
      ( r2_hidden('#skF_11'(A_55,B_56,k2_zfmisc_1(A_55,B_56),D_82),A_55)
      | ~ r2_hidden(D_82,k2_zfmisc_1(A_55,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_8434,plain,(
    v1_xboole_0('#skF_16') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8424,c_14])).

tff(c_8555,plain,(
    v1_xboole_0('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8544,c_8434])).

tff(c_10350,plain,(
    ! [A_889,B_890,D_891] :
      ( r2_hidden('#skF_12'(A_889,B_890,k2_zfmisc_1(A_889,B_890),D_891),B_890)
      | ~ r2_hidden(D_891,k2_zfmisc_1(A_889,B_890)) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_10389,plain,(
    ! [B_895,D_896,A_897] :
      ( ~ v1_xboole_0(B_895)
      | ~ r2_hidden(D_896,k2_zfmisc_1(A_897,B_895)) ) ),
    inference(resolution,[status(thm)],[c_10350,c_4])).

tff(c_10452,plain,(
    ! [B_900,A_901] :
      ( ~ v1_xboole_0(B_900)
      | k2_zfmisc_1(A_901,B_900) = '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_8545,c_10389])).

tff(c_10483,plain,(
    ! [A_906] : k2_zfmisc_1(A_906,'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_8555,c_10452])).

tff(c_10366,plain,(
    ! [B_890,D_891,A_889] :
      ( ~ v1_xboole_0(B_890)
      | ~ r2_hidden(D_891,k2_zfmisc_1(A_889,B_890)) ) ),
    inference(resolution,[status(thm)],[c_10350,c_4])).

tff(c_10491,plain,(
    ! [D_891] :
      ( ~ v1_xboole_0('#skF_13')
      | ~ r2_hidden(D_891,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10483,c_10366])).

tff(c_10512,plain,(
    ! [D_907] : ~ r2_hidden(D_907,'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8555,c_10491])).

tff(c_10588,plain,(
    ! [D_911,B_912] : ~ r2_hidden(D_911,k2_zfmisc_1('#skF_13',B_912)) ),
    inference(resolution,[status(thm)],[c_76,c_10512])).

tff(c_10645,plain,(
    ! [B_912] : k2_zfmisc_1('#skF_13',B_912) = '#skF_13' ),
    inference(resolution,[status(thm)],[c_8545,c_10588])).

tff(c_8557,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8544,c_8424])).

tff(c_8600,plain,
    ( k2_zfmisc_1('#skF_13','#skF_14') != '#skF_13'
    | k2_zfmisc_1('#skF_15','#skF_13') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8557,c_8544,c_8557,c_126])).

tff(c_8601,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_8600])).

tff(c_10702,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10645,c_8601])).

tff(c_10704,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_8600])).

tff(c_10717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8550,c_10704])).

tff(c_10718,plain,(
    '#skF_16' = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_8543])).

tff(c_10730,plain,(
    v1_xboole_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10718,c_8434])).

tff(c_10720,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_4'(A_18),A_18)
      | A_18 = '#skF_14' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10718,c_8531])).

tff(c_12300,plain,(
    ! [A_1043,B_1044,D_1045] :
      ( r2_hidden('#skF_12'(A_1043,B_1044,k2_zfmisc_1(A_1043,B_1044),D_1045),B_1044)
      | ~ r2_hidden(D_1045,k2_zfmisc_1(A_1043,B_1044)) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_12410,plain,(
    ! [B_1050,D_1051,A_1052] :
      ( ~ v1_xboole_0(B_1050)
      | ~ r2_hidden(D_1051,k2_zfmisc_1(A_1052,B_1050)) ) ),
    inference(resolution,[status(thm)],[c_12300,c_4])).

tff(c_12482,plain,(
    ! [B_1058,A_1059] :
      ( ~ v1_xboole_0(B_1058)
      | k2_zfmisc_1(A_1059,B_1058) = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_10720,c_12410])).

tff(c_12488,plain,(
    ! [A_1059] : k2_zfmisc_1(A_1059,'#skF_14') = '#skF_14' ),
    inference(resolution,[status(thm)],[c_10730,c_12482])).

tff(c_10725,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10718,c_8455])).

tff(c_12491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12488,c_10725])).

tff(c_12493,plain,(
    k1_xboole_0 = '#skF_15' ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_124,plain,
    ( k1_xboole_0 = '#skF_14'
    | k1_xboole_0 = '#skF_13'
    | k1_xboole_0 != '#skF_15' ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_12578,plain,
    ( '#skF_15' = '#skF_14'
    | '#skF_15' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12493,c_12493,c_12493,c_124])).

tff(c_12579,plain,(
    '#skF_15' = '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_12578])).

tff(c_12590,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12579,c_12493])).

tff(c_12657,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_4'(A_18),A_18)
      | A_18 = '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12590,c_24])).

tff(c_14481,plain,(
    ! [A_1228,B_1229,D_1230] :
      ( r2_hidden('#skF_11'(A_1228,B_1229,k2_zfmisc_1(A_1228,B_1229),D_1230),A_1228)
      | ~ r2_hidden(D_1230,k2_zfmisc_1(A_1228,B_1229)) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_12501,plain,(
    v1_xboole_0('#skF_15') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12493,c_14])).

tff(c_12589,plain,(
    v1_xboole_0('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12579,c_12501])).

tff(c_14298,plain,(
    ! [A_1209,B_1210,D_1211] :
      ( r2_hidden('#skF_12'(A_1209,B_1210,k2_zfmisc_1(A_1209,B_1210),D_1211),B_1210)
      | ~ r2_hidden(D_1211,k2_zfmisc_1(A_1209,B_1210)) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_14315,plain,(
    ! [B_1212,D_1213,A_1214] :
      ( ~ v1_xboole_0(B_1212)
      | ~ r2_hidden(D_1213,k2_zfmisc_1(A_1214,B_1212)) ) ),
    inference(resolution,[status(thm)],[c_14298,c_4])).

tff(c_14365,plain,(
    ! [B_1217,A_1218] :
      ( ~ v1_xboole_0(B_1217)
      | k2_zfmisc_1(A_1218,B_1217) = '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_12657,c_14315])).

tff(c_14390,plain,(
    ! [A_1223] : k2_zfmisc_1(A_1223,'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_12589,c_14365])).

tff(c_14314,plain,(
    ! [B_1210,D_1211,A_1209] :
      ( ~ v1_xboole_0(B_1210)
      | ~ r2_hidden(D_1211,k2_zfmisc_1(A_1209,B_1210)) ) ),
    inference(resolution,[status(thm)],[c_14298,c_4])).

tff(c_14398,plain,(
    ! [D_1211] :
      ( ~ v1_xboole_0('#skF_13')
      | ~ r2_hidden(D_1211,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14390,c_14314])).

tff(c_14411,plain,(
    ! [D_1211] : ~ r2_hidden(D_1211,'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12589,c_14398])).

tff(c_14508,plain,(
    ! [D_1231,B_1232] : ~ r2_hidden(D_1231,k2_zfmisc_1('#skF_13',B_1232)) ),
    inference(resolution,[status(thm)],[c_14481,c_14411])).

tff(c_14561,plain,(
    ! [B_1232] : k2_zfmisc_1('#skF_13',B_1232) = '#skF_13' ),
    inference(resolution,[status(thm)],[c_12657,c_14508])).

tff(c_12492,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_12508,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_15' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12493,c_12492])).

tff(c_12586,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12579,c_12508])).

tff(c_14579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14561,c_12586])).

tff(c_14580,plain,(
    '#skF_15' = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_12578])).

tff(c_14594,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14580,c_12493])).

tff(c_14665,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_4'(A_18),A_18)
      | A_18 = '#skF_14' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14594,c_24])).

tff(c_14593,plain,(
    v1_xboole_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14580,c_12501])).

tff(c_16303,plain,(
    ! [A_1375,B_1376,D_1377] :
      ( r2_hidden('#skF_11'(A_1375,B_1376,k2_zfmisc_1(A_1375,B_1376),D_1377),A_1375)
      | ~ r2_hidden(D_1377,k2_zfmisc_1(A_1375,B_1376)) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_16342,plain,(
    ! [A_1381,D_1382,B_1383] :
      ( ~ v1_xboole_0(A_1381)
      | ~ r2_hidden(D_1382,k2_zfmisc_1(A_1381,B_1383)) ) ),
    inference(resolution,[status(thm)],[c_16303,c_4])).

tff(c_16397,plain,(
    ! [A_1386,B_1387] :
      ( ~ v1_xboole_0(A_1386)
      | k2_zfmisc_1(A_1386,B_1387) = '#skF_14' ) ),
    inference(resolution,[status(thm)],[c_14665,c_16342])).

tff(c_16444,plain,(
    ! [B_1391] : k2_zfmisc_1('#skF_14',B_1391) = '#skF_14' ),
    inference(resolution,[status(thm)],[c_14593,c_16397])).

tff(c_16319,plain,(
    ! [A_1375,D_1377,B_1376] :
      ( ~ v1_xboole_0(A_1375)
      | ~ r2_hidden(D_1377,k2_zfmisc_1(A_1375,B_1376)) ) ),
    inference(resolution,[status(thm)],[c_16303,c_4])).

tff(c_16452,plain,(
    ! [D_1377] :
      ( ~ v1_xboole_0('#skF_14')
      | ~ r2_hidden(D_1377,'#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16444,c_16319])).

tff(c_16473,plain,(
    ! [D_1392] : ~ r2_hidden(D_1392,'#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14593,c_16452])).

tff(c_16551,plain,(
    ! [D_1396,A_1397] : ~ r2_hidden(D_1396,k2_zfmisc_1(A_1397,'#skF_14')) ),
    inference(resolution,[status(thm)],[c_74,c_16473])).

tff(c_16614,plain,(
    ! [A_1397] : k2_zfmisc_1(A_1397,'#skF_14') = '#skF_14' ),
    inference(resolution,[status(thm)],[c_14665,c_16551])).

tff(c_14590,plain,(
    k2_zfmisc_1('#skF_13','#skF_14') != '#skF_14' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14580,c_12508])).

tff(c_16633,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16614,c_14590])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.40/3.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.40/3.28  
% 9.40/3.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.40/3.28  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_15 > #skF_1 > #skF_12 > #skF_3 > #skF_16 > #skF_14 > #skF_13 > #skF_11 > #skF_7 > #skF_9 > #skF_2 > #skF_8 > #skF_5 > #skF_10
% 9.40/3.28  
% 9.40/3.28  %Foreground sorts:
% 9.40/3.28  
% 9.40/3.28  
% 9.40/3.28  %Background operators:
% 9.40/3.28  
% 9.40/3.28  
% 9.40/3.28  %Foreground operators:
% 9.40/3.28  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 9.40/3.28  tff('#skF_4', type, '#skF_4': $i > $i).
% 9.40/3.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.40/3.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.40/3.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.40/3.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.40/3.28  tff('#skF_15', type, '#skF_15': $i).
% 9.40/3.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.40/3.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.40/3.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.40/3.28  tff('#skF_12', type, '#skF_12': ($i * $i * $i * $i) > $i).
% 9.40/3.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.40/3.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.40/3.28  tff('#skF_16', type, '#skF_16': $i).
% 9.40/3.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.40/3.28  tff('#skF_14', type, '#skF_14': $i).
% 9.40/3.28  tff('#skF_13', type, '#skF_13': $i).
% 9.40/3.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.40/3.28  tff('#skF_11', type, '#skF_11': ($i * $i * $i * $i) > $i).
% 9.40/3.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.40/3.28  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 9.40/3.28  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 9.40/3.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.40/3.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.40/3.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.40/3.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.40/3.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.40/3.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.40/3.28  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 9.40/3.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.40/3.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.40/3.28  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.40/3.28  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 9.40/3.28  
% 9.40/3.31  tff(f_185, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.40/3.31  tff(f_71, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 9.40/3.31  tff(f_41, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.40/3.31  tff(f_146, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 9.40/3.31  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.40/3.31  tff(c_118, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!=k1_xboole_0 | k1_xboole_0!='#skF_16'), inference(cnfTransformation, [status(thm)], [f_185])).
% 9.40/3.31  tff(c_207, plain, (k1_xboole_0!='#skF_16'), inference(splitLeft, [status(thm)], [c_118])).
% 9.40/3.31  tff(c_24, plain, (![A_18]: (r2_hidden('#skF_4'(A_18), A_18) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.40/3.31  tff(c_122, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!=k1_xboole_0 | k1_xboole_0!='#skF_15'), inference(cnfTransformation, [status(thm)], [f_185])).
% 9.40/3.31  tff(c_178, plain, (k1_xboole_0!='#skF_15'), inference(splitLeft, [status(thm)], [c_122])).
% 9.40/3.31  tff(c_14, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.40/3.31  tff(c_128, plain, (k1_xboole_0='#skF_14' | k1_xboole_0='#skF_13' | k2_zfmisc_1('#skF_15', '#skF_16')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_185])).
% 9.40/3.31  tff(c_403, plain, (k2_zfmisc_1('#skF_15', '#skF_16')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_128])).
% 9.40/3.31  tff(c_1826, plain, (![E_245, F_246, A_247, B_248]: (r2_hidden(k4_tarski(E_245, F_246), k2_zfmisc_1(A_247, B_248)) | ~r2_hidden(F_246, B_248) | ~r2_hidden(E_245, A_247))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.40/3.31  tff(c_1984, plain, (![E_257, F_258]: (r2_hidden(k4_tarski(E_257, F_258), k1_xboole_0) | ~r2_hidden(F_258, '#skF_16') | ~r2_hidden(E_257, '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_403, c_1826])).
% 9.40/3.31  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.40/3.31  tff(c_1991, plain, (![F_258, E_257]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(F_258, '#skF_16') | ~r2_hidden(E_257, '#skF_15'))), inference(resolution, [status(thm)], [c_1984, c_4])).
% 9.40/3.31  tff(c_1998, plain, (![F_258, E_257]: (~r2_hidden(F_258, '#skF_16') | ~r2_hidden(E_257, '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1991])).
% 9.40/3.31  tff(c_2056, plain, (![E_261]: (~r2_hidden(E_261, '#skF_15'))), inference(splitLeft, [status(thm)], [c_1998])).
% 9.40/3.31  tff(c_2084, plain, (k1_xboole_0='#skF_15'), inference(resolution, [status(thm)], [c_24, c_2056])).
% 9.40/3.31  tff(c_2098, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_2084])).
% 9.40/3.31  tff(c_2100, plain, (![F_262]: (~r2_hidden(F_262, '#skF_16'))), inference(splitRight, [status(thm)], [c_1998])).
% 9.40/3.31  tff(c_2128, plain, (k1_xboole_0='#skF_16'), inference(resolution, [status(thm)], [c_24, c_2100])).
% 9.40/3.31  tff(c_2142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_207, c_2128])).
% 9.40/3.31  tff(c_2143, plain, (k1_xboole_0='#skF_13' | k1_xboole_0='#skF_14'), inference(splitRight, [status(thm)], [c_128])).
% 9.40/3.31  tff(c_2145, plain, (k1_xboole_0='#skF_14'), inference(splitLeft, [status(thm)], [c_2143])).
% 9.40/3.31  tff(c_2150, plain, (![A_18]: (r2_hidden('#skF_4'(A_18), A_18) | A_18='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_2145, c_24])).
% 9.40/3.31  tff(c_74, plain, (![A_55, B_56, D_82]: (r2_hidden('#skF_12'(A_55, B_56, k2_zfmisc_1(A_55, B_56), D_82), B_56) | ~r2_hidden(D_82, k2_zfmisc_1(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.40/3.31  tff(c_2161, plain, (v1_xboole_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_2145, c_14])).
% 9.40/3.31  tff(c_3952, plain, (![A_397, B_398, D_399]: (r2_hidden('#skF_11'(A_397, B_398, k2_zfmisc_1(A_397, B_398), D_399), A_397) | ~r2_hidden(D_399, k2_zfmisc_1(A_397, B_398)))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.40/3.31  tff(c_4255, plain, (![A_422, D_423, B_424]: (~v1_xboole_0(A_422) | ~r2_hidden(D_423, k2_zfmisc_1(A_422, B_424)))), inference(resolution, [status(thm)], [c_3952, c_4])).
% 9.40/3.31  tff(c_4368, plain, (![A_430, B_431]: (~v1_xboole_0(A_430) | k2_zfmisc_1(A_430, B_431)='#skF_14')), inference(resolution, [status(thm)], [c_2150, c_4255])).
% 9.40/3.31  tff(c_4378, plain, (![B_432]: (k2_zfmisc_1('#skF_14', B_432)='#skF_14')), inference(resolution, [status(thm)], [c_2161, c_4368])).
% 9.40/3.31  tff(c_3968, plain, (![A_397, D_399, B_398]: (~v1_xboole_0(A_397) | ~r2_hidden(D_399, k2_zfmisc_1(A_397, B_398)))), inference(resolution, [status(thm)], [c_3952, c_4])).
% 9.40/3.31  tff(c_4386, plain, (![D_399]: (~v1_xboole_0('#skF_14') | ~r2_hidden(D_399, '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_4378, c_3968])).
% 9.40/3.31  tff(c_4407, plain, (![D_433]: (~r2_hidden(D_433, '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_2161, c_4386])).
% 9.40/3.31  tff(c_4499, plain, (![D_440, A_441]: (~r2_hidden(D_440, k2_zfmisc_1(A_441, '#skF_14')))), inference(resolution, [status(thm)], [c_74, c_4407])).
% 9.40/3.31  tff(c_4576, plain, (![A_441]: (k2_zfmisc_1(A_441, '#skF_14')='#skF_14')), inference(resolution, [status(thm)], [c_2150, c_4499])).
% 9.40/3.31  tff(c_126, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!=k1_xboole_0 | k2_zfmisc_1('#skF_15', '#skF_16')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_185])).
% 9.40/3.31  tff(c_309, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_126])).
% 9.40/3.31  tff(c_2149, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_2145, c_309])).
% 9.40/3.31  tff(c_4581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4576, c_2149])).
% 9.40/3.31  tff(c_4582, plain, (k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_2143])).
% 9.40/3.31  tff(c_4601, plain, (v1_xboole_0('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_4582, c_14])).
% 9.40/3.31  tff(c_4590, plain, (![A_18]: (r2_hidden('#skF_4'(A_18), A_18) | A_18='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_4582, c_24])).
% 9.40/3.31  tff(c_6532, plain, (![A_597, B_598, D_599]: (r2_hidden('#skF_11'(A_597, B_598, k2_zfmisc_1(A_597, B_598), D_599), A_597) | ~r2_hidden(D_599, k2_zfmisc_1(A_597, B_598)))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.40/3.31  tff(c_6657, plain, (![A_610, D_611, B_612]: (~v1_xboole_0(A_610) | ~r2_hidden(D_611, k2_zfmisc_1(A_610, B_612)))), inference(resolution, [status(thm)], [c_6532, c_4])).
% 9.40/3.31  tff(c_6737, plain, (![A_618, B_619]: (~v1_xboole_0(A_618) | k2_zfmisc_1(A_618, B_619)='#skF_13')), inference(resolution, [status(thm)], [c_4590, c_6657])).
% 9.40/3.31  tff(c_6746, plain, (![B_619]: (k2_zfmisc_1('#skF_13', B_619)='#skF_13')), inference(resolution, [status(thm)], [c_4601, c_6737])).
% 9.40/3.31  tff(c_4589, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_4582, c_309])).
% 9.40/3.31  tff(c_6749, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6746, c_4589])).
% 9.40/3.31  tff(c_6750, plain, (k2_zfmisc_1('#skF_15', '#skF_16')=k1_xboole_0), inference(splitRight, [status(thm)], [c_126])).
% 9.40/3.31  tff(c_8101, plain, (![E_716, F_717, A_718, B_719]: (r2_hidden(k4_tarski(E_716, F_717), k2_zfmisc_1(A_718, B_719)) | ~r2_hidden(F_717, B_719) | ~r2_hidden(E_716, A_718))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.40/3.31  tff(c_8118, plain, (![E_720, F_721]: (r2_hidden(k4_tarski(E_720, F_721), k1_xboole_0) | ~r2_hidden(F_721, '#skF_16') | ~r2_hidden(E_720, '#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_6750, c_8101])).
% 9.40/3.31  tff(c_8125, plain, (![F_721, E_720]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(F_721, '#skF_16') | ~r2_hidden(E_720, '#skF_15'))), inference(resolution, [status(thm)], [c_8118, c_4])).
% 9.40/3.31  tff(c_8132, plain, (![F_721, E_720]: (~r2_hidden(F_721, '#skF_16') | ~r2_hidden(E_720, '#skF_15'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_8125])).
% 9.40/3.31  tff(c_8346, plain, (![E_734]: (~r2_hidden(E_734, '#skF_15'))), inference(splitLeft, [status(thm)], [c_8132])).
% 9.40/3.31  tff(c_8370, plain, (k1_xboole_0='#skF_15'), inference(resolution, [status(thm)], [c_24, c_8346])).
% 9.40/3.31  tff(c_8383, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_8370])).
% 9.40/3.31  tff(c_8385, plain, (![F_735]: (~r2_hidden(F_735, '#skF_16'))), inference(splitRight, [status(thm)], [c_8132])).
% 9.40/3.31  tff(c_8409, plain, (k1_xboole_0='#skF_16'), inference(resolution, [status(thm)], [c_24, c_8385])).
% 9.40/3.31  tff(c_8422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_207, c_8409])).
% 9.40/3.31  tff(c_8424, plain, (k1_xboole_0='#skF_16'), inference(splitRight, [status(thm)], [c_118])).
% 9.40/3.31  tff(c_120, plain, (k1_xboole_0='#skF_14' | k1_xboole_0='#skF_13' | k1_xboole_0!='#skF_16'), inference(cnfTransformation, [status(thm)], [f_185])).
% 9.40/3.31  tff(c_8543, plain, ('#skF_16'='#skF_14' | '#skF_16'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_8424, c_8424, c_8424, c_120])).
% 9.40/3.31  tff(c_8544, plain, ('#skF_16'='#skF_13'), inference(splitLeft, [status(thm)], [c_8543])).
% 9.40/3.31  tff(c_8423, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_118])).
% 9.40/3.31  tff(c_8455, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_16'), inference(demodulation, [status(thm), theory('equality')], [c_8424, c_8423])).
% 9.40/3.31  tff(c_8550, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_8544, c_8455])).
% 9.40/3.31  tff(c_8531, plain, (![A_18]: (r2_hidden('#skF_4'(A_18), A_18) | A_18='#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_8424, c_24])).
% 9.40/3.31  tff(c_8545, plain, (![A_18]: (r2_hidden('#skF_4'(A_18), A_18) | A_18='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_8544, c_8531])).
% 9.40/3.31  tff(c_76, plain, (![A_55, B_56, D_82]: (r2_hidden('#skF_11'(A_55, B_56, k2_zfmisc_1(A_55, B_56), D_82), A_55) | ~r2_hidden(D_82, k2_zfmisc_1(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.40/3.31  tff(c_8434, plain, (v1_xboole_0('#skF_16')), inference(demodulation, [status(thm), theory('equality')], [c_8424, c_14])).
% 9.40/3.31  tff(c_8555, plain, (v1_xboole_0('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_8544, c_8434])).
% 9.40/3.31  tff(c_10350, plain, (![A_889, B_890, D_891]: (r2_hidden('#skF_12'(A_889, B_890, k2_zfmisc_1(A_889, B_890), D_891), B_890) | ~r2_hidden(D_891, k2_zfmisc_1(A_889, B_890)))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.40/3.31  tff(c_10389, plain, (![B_895, D_896, A_897]: (~v1_xboole_0(B_895) | ~r2_hidden(D_896, k2_zfmisc_1(A_897, B_895)))), inference(resolution, [status(thm)], [c_10350, c_4])).
% 9.40/3.31  tff(c_10452, plain, (![B_900, A_901]: (~v1_xboole_0(B_900) | k2_zfmisc_1(A_901, B_900)='#skF_13')), inference(resolution, [status(thm)], [c_8545, c_10389])).
% 9.40/3.31  tff(c_10483, plain, (![A_906]: (k2_zfmisc_1(A_906, '#skF_13')='#skF_13')), inference(resolution, [status(thm)], [c_8555, c_10452])).
% 9.40/3.31  tff(c_10366, plain, (![B_890, D_891, A_889]: (~v1_xboole_0(B_890) | ~r2_hidden(D_891, k2_zfmisc_1(A_889, B_890)))), inference(resolution, [status(thm)], [c_10350, c_4])).
% 9.40/3.31  tff(c_10491, plain, (![D_891]: (~v1_xboole_0('#skF_13') | ~r2_hidden(D_891, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_10483, c_10366])).
% 9.40/3.31  tff(c_10512, plain, (![D_907]: (~r2_hidden(D_907, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_8555, c_10491])).
% 9.40/3.31  tff(c_10588, plain, (![D_911, B_912]: (~r2_hidden(D_911, k2_zfmisc_1('#skF_13', B_912)))), inference(resolution, [status(thm)], [c_76, c_10512])).
% 9.40/3.31  tff(c_10645, plain, (![B_912]: (k2_zfmisc_1('#skF_13', B_912)='#skF_13')), inference(resolution, [status(thm)], [c_8545, c_10588])).
% 9.40/3.31  tff(c_8557, plain, (k1_xboole_0='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_8544, c_8424])).
% 9.40/3.31  tff(c_8600, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_13' | k2_zfmisc_1('#skF_15', '#skF_13')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_8557, c_8544, c_8557, c_126])).
% 9.40/3.31  tff(c_8601, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_13'), inference(splitLeft, [status(thm)], [c_8600])).
% 9.40/3.31  tff(c_10702, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10645, c_8601])).
% 9.40/3.31  tff(c_10704, plain, (k2_zfmisc_1('#skF_13', '#skF_14')='#skF_13'), inference(splitRight, [status(thm)], [c_8600])).
% 9.40/3.31  tff(c_10717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8550, c_10704])).
% 9.40/3.31  tff(c_10718, plain, ('#skF_16'='#skF_14'), inference(splitRight, [status(thm)], [c_8543])).
% 9.40/3.31  tff(c_10730, plain, (v1_xboole_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_10718, c_8434])).
% 9.40/3.31  tff(c_10720, plain, (![A_18]: (r2_hidden('#skF_4'(A_18), A_18) | A_18='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_10718, c_8531])).
% 9.40/3.31  tff(c_12300, plain, (![A_1043, B_1044, D_1045]: (r2_hidden('#skF_12'(A_1043, B_1044, k2_zfmisc_1(A_1043, B_1044), D_1045), B_1044) | ~r2_hidden(D_1045, k2_zfmisc_1(A_1043, B_1044)))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.40/3.31  tff(c_12410, plain, (![B_1050, D_1051, A_1052]: (~v1_xboole_0(B_1050) | ~r2_hidden(D_1051, k2_zfmisc_1(A_1052, B_1050)))), inference(resolution, [status(thm)], [c_12300, c_4])).
% 9.40/3.31  tff(c_12482, plain, (![B_1058, A_1059]: (~v1_xboole_0(B_1058) | k2_zfmisc_1(A_1059, B_1058)='#skF_14')), inference(resolution, [status(thm)], [c_10720, c_12410])).
% 9.40/3.31  tff(c_12488, plain, (![A_1059]: (k2_zfmisc_1(A_1059, '#skF_14')='#skF_14')), inference(resolution, [status(thm)], [c_10730, c_12482])).
% 9.40/3.31  tff(c_10725, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_10718, c_8455])).
% 9.40/3.31  tff(c_12491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12488, c_10725])).
% 9.40/3.31  tff(c_12493, plain, (k1_xboole_0='#skF_15'), inference(splitRight, [status(thm)], [c_122])).
% 9.40/3.31  tff(c_124, plain, (k1_xboole_0='#skF_14' | k1_xboole_0='#skF_13' | k1_xboole_0!='#skF_15'), inference(cnfTransformation, [status(thm)], [f_185])).
% 9.40/3.31  tff(c_12578, plain, ('#skF_15'='#skF_14' | '#skF_15'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_12493, c_12493, c_12493, c_124])).
% 9.40/3.31  tff(c_12579, plain, ('#skF_15'='#skF_13'), inference(splitLeft, [status(thm)], [c_12578])).
% 9.40/3.31  tff(c_12590, plain, (k1_xboole_0='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_12579, c_12493])).
% 9.40/3.31  tff(c_12657, plain, (![A_18]: (r2_hidden('#skF_4'(A_18), A_18) | A_18='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_12590, c_24])).
% 9.40/3.31  tff(c_14481, plain, (![A_1228, B_1229, D_1230]: (r2_hidden('#skF_11'(A_1228, B_1229, k2_zfmisc_1(A_1228, B_1229), D_1230), A_1228) | ~r2_hidden(D_1230, k2_zfmisc_1(A_1228, B_1229)))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.40/3.31  tff(c_12501, plain, (v1_xboole_0('#skF_15')), inference(demodulation, [status(thm), theory('equality')], [c_12493, c_14])).
% 9.40/3.31  tff(c_12589, plain, (v1_xboole_0('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_12579, c_12501])).
% 9.40/3.31  tff(c_14298, plain, (![A_1209, B_1210, D_1211]: (r2_hidden('#skF_12'(A_1209, B_1210, k2_zfmisc_1(A_1209, B_1210), D_1211), B_1210) | ~r2_hidden(D_1211, k2_zfmisc_1(A_1209, B_1210)))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.40/3.31  tff(c_14315, plain, (![B_1212, D_1213, A_1214]: (~v1_xboole_0(B_1212) | ~r2_hidden(D_1213, k2_zfmisc_1(A_1214, B_1212)))), inference(resolution, [status(thm)], [c_14298, c_4])).
% 9.40/3.31  tff(c_14365, plain, (![B_1217, A_1218]: (~v1_xboole_0(B_1217) | k2_zfmisc_1(A_1218, B_1217)='#skF_13')), inference(resolution, [status(thm)], [c_12657, c_14315])).
% 9.40/3.31  tff(c_14390, plain, (![A_1223]: (k2_zfmisc_1(A_1223, '#skF_13')='#skF_13')), inference(resolution, [status(thm)], [c_12589, c_14365])).
% 9.40/3.31  tff(c_14314, plain, (![B_1210, D_1211, A_1209]: (~v1_xboole_0(B_1210) | ~r2_hidden(D_1211, k2_zfmisc_1(A_1209, B_1210)))), inference(resolution, [status(thm)], [c_14298, c_4])).
% 9.40/3.31  tff(c_14398, plain, (![D_1211]: (~v1_xboole_0('#skF_13') | ~r2_hidden(D_1211, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_14390, c_14314])).
% 9.40/3.31  tff(c_14411, plain, (![D_1211]: (~r2_hidden(D_1211, '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_12589, c_14398])).
% 9.40/3.31  tff(c_14508, plain, (![D_1231, B_1232]: (~r2_hidden(D_1231, k2_zfmisc_1('#skF_13', B_1232)))), inference(resolution, [status(thm)], [c_14481, c_14411])).
% 9.40/3.31  tff(c_14561, plain, (![B_1232]: (k2_zfmisc_1('#skF_13', B_1232)='#skF_13')), inference(resolution, [status(thm)], [c_12657, c_14508])).
% 9.40/3.31  tff(c_12492, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_122])).
% 9.40/3.31  tff(c_12508, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_15'), inference(demodulation, [status(thm), theory('equality')], [c_12493, c_12492])).
% 9.40/3.31  tff(c_12586, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_12579, c_12508])).
% 9.40/3.31  tff(c_14579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14561, c_12586])).
% 9.40/3.31  tff(c_14580, plain, ('#skF_15'='#skF_14'), inference(splitRight, [status(thm)], [c_12578])).
% 9.40/3.31  tff(c_14594, plain, (k1_xboole_0='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_14580, c_12493])).
% 9.40/3.31  tff(c_14665, plain, (![A_18]: (r2_hidden('#skF_4'(A_18), A_18) | A_18='#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_14594, c_24])).
% 9.40/3.31  tff(c_14593, plain, (v1_xboole_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_14580, c_12501])).
% 9.40/3.31  tff(c_16303, plain, (![A_1375, B_1376, D_1377]: (r2_hidden('#skF_11'(A_1375, B_1376, k2_zfmisc_1(A_1375, B_1376), D_1377), A_1375) | ~r2_hidden(D_1377, k2_zfmisc_1(A_1375, B_1376)))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.40/3.31  tff(c_16342, plain, (![A_1381, D_1382, B_1383]: (~v1_xboole_0(A_1381) | ~r2_hidden(D_1382, k2_zfmisc_1(A_1381, B_1383)))), inference(resolution, [status(thm)], [c_16303, c_4])).
% 9.40/3.31  tff(c_16397, plain, (![A_1386, B_1387]: (~v1_xboole_0(A_1386) | k2_zfmisc_1(A_1386, B_1387)='#skF_14')), inference(resolution, [status(thm)], [c_14665, c_16342])).
% 9.40/3.31  tff(c_16444, plain, (![B_1391]: (k2_zfmisc_1('#skF_14', B_1391)='#skF_14')), inference(resolution, [status(thm)], [c_14593, c_16397])).
% 9.40/3.31  tff(c_16319, plain, (![A_1375, D_1377, B_1376]: (~v1_xboole_0(A_1375) | ~r2_hidden(D_1377, k2_zfmisc_1(A_1375, B_1376)))), inference(resolution, [status(thm)], [c_16303, c_4])).
% 9.40/3.31  tff(c_16452, plain, (![D_1377]: (~v1_xboole_0('#skF_14') | ~r2_hidden(D_1377, '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_16444, c_16319])).
% 9.40/3.31  tff(c_16473, plain, (![D_1392]: (~r2_hidden(D_1392, '#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_14593, c_16452])).
% 9.40/3.31  tff(c_16551, plain, (![D_1396, A_1397]: (~r2_hidden(D_1396, k2_zfmisc_1(A_1397, '#skF_14')))), inference(resolution, [status(thm)], [c_74, c_16473])).
% 9.40/3.31  tff(c_16614, plain, (![A_1397]: (k2_zfmisc_1(A_1397, '#skF_14')='#skF_14')), inference(resolution, [status(thm)], [c_14665, c_16551])).
% 9.40/3.31  tff(c_14590, plain, (k2_zfmisc_1('#skF_13', '#skF_14')!='#skF_14'), inference(demodulation, [status(thm), theory('equality')], [c_14580, c_12508])).
% 9.40/3.31  tff(c_16633, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16614, c_14590])).
% 9.40/3.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.40/3.31  
% 9.40/3.31  Inference rules
% 9.40/3.31  ----------------------
% 9.40/3.31  #Ref     : 0
% 9.40/3.31  #Sup     : 3733
% 9.40/3.31  #Fact    : 0
% 9.40/3.31  #Define  : 0
% 9.40/3.31  #Split   : 13
% 9.40/3.31  #Chain   : 0
% 9.40/3.31  #Close   : 0
% 9.40/3.31  
% 9.40/3.31  Ordering : KBO
% 9.40/3.31  
% 9.40/3.31  Simplification rules
% 9.40/3.31  ----------------------
% 9.40/3.31  #Subsume      : 480
% 9.40/3.31  #Demod        : 2274
% 9.40/3.31  #Tautology    : 1886
% 9.40/3.31  #SimpNegUnit  : 89
% 9.40/3.31  #BackRed      : 210
% 9.40/3.31  
% 9.40/3.31  #Partial instantiations: 0
% 9.40/3.31  #Strategies tried      : 1
% 9.40/3.31  
% 9.40/3.31  Timing (in seconds)
% 9.40/3.31  ----------------------
% 9.40/3.31  Preprocessing        : 0.42
% 9.40/3.31  Parsing              : 0.19
% 9.40/3.31  CNF conversion       : 0.04
% 9.40/3.31  Main loop            : 2.10
% 9.40/3.31  Inferencing          : 0.70
% 9.40/3.31  Reduction            : 0.80
% 9.40/3.31  Demodulation         : 0.62
% 9.40/3.31  BG Simplification    : 0.08
% 9.40/3.31  Subsumption          : 0.35
% 9.40/3.31  Abstraction          : 0.09
% 9.40/3.31  MUC search           : 0.00
% 9.40/3.31  Cooper               : 0.00
% 9.40/3.31  Total                : 2.57
% 9.40/3.31  Index Insertion      : 0.00
% 9.40/3.31  Index Deletion       : 0.00
% 9.40/3.31  Index Matching       : 0.00
% 9.40/3.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
