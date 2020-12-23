%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:02 EST 2020

% Result     : Theorem 5.61s
% Output     : CNFRefutation 5.69s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 785 expanded)
%              Number of leaves         :   36 ( 287 expanded)
%              Depth                    :   13
%              Number of atoms          :  160 (2391 expanded)
%              Number of equality atoms :   51 ( 955 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2235,plain,(
    ! [C_270,A_271,B_272] :
      ( v1_relat_1(C_270)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_271,B_272))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2244,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_2235])).

tff(c_18,plain,(
    ! [A_13] :
      ( k9_relat_1(A_13,k1_relat_1(A_13)) = k2_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2526,plain,(
    ! [A_326,B_327,C_328] :
      ( r2_hidden(k4_tarski('#skF_2'(A_326,B_327,C_328),A_326),C_328)
      | ~ r2_hidden(A_326,k9_relat_1(C_328,B_327))
      | ~ v1_relat_1(C_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2585,plain,(
    ! [C_329,A_330,B_331] :
      ( ~ v1_xboole_0(C_329)
      | ~ r2_hidden(A_330,k9_relat_1(C_329,B_331))
      | ~ v1_relat_1(C_329) ) ),
    inference(resolution,[status(thm)],[c_2526,c_2])).

tff(c_2609,plain,(
    ! [C_332,B_333] :
      ( ~ v1_xboole_0(C_332)
      | ~ v1_relat_1(C_332)
      | v1_xboole_0(k9_relat_1(C_332,B_333)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2585])).

tff(c_2618,plain,(
    ! [A_334] :
      ( ~ v1_xboole_0(A_334)
      | ~ v1_relat_1(A_334)
      | v1_xboole_0(k2_relat_1(A_334))
      | ~ v1_relat_1(A_334) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2609])).

tff(c_2265,plain,(
    ! [A_279,B_280,C_281] :
      ( k2_relset_1(A_279,B_280,C_281) = k2_relat_1(C_281)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(A_279,B_280))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2274,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_2265])).

tff(c_50,plain,(
    r2_hidden('#skF_3',k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_74,plain,(
    ~ v1_xboole_0(k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_2276,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2274,c_74])).

tff(c_2621,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2618,c_2276])).

tff(c_2627,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2244,c_2621])).

tff(c_2277,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2274,c_50])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2250,plain,(
    ! [A_275,B_276,C_277] :
      ( k1_relset_1(A_275,B_276,C_277) = k1_relat_1(C_277)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(k2_zfmisc_1(A_275,B_276))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2259,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_2250])).

tff(c_3036,plain,(
    ! [B_383,A_384,C_385] :
      ( k1_xboole_0 = B_383
      | k1_relset_1(A_384,B_383,C_385) = A_384
      | ~ v1_funct_2(C_385,A_384,B_383)
      | ~ m1_subset_1(C_385,k1_zfmisc_1(k2_zfmisc_1(A_384,B_383))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3043,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_3036])).

tff(c_3047,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2259,c_3043])).

tff(c_3048,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3047])).

tff(c_3063,plain,
    ( k9_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3048,c_18])).

tff(c_3073,plain,(
    k9_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2244,c_3063])).

tff(c_2292,plain,(
    ! [A_285,B_286,C_287] :
      ( r2_hidden('#skF_2'(A_285,B_286,C_287),B_286)
      | ~ r2_hidden(A_285,k9_relat_1(C_287,B_286))
      | ~ v1_relat_1(C_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2299,plain,(
    ! [A_285,B_286,C_287] :
      ( m1_subset_1('#skF_2'(A_285,B_286,C_287),B_286)
      | ~ r2_hidden(A_285,k9_relat_1(C_287,B_286))
      | ~ v1_relat_1(C_287) ) ),
    inference(resolution,[status(thm)],[c_2292,c_8])).

tff(c_3093,plain,(
    ! [A_285] :
      ( m1_subset_1('#skF_2'(A_285,'#skF_4','#skF_6'),'#skF_4')
      | ~ r2_hidden(A_285,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3073,c_2299])).

tff(c_3152,plain,(
    ! [A_389] :
      ( m1_subset_1('#skF_2'(A_389,'#skF_4','#skF_6'),'#skF_4')
      | ~ r2_hidden(A_389,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2244,c_3093])).

tff(c_3175,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2277,c_3152])).

tff(c_48,plain,(
    ! [E_30] :
      ( k1_funct_1('#skF_6',E_30) != '#skF_3'
      | ~ m1_subset_1(E_30,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_3182,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_6')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_3175,c_48])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_26,plain,(
    ! [C_16,A_14,B_15] :
      ( k1_funct_1(C_16,A_14) = B_15
      | ~ r2_hidden(k4_tarski(A_14,B_15),C_16)
      | ~ v1_funct_1(C_16)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3998,plain,(
    ! [C_465,A_466,B_467] :
      ( k1_funct_1(C_465,'#skF_2'(A_466,B_467,C_465)) = A_466
      | ~ v1_funct_1(C_465)
      | ~ r2_hidden(A_466,k9_relat_1(C_465,B_467))
      | ~ v1_relat_1(C_465) ) ),
    inference(resolution,[status(thm)],[c_2526,c_26])).

tff(c_4002,plain,(
    ! [A_466] :
      ( k1_funct_1('#skF_6','#skF_2'(A_466,'#skF_4','#skF_6')) = A_466
      | ~ v1_funct_1('#skF_6')
      | ~ r2_hidden(A_466,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3073,c_3998])).

tff(c_4028,plain,(
    ! [A_468] :
      ( k1_funct_1('#skF_6','#skF_2'(A_468,'#skF_4','#skF_6')) = A_468
      | ~ r2_hidden(A_468,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2244,c_56,c_4002])).

tff(c_4043,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_6')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2277,c_4028])).

tff(c_4054,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3182,c_4043])).

tff(c_4056,plain,(
    k1_relat_1('#skF_6') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3047])).

tff(c_4055,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3047])).

tff(c_38,plain,(
    ! [C_28,A_26] :
      ( k1_xboole_0 = C_28
      | ~ v1_funct_2(C_28,A_26,k1_xboole_0)
      | k1_xboole_0 = A_26
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4510,plain,(
    ! [C_498,A_499] :
      ( C_498 = '#skF_5'
      | ~ v1_funct_2(C_498,A_499,'#skF_5')
      | A_499 = '#skF_5'
      | ~ m1_subset_1(C_498,k1_zfmisc_1(k2_zfmisc_1(A_499,'#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4055,c_4055,c_4055,c_4055,c_38])).

tff(c_4517,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_4510])).

tff(c_4521,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4517])).

tff(c_4522,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4521])).

tff(c_4543,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4522,c_54])).

tff(c_4542,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4522,c_52])).

tff(c_44,plain,(
    ! [B_27,C_28] :
      ( k1_relset_1(k1_xboole_0,B_27,C_28) = k1_xboole_0
      | ~ v1_funct_2(C_28,k1_xboole_0,B_27)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4058,plain,(
    ! [B_27,C_28] :
      ( k1_relset_1('#skF_5',B_27,C_28) = '#skF_5'
      | ~ v1_funct_2(C_28,'#skF_5',B_27)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_27))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4055,c_4055,c_4055,c_4055,c_44])).

tff(c_4811,plain,(
    ! [B_507,C_508] :
      ( k1_relset_1('#skF_4',B_507,C_508) = '#skF_4'
      | ~ v1_funct_2(C_508,'#skF_4',B_507)
      | ~ m1_subset_1(C_508,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_507))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4522,c_4522,c_4522,c_4522,c_4058])).

tff(c_4814,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_4542,c_4811])).

tff(c_4825,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4543,c_4814])).

tff(c_4541,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4522,c_2259])).

tff(c_4836,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4825,c_4541])).

tff(c_4837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4056,c_4836])).

tff(c_4838,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4521])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4077,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4055,c_6])).

tff(c_4854,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4838,c_4077])).

tff(c_4862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2627,c_4854])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:32:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.61/2.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.69/2.08  
% 5.69/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.69/2.08  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 5.69/2.08  
% 5.69/2.08  %Foreground sorts:
% 5.69/2.08  
% 5.69/2.08  
% 5.69/2.08  %Background operators:
% 5.69/2.08  
% 5.69/2.08  
% 5.69/2.08  %Foreground operators:
% 5.69/2.08  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.69/2.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.69/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.69/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.69/2.08  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.69/2.08  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.69/2.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.69/2.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.69/2.08  tff('#skF_5', type, '#skF_5': $i).
% 5.69/2.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.69/2.08  tff('#skF_6', type, '#skF_6': $i).
% 5.69/2.08  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.69/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.69/2.08  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.69/2.08  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.69/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.69/2.08  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.69/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.69/2.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.69/2.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.69/2.08  tff('#skF_4', type, '#skF_4': $i).
% 5.69/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.69/2.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.69/2.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.69/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.69/2.08  
% 5.69/2.10  tff(f_110, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 5.69/2.10  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.69/2.10  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 5.69/2.10  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.69/2.10  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 5.69/2.10  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.69/2.10  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.69/2.10  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.69/2.10  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 5.69/2.10  tff(f_64, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 5.69/2.10  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.69/2.10  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.69/2.10  tff(c_2235, plain, (![C_270, A_271, B_272]: (v1_relat_1(C_270) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.69/2.10  tff(c_2244, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_2235])).
% 5.69/2.10  tff(c_18, plain, (![A_13]: (k9_relat_1(A_13, k1_relat_1(A_13))=k2_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.69/2.10  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.69/2.10  tff(c_2526, plain, (![A_326, B_327, C_328]: (r2_hidden(k4_tarski('#skF_2'(A_326, B_327, C_328), A_326), C_328) | ~r2_hidden(A_326, k9_relat_1(C_328, B_327)) | ~v1_relat_1(C_328))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.69/2.10  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.69/2.10  tff(c_2585, plain, (![C_329, A_330, B_331]: (~v1_xboole_0(C_329) | ~r2_hidden(A_330, k9_relat_1(C_329, B_331)) | ~v1_relat_1(C_329))), inference(resolution, [status(thm)], [c_2526, c_2])).
% 5.69/2.10  tff(c_2609, plain, (![C_332, B_333]: (~v1_xboole_0(C_332) | ~v1_relat_1(C_332) | v1_xboole_0(k9_relat_1(C_332, B_333)))), inference(resolution, [status(thm)], [c_4, c_2585])).
% 5.69/2.10  tff(c_2618, plain, (![A_334]: (~v1_xboole_0(A_334) | ~v1_relat_1(A_334) | v1_xboole_0(k2_relat_1(A_334)) | ~v1_relat_1(A_334))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2609])).
% 5.69/2.10  tff(c_2265, plain, (![A_279, B_280, C_281]: (k2_relset_1(A_279, B_280, C_281)=k2_relat_1(C_281) | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(A_279, B_280))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.69/2.10  tff(c_2274, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_2265])).
% 5.69/2.10  tff(c_50, plain, (r2_hidden('#skF_3', k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.69/2.10  tff(c_74, plain, (~v1_xboole_0(k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_50, c_2])).
% 5.69/2.10  tff(c_2276, plain, (~v1_xboole_0(k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2274, c_74])).
% 5.69/2.10  tff(c_2621, plain, (~v1_xboole_0('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2618, c_2276])).
% 5.69/2.10  tff(c_2627, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2244, c_2621])).
% 5.69/2.10  tff(c_2277, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2274, c_50])).
% 5.69/2.10  tff(c_54, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.69/2.10  tff(c_2250, plain, (![A_275, B_276, C_277]: (k1_relset_1(A_275, B_276, C_277)=k1_relat_1(C_277) | ~m1_subset_1(C_277, k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.69/2.10  tff(c_2259, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_2250])).
% 5.69/2.10  tff(c_3036, plain, (![B_383, A_384, C_385]: (k1_xboole_0=B_383 | k1_relset_1(A_384, B_383, C_385)=A_384 | ~v1_funct_2(C_385, A_384, B_383) | ~m1_subset_1(C_385, k1_zfmisc_1(k2_zfmisc_1(A_384, B_383))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.69/2.10  tff(c_3043, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_3036])).
% 5.69/2.10  tff(c_3047, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2259, c_3043])).
% 5.69/2.10  tff(c_3048, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_3047])).
% 5.69/2.10  tff(c_3063, plain, (k9_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3048, c_18])).
% 5.69/2.10  tff(c_3073, plain, (k9_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2244, c_3063])).
% 5.69/2.10  tff(c_2292, plain, (![A_285, B_286, C_287]: (r2_hidden('#skF_2'(A_285, B_286, C_287), B_286) | ~r2_hidden(A_285, k9_relat_1(C_287, B_286)) | ~v1_relat_1(C_287))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.69/2.10  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.69/2.10  tff(c_2299, plain, (![A_285, B_286, C_287]: (m1_subset_1('#skF_2'(A_285, B_286, C_287), B_286) | ~r2_hidden(A_285, k9_relat_1(C_287, B_286)) | ~v1_relat_1(C_287))), inference(resolution, [status(thm)], [c_2292, c_8])).
% 5.69/2.10  tff(c_3093, plain, (![A_285]: (m1_subset_1('#skF_2'(A_285, '#skF_4', '#skF_6'), '#skF_4') | ~r2_hidden(A_285, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3073, c_2299])).
% 5.69/2.10  tff(c_3152, plain, (![A_389]: (m1_subset_1('#skF_2'(A_389, '#skF_4', '#skF_6'), '#skF_4') | ~r2_hidden(A_389, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_2244, c_3093])).
% 5.69/2.10  tff(c_3175, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_2277, c_3152])).
% 5.69/2.10  tff(c_48, plain, (![E_30]: (k1_funct_1('#skF_6', E_30)!='#skF_3' | ~m1_subset_1(E_30, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.69/2.10  tff(c_3182, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_6'))!='#skF_3'), inference(resolution, [status(thm)], [c_3175, c_48])).
% 5.69/2.10  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.69/2.10  tff(c_26, plain, (![C_16, A_14, B_15]: (k1_funct_1(C_16, A_14)=B_15 | ~r2_hidden(k4_tarski(A_14, B_15), C_16) | ~v1_funct_1(C_16) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.69/2.10  tff(c_3998, plain, (![C_465, A_466, B_467]: (k1_funct_1(C_465, '#skF_2'(A_466, B_467, C_465))=A_466 | ~v1_funct_1(C_465) | ~r2_hidden(A_466, k9_relat_1(C_465, B_467)) | ~v1_relat_1(C_465))), inference(resolution, [status(thm)], [c_2526, c_26])).
% 5.69/2.10  tff(c_4002, plain, (![A_466]: (k1_funct_1('#skF_6', '#skF_2'(A_466, '#skF_4', '#skF_6'))=A_466 | ~v1_funct_1('#skF_6') | ~r2_hidden(A_466, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3073, c_3998])).
% 5.69/2.10  tff(c_4028, plain, (![A_468]: (k1_funct_1('#skF_6', '#skF_2'(A_468, '#skF_4', '#skF_6'))=A_468 | ~r2_hidden(A_468, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_2244, c_56, c_4002])).
% 5.69/2.10  tff(c_4043, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_6'))='#skF_3'), inference(resolution, [status(thm)], [c_2277, c_4028])).
% 5.69/2.10  tff(c_4054, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3182, c_4043])).
% 5.69/2.10  tff(c_4056, plain, (k1_relat_1('#skF_6')!='#skF_4'), inference(splitRight, [status(thm)], [c_3047])).
% 5.69/2.10  tff(c_4055, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_3047])).
% 5.69/2.10  tff(c_38, plain, (![C_28, A_26]: (k1_xboole_0=C_28 | ~v1_funct_2(C_28, A_26, k1_xboole_0) | k1_xboole_0=A_26 | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.69/2.10  tff(c_4510, plain, (![C_498, A_499]: (C_498='#skF_5' | ~v1_funct_2(C_498, A_499, '#skF_5') | A_499='#skF_5' | ~m1_subset_1(C_498, k1_zfmisc_1(k2_zfmisc_1(A_499, '#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_4055, c_4055, c_4055, c_4055, c_38])).
% 5.69/2.10  tff(c_4517, plain, ('#skF_5'='#skF_6' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_52, c_4510])).
% 5.69/2.10  tff(c_4521, plain, ('#skF_5'='#skF_6' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4517])).
% 5.69/2.10  tff(c_4522, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_4521])).
% 5.69/2.10  tff(c_4543, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4522, c_54])).
% 5.69/2.10  tff(c_4542, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4522, c_52])).
% 5.69/2.10  tff(c_44, plain, (![B_27, C_28]: (k1_relset_1(k1_xboole_0, B_27, C_28)=k1_xboole_0 | ~v1_funct_2(C_28, k1_xboole_0, B_27) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_27))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.69/2.10  tff(c_4058, plain, (![B_27, C_28]: (k1_relset_1('#skF_5', B_27, C_28)='#skF_5' | ~v1_funct_2(C_28, '#skF_5', B_27) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_27))))), inference(demodulation, [status(thm), theory('equality')], [c_4055, c_4055, c_4055, c_4055, c_44])).
% 5.69/2.10  tff(c_4811, plain, (![B_507, C_508]: (k1_relset_1('#skF_4', B_507, C_508)='#skF_4' | ~v1_funct_2(C_508, '#skF_4', B_507) | ~m1_subset_1(C_508, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_507))))), inference(demodulation, [status(thm), theory('equality')], [c_4522, c_4522, c_4522, c_4522, c_4058])).
% 5.69/2.10  tff(c_4814, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_4542, c_4811])).
% 5.69/2.10  tff(c_4825, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4543, c_4814])).
% 5.69/2.10  tff(c_4541, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4522, c_2259])).
% 5.69/2.10  tff(c_4836, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4825, c_4541])).
% 5.69/2.10  tff(c_4837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4056, c_4836])).
% 5.69/2.10  tff(c_4838, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_4521])).
% 5.69/2.10  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.69/2.10  tff(c_4077, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4055, c_6])).
% 5.69/2.10  tff(c_4854, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4838, c_4077])).
% 5.69/2.10  tff(c_4862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2627, c_4854])).
% 5.69/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.69/2.10  
% 5.69/2.10  Inference rules
% 5.69/2.10  ----------------------
% 5.69/2.10  #Ref     : 0
% 5.69/2.10  #Sup     : 982
% 5.69/2.10  #Fact    : 0
% 5.69/2.10  #Define  : 0
% 5.69/2.10  #Split   : 8
% 5.69/2.10  #Chain   : 0
% 5.69/2.10  #Close   : 0
% 5.69/2.10  
% 5.69/2.10  Ordering : KBO
% 5.69/2.10  
% 5.69/2.10  Simplification rules
% 5.69/2.10  ----------------------
% 5.69/2.10  #Subsume      : 301
% 5.69/2.10  #Demod        : 895
% 5.69/2.10  #Tautology    : 139
% 5.69/2.10  #SimpNegUnit  : 24
% 5.69/2.10  #BackRed      : 108
% 5.69/2.10  
% 5.69/2.10  #Partial instantiations: 0
% 5.69/2.10  #Strategies tried      : 1
% 5.69/2.10  
% 5.69/2.10  Timing (in seconds)
% 5.69/2.10  ----------------------
% 5.69/2.10  Preprocessing        : 0.31
% 5.69/2.10  Parsing              : 0.16
% 5.69/2.10  CNF conversion       : 0.02
% 5.69/2.10  Main loop            : 0.98
% 5.69/2.10  Inferencing          : 0.35
% 5.69/2.10  Reduction            : 0.27
% 5.69/2.10  Demodulation         : 0.19
% 5.69/2.10  BG Simplification    : 0.04
% 5.69/2.10  Subsumption          : 0.23
% 5.69/2.10  Abstraction          : 0.05
% 5.69/2.10  MUC search           : 0.00
% 5.69/2.10  Cooper               : 0.00
% 5.69/2.10  Total                : 1.33
% 5.69/2.10  Index Insertion      : 0.00
% 5.69/2.10  Index Deletion       : 0.00
% 5.69/2.10  Index Matching       : 0.00
% 5.69/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
