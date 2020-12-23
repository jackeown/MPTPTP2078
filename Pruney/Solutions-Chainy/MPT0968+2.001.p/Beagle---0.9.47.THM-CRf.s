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
% DateTime   : Thu Dec  3 10:11:17 EST 2020

% Result     : Theorem 6.77s
% Output     : CNFRefutation 6.77s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 416 expanded)
%              Number of leaves         :   59 ( 162 expanded)
%              Depth                    :   15
%              Number of atoms          :  140 ( 908 expanded)
%              Number of equality atoms :   54 ( 462 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_2 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_4 > #skF_15 > #skF_8 > #skF_12 > #skF_3 > #skF_14 > #skF_13 > #skF_11 > #skF_9 > #skF_2 > #skF_1 > #skF_6 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_233,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => r2_hidden(C,k1_funct_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

tff(f_170,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_162,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_148,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_166,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_204,axiom,(
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

tff(f_220,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_89,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_158,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(c_160,plain,(
    m1_subset_1('#skF_15',k1_zfmisc_1(k2_zfmisc_1('#skF_13','#skF_14'))) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_700,plain,(
    ! [A_194,B_195,C_196] :
      ( k2_relset_1(A_194,B_195,C_196) = k2_relat_1(C_196)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_720,plain,(
    k2_relset_1('#skF_13','#skF_14','#skF_15') = k2_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_160,c_700])).

tff(c_1128,plain,(
    ! [A_246,B_247,C_248] :
      ( m1_subset_1(k2_relset_1(A_246,B_247,C_248),k1_zfmisc_1(B_247))
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1186,plain,
    ( m1_subset_1(k2_relat_1('#skF_15'),k1_zfmisc_1('#skF_14'))
    | ~ m1_subset_1('#skF_15',k1_zfmisc_1(k2_zfmisc_1('#skF_13','#skF_14'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_720,c_1128])).

tff(c_1212,plain,(
    m1_subset_1(k2_relat_1('#skF_15'),k1_zfmisc_1('#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_1186])).

tff(c_36,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1220,plain,(
    r1_tarski(k2_relat_1('#skF_15'),'#skF_14') ),
    inference(resolution,[status(thm)],[c_1212,c_36])).

tff(c_292,plain,(
    ! [C_133,A_134,B_135] :
      ( v1_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_305,plain,(
    v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_160,c_292])).

tff(c_164,plain,(
    v1_funct_1('#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_158,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 != '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_177,plain,(
    k1_xboole_0 != '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_162,plain,(
    v1_funct_2('#skF_15','#skF_13','#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_769,plain,(
    ! [A_209,B_210,C_211] :
      ( k1_relset_1(A_209,B_210,C_211) = k1_relat_1(C_211)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_789,plain,(
    k1_relset_1('#skF_13','#skF_14','#skF_15') = k1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_160,c_769])).

tff(c_2728,plain,(
    ! [B_394,A_395,C_396] :
      ( k1_xboole_0 = B_394
      | k1_relset_1(A_395,B_394,C_396) = A_395
      | ~ v1_funct_2(C_396,A_395,B_394)
      | ~ m1_subset_1(C_396,k1_zfmisc_1(k2_zfmisc_1(A_395,B_394))) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_2747,plain,
    ( k1_xboole_0 = '#skF_14'
    | k1_relset_1('#skF_13','#skF_14','#skF_15') = '#skF_13'
    | ~ v1_funct_2('#skF_15','#skF_13','#skF_14') ),
    inference(resolution,[status(thm)],[c_160,c_2728])).

tff(c_2760,plain,
    ( k1_xboole_0 = '#skF_14'
    | k1_relat_1('#skF_15') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_789,c_2747])).

tff(c_2761,plain,(
    k1_relat_1('#skF_15') = '#skF_13' ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_2760])).

tff(c_120,plain,(
    ! [E_105,B_87] :
      ( r2_hidden(E_105,k1_funct_2(k1_relat_1(E_105),B_87))
      | ~ r1_tarski(k2_relat_1(E_105),B_87)
      | ~ v1_funct_1(E_105)
      | ~ v1_relat_1(E_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_2773,plain,(
    ! [B_87] :
      ( r2_hidden('#skF_15',k1_funct_2('#skF_13',B_87))
      | ~ r1_tarski(k2_relat_1('#skF_15'),B_87)
      | ~ v1_funct_1('#skF_15')
      | ~ v1_relat_1('#skF_15') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2761,c_120])).

tff(c_2905,plain,(
    ! [B_400] :
      ( r2_hidden('#skF_15',k1_funct_2('#skF_13',B_400))
      | ~ r1_tarski(k2_relat_1('#skF_15'),B_400) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_164,c_2773])).

tff(c_156,plain,(
    ~ r2_hidden('#skF_15',k1_funct_2('#skF_13','#skF_14')) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_2910,plain,(
    ~ r1_tarski(k2_relat_1('#skF_15'),'#skF_14') ),
    inference(resolution,[status(thm)],[c_2905,c_156])).

tff(c_2919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1220,c_2910])).

tff(c_2920,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2976,plain,(
    ! [A_5] : k3_xboole_0(A_5,'#skF_13') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2920,c_2920,c_6])).

tff(c_28,plain,(
    ! [B_16] : k2_zfmisc_1(k1_xboole_0,B_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2952,plain,(
    ! [B_16] : k2_zfmisc_1('#skF_13',B_16) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2920,c_2920,c_28])).

tff(c_2921,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_2928,plain,(
    '#skF_14' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2920,c_2921])).

tff(c_2996,plain,(
    m1_subset_1('#skF_15',k1_zfmisc_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2952,c_2928,c_160])).

tff(c_3000,plain,(
    ! [A_412,B_413] :
      ( r1_tarski(A_412,B_413)
      | ~ m1_subset_1(A_412,k1_zfmisc_1(B_413)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3004,plain,(
    r1_tarski('#skF_15','#skF_13') ),
    inference(resolution,[status(thm)],[c_2996,c_3000])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3007,plain,(
    k3_xboole_0('#skF_15','#skF_13') = '#skF_15' ),
    inference(resolution,[status(thm)],[c_3004,c_4])).

tff(c_3009,plain,(
    '#skF_15' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2976,c_3007])).

tff(c_3011,plain,(
    m1_subset_1('#skF_13',k1_zfmisc_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3009,c_2996])).

tff(c_26,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2960,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,'#skF_13') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2920,c_2920,c_26])).

tff(c_3080,plain,(
    ! [C_426,A_427,B_428] :
      ( v1_relat_1(C_426)
      | ~ m1_subset_1(C_426,k1_zfmisc_1(k2_zfmisc_1(A_427,B_428))) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_3090,plain,(
    ! [C_429] :
      ( v1_relat_1(C_429)
      | ~ m1_subset_1(C_429,k1_zfmisc_1('#skF_13')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2960,c_3080])).

tff(c_3098,plain,(
    v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_3011,c_3090])).

tff(c_3014,plain,(
    v1_funct_1('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3009,c_164])).

tff(c_48,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2923,plain,(
    k1_relat_1('#skF_13') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2920,c_2920,c_48])).

tff(c_3597,plain,(
    ! [A_514,B_515,C_516] :
      ( k1_relset_1(A_514,B_515,C_516) = k1_relat_1(C_516)
      | ~ m1_subset_1(C_516,k1_zfmisc_1(k2_zfmisc_1(A_514,B_515))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_3614,plain,(
    ! [A_517,C_518] :
      ( k1_relset_1(A_517,'#skF_13',C_518) = k1_relat_1(C_518)
      | ~ m1_subset_1(C_518,k1_zfmisc_1('#skF_13')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2960,c_3597])).

tff(c_3619,plain,(
    ! [A_517] : k1_relset_1(A_517,'#skF_13','#skF_13') = k1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_3011,c_3614])).

tff(c_3625,plain,(
    ! [A_517] : k1_relset_1(A_517,'#skF_13','#skF_13') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2923,c_3619])).

tff(c_3938,plain,(
    ! [A_546,B_547,C_548] :
      ( m1_subset_1(k1_relset_1(A_546,B_547,C_548),k1_zfmisc_1(A_546))
      | ~ m1_subset_1(C_548,k1_zfmisc_1(k2_zfmisc_1(A_546,B_547))) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3996,plain,(
    ! [A_517] :
      ( m1_subset_1('#skF_13',k1_zfmisc_1(A_517))
      | ~ m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1(A_517,'#skF_13'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3625,c_3938])).

tff(c_4024,plain,(
    ! [A_549] : m1_subset_1('#skF_13',k1_zfmisc_1(A_549)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3011,c_2960,c_3996])).

tff(c_4105,plain,(
    ! [A_549] : r1_tarski('#skF_13',A_549) ),
    inference(resolution,[status(thm)],[c_4024,c_36])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2922,plain,(
    k2_relat_1('#skF_13') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2920,c_2920,c_46])).

tff(c_5300,plain,(
    ! [E_637,B_638] :
      ( r2_hidden(E_637,k1_funct_2(k1_relat_1(E_637),B_638))
      | ~ r1_tarski(k2_relat_1(E_637),B_638)
      | ~ v1_funct_1(E_637)
      | ~ v1_relat_1(E_637) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_5308,plain,(
    ! [B_638] :
      ( r2_hidden('#skF_13',k1_funct_2('#skF_13',B_638))
      | ~ r1_tarski(k2_relat_1('#skF_13'),B_638)
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2923,c_5300])).

tff(c_5311,plain,(
    ! [B_638] : r2_hidden('#skF_13',k1_funct_2('#skF_13',B_638)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3098,c_3014,c_4105,c_2922,c_5308])).

tff(c_2934,plain,(
    ~ r2_hidden('#skF_15',k1_funct_2('#skF_13','#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2928,c_156])).

tff(c_3013,plain,(
    ~ r2_hidden('#skF_13',k1_funct_2('#skF_13','#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3009,c_2934])).

tff(c_5314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5311,c_3013])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:15:09 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.77/2.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.77/2.25  
% 6.77/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.77/2.26  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_2 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_4 > #skF_15 > #skF_8 > #skF_12 > #skF_3 > #skF_14 > #skF_13 > #skF_11 > #skF_9 > #skF_2 > #skF_1 > #skF_6 > #skF_10
% 6.77/2.26  
% 6.77/2.26  %Foreground sorts:
% 6.77/2.26  
% 6.77/2.26  
% 6.77/2.26  %Background operators:
% 6.77/2.26  
% 6.77/2.26  
% 6.77/2.26  %Foreground operators:
% 6.77/2.26  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.77/2.26  tff('#skF_7', type, '#skF_7': $i > $i).
% 6.77/2.26  tff('#skF_5', type, '#skF_5': $i > $i).
% 6.77/2.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.77/2.26  tff('#skF_4', type, '#skF_4': $i > $i).
% 6.77/2.26  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.77/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.77/2.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.77/2.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.77/2.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.77/2.26  tff('#skF_15', type, '#skF_15': $i).
% 6.77/2.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.77/2.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.77/2.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.77/2.26  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.77/2.26  tff('#skF_8', type, '#skF_8': $i > $i).
% 6.77/2.26  tff('#skF_12', type, '#skF_12': ($i * $i * $i * $i) > $i).
% 6.77/2.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.77/2.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.77/2.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.77/2.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.77/2.26  tff('#skF_14', type, '#skF_14': $i).
% 6.77/2.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.77/2.26  tff('#skF_13', type, '#skF_13': $i).
% 6.77/2.26  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.77/2.26  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 6.77/2.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.77/2.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.77/2.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.77/2.26  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.77/2.26  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 6.77/2.26  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 6.77/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.77/2.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.77/2.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.77/2.26  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.77/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.77/2.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.77/2.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.77/2.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.77/2.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.77/2.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.77/2.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.77/2.26  tff('#skF_6', type, '#skF_6': $i > $i).
% 6.77/2.26  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 6.77/2.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.77/2.26  
% 6.77/2.27  tff(f_233, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => r2_hidden(C, k1_funct_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_funct_2)).
% 6.77/2.27  tff(f_170, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.77/2.27  tff(f_162, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 6.77/2.27  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.77/2.27  tff(f_148, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.77/2.27  tff(f_166, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.77/2.27  tff(f_204, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.77/2.27  tff(f_220, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 6.77/2.27  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.77/2.27  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.77/2.27  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.77/2.27  tff(f_89, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 6.77/2.27  tff(f_158, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 6.77/2.27  tff(c_160, plain, (m1_subset_1('#skF_15', k1_zfmisc_1(k2_zfmisc_1('#skF_13', '#skF_14')))), inference(cnfTransformation, [status(thm)], [f_233])).
% 6.77/2.27  tff(c_700, plain, (![A_194, B_195, C_196]: (k2_relset_1(A_194, B_195, C_196)=k2_relat_1(C_196) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))))), inference(cnfTransformation, [status(thm)], [f_170])).
% 6.77/2.27  tff(c_720, plain, (k2_relset_1('#skF_13', '#skF_14', '#skF_15')=k2_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_160, c_700])).
% 6.77/2.27  tff(c_1128, plain, (![A_246, B_247, C_248]: (m1_subset_1(k2_relset_1(A_246, B_247, C_248), k1_zfmisc_1(B_247)) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.77/2.27  tff(c_1186, plain, (m1_subset_1(k2_relat_1('#skF_15'), k1_zfmisc_1('#skF_14')) | ~m1_subset_1('#skF_15', k1_zfmisc_1(k2_zfmisc_1('#skF_13', '#skF_14')))), inference(superposition, [status(thm), theory('equality')], [c_720, c_1128])).
% 6.77/2.27  tff(c_1212, plain, (m1_subset_1(k2_relat_1('#skF_15'), k1_zfmisc_1('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_1186])).
% 6.77/2.27  tff(c_36, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.77/2.27  tff(c_1220, plain, (r1_tarski(k2_relat_1('#skF_15'), '#skF_14')), inference(resolution, [status(thm)], [c_1212, c_36])).
% 6.77/2.27  tff(c_292, plain, (![C_133, A_134, B_135]: (v1_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.77/2.27  tff(c_305, plain, (v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_160, c_292])).
% 6.77/2.27  tff(c_164, plain, (v1_funct_1('#skF_15')), inference(cnfTransformation, [status(thm)], [f_233])).
% 6.77/2.27  tff(c_158, plain, (k1_xboole_0='#skF_13' | k1_xboole_0!='#skF_14'), inference(cnfTransformation, [status(thm)], [f_233])).
% 6.77/2.27  tff(c_177, plain, (k1_xboole_0!='#skF_14'), inference(splitLeft, [status(thm)], [c_158])).
% 6.77/2.27  tff(c_162, plain, (v1_funct_2('#skF_15', '#skF_13', '#skF_14')), inference(cnfTransformation, [status(thm)], [f_233])).
% 6.77/2.27  tff(c_769, plain, (![A_209, B_210, C_211]: (k1_relset_1(A_209, B_210, C_211)=k1_relat_1(C_211) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.77/2.27  tff(c_789, plain, (k1_relset_1('#skF_13', '#skF_14', '#skF_15')=k1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_160, c_769])).
% 6.77/2.27  tff(c_2728, plain, (![B_394, A_395, C_396]: (k1_xboole_0=B_394 | k1_relset_1(A_395, B_394, C_396)=A_395 | ~v1_funct_2(C_396, A_395, B_394) | ~m1_subset_1(C_396, k1_zfmisc_1(k2_zfmisc_1(A_395, B_394))))), inference(cnfTransformation, [status(thm)], [f_204])).
% 6.77/2.27  tff(c_2747, plain, (k1_xboole_0='#skF_14' | k1_relset_1('#skF_13', '#skF_14', '#skF_15')='#skF_13' | ~v1_funct_2('#skF_15', '#skF_13', '#skF_14')), inference(resolution, [status(thm)], [c_160, c_2728])).
% 6.77/2.27  tff(c_2760, plain, (k1_xboole_0='#skF_14' | k1_relat_1('#skF_15')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_789, c_2747])).
% 6.77/2.27  tff(c_2761, plain, (k1_relat_1('#skF_15')='#skF_13'), inference(negUnitSimplification, [status(thm)], [c_177, c_2760])).
% 6.77/2.27  tff(c_120, plain, (![E_105, B_87]: (r2_hidden(E_105, k1_funct_2(k1_relat_1(E_105), B_87)) | ~r1_tarski(k2_relat_1(E_105), B_87) | ~v1_funct_1(E_105) | ~v1_relat_1(E_105))), inference(cnfTransformation, [status(thm)], [f_220])).
% 6.77/2.27  tff(c_2773, plain, (![B_87]: (r2_hidden('#skF_15', k1_funct_2('#skF_13', B_87)) | ~r1_tarski(k2_relat_1('#skF_15'), B_87) | ~v1_funct_1('#skF_15') | ~v1_relat_1('#skF_15'))), inference(superposition, [status(thm), theory('equality')], [c_2761, c_120])).
% 6.77/2.27  tff(c_2905, plain, (![B_400]: (r2_hidden('#skF_15', k1_funct_2('#skF_13', B_400)) | ~r1_tarski(k2_relat_1('#skF_15'), B_400))), inference(demodulation, [status(thm), theory('equality')], [c_305, c_164, c_2773])).
% 6.77/2.27  tff(c_156, plain, (~r2_hidden('#skF_15', k1_funct_2('#skF_13', '#skF_14'))), inference(cnfTransformation, [status(thm)], [f_233])).
% 6.77/2.27  tff(c_2910, plain, (~r1_tarski(k2_relat_1('#skF_15'), '#skF_14')), inference(resolution, [status(thm)], [c_2905, c_156])).
% 6.77/2.27  tff(c_2919, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1220, c_2910])).
% 6.77/2.27  tff(c_2920, plain, (k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_158])).
% 6.77/2.27  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.77/2.27  tff(c_2976, plain, (![A_5]: (k3_xboole_0(A_5, '#skF_13')='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_2920, c_2920, c_6])).
% 6.77/2.27  tff(c_28, plain, (![B_16]: (k2_zfmisc_1(k1_xboole_0, B_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.77/2.27  tff(c_2952, plain, (![B_16]: (k2_zfmisc_1('#skF_13', B_16)='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_2920, c_2920, c_28])).
% 6.77/2.27  tff(c_2921, plain, (k1_xboole_0='#skF_14'), inference(splitRight, [status(thm)], [c_158])).
% 6.77/2.27  tff(c_2928, plain, ('#skF_14'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_2920, c_2921])).
% 6.77/2.27  tff(c_2996, plain, (m1_subset_1('#skF_15', k1_zfmisc_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_2952, c_2928, c_160])).
% 6.77/2.27  tff(c_3000, plain, (![A_412, B_413]: (r1_tarski(A_412, B_413) | ~m1_subset_1(A_412, k1_zfmisc_1(B_413)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.77/2.27  tff(c_3004, plain, (r1_tarski('#skF_15', '#skF_13')), inference(resolution, [status(thm)], [c_2996, c_3000])).
% 6.77/2.27  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.77/2.27  tff(c_3007, plain, (k3_xboole_0('#skF_15', '#skF_13')='#skF_15'), inference(resolution, [status(thm)], [c_3004, c_4])).
% 6.77/2.27  tff(c_3009, plain, ('#skF_15'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_2976, c_3007])).
% 6.77/2.27  tff(c_3011, plain, (m1_subset_1('#skF_13', k1_zfmisc_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_3009, c_2996])).
% 6.77/2.27  tff(c_26, plain, (![A_15]: (k2_zfmisc_1(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.77/2.27  tff(c_2960, plain, (![A_15]: (k2_zfmisc_1(A_15, '#skF_13')='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_2920, c_2920, c_26])).
% 6.77/2.27  tff(c_3080, plain, (![C_426, A_427, B_428]: (v1_relat_1(C_426) | ~m1_subset_1(C_426, k1_zfmisc_1(k2_zfmisc_1(A_427, B_428))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.77/2.27  tff(c_3090, plain, (![C_429]: (v1_relat_1(C_429) | ~m1_subset_1(C_429, k1_zfmisc_1('#skF_13')))), inference(superposition, [status(thm), theory('equality')], [c_2960, c_3080])).
% 6.77/2.27  tff(c_3098, plain, (v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_3011, c_3090])).
% 6.77/2.27  tff(c_3014, plain, (v1_funct_1('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_3009, c_164])).
% 6.77/2.27  tff(c_48, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.77/2.27  tff(c_2923, plain, (k1_relat_1('#skF_13')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_2920, c_2920, c_48])).
% 6.77/2.27  tff(c_3597, plain, (![A_514, B_515, C_516]: (k1_relset_1(A_514, B_515, C_516)=k1_relat_1(C_516) | ~m1_subset_1(C_516, k1_zfmisc_1(k2_zfmisc_1(A_514, B_515))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.77/2.27  tff(c_3614, plain, (![A_517, C_518]: (k1_relset_1(A_517, '#skF_13', C_518)=k1_relat_1(C_518) | ~m1_subset_1(C_518, k1_zfmisc_1('#skF_13')))), inference(superposition, [status(thm), theory('equality')], [c_2960, c_3597])).
% 6.77/2.27  tff(c_3619, plain, (![A_517]: (k1_relset_1(A_517, '#skF_13', '#skF_13')=k1_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_3011, c_3614])).
% 6.77/2.27  tff(c_3625, plain, (![A_517]: (k1_relset_1(A_517, '#skF_13', '#skF_13')='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_2923, c_3619])).
% 6.77/2.27  tff(c_3938, plain, (![A_546, B_547, C_548]: (m1_subset_1(k1_relset_1(A_546, B_547, C_548), k1_zfmisc_1(A_546)) | ~m1_subset_1(C_548, k1_zfmisc_1(k2_zfmisc_1(A_546, B_547))))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.77/2.27  tff(c_3996, plain, (![A_517]: (m1_subset_1('#skF_13', k1_zfmisc_1(A_517)) | ~m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1(A_517, '#skF_13'))))), inference(superposition, [status(thm), theory('equality')], [c_3625, c_3938])).
% 6.77/2.27  tff(c_4024, plain, (![A_549]: (m1_subset_1('#skF_13', k1_zfmisc_1(A_549)))), inference(demodulation, [status(thm), theory('equality')], [c_3011, c_2960, c_3996])).
% 6.77/2.27  tff(c_4105, plain, (![A_549]: (r1_tarski('#skF_13', A_549))), inference(resolution, [status(thm)], [c_4024, c_36])).
% 6.77/2.27  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.77/2.27  tff(c_2922, plain, (k2_relat_1('#skF_13')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_2920, c_2920, c_46])).
% 6.77/2.27  tff(c_5300, plain, (![E_637, B_638]: (r2_hidden(E_637, k1_funct_2(k1_relat_1(E_637), B_638)) | ~r1_tarski(k2_relat_1(E_637), B_638) | ~v1_funct_1(E_637) | ~v1_relat_1(E_637))), inference(cnfTransformation, [status(thm)], [f_220])).
% 6.77/2.27  tff(c_5308, plain, (![B_638]: (r2_hidden('#skF_13', k1_funct_2('#skF_13', B_638)) | ~r1_tarski(k2_relat_1('#skF_13'), B_638) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_2923, c_5300])).
% 6.77/2.27  tff(c_5311, plain, (![B_638]: (r2_hidden('#skF_13', k1_funct_2('#skF_13', B_638)))), inference(demodulation, [status(thm), theory('equality')], [c_3098, c_3014, c_4105, c_2922, c_5308])).
% 6.77/2.27  tff(c_2934, plain, (~r2_hidden('#skF_15', k1_funct_2('#skF_13', '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_2928, c_156])).
% 6.77/2.27  tff(c_3013, plain, (~r2_hidden('#skF_13', k1_funct_2('#skF_13', '#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_3009, c_2934])).
% 6.77/2.27  tff(c_5314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5311, c_3013])).
% 6.77/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.77/2.27  
% 6.77/2.27  Inference rules
% 6.77/2.27  ----------------------
% 6.77/2.27  #Ref     : 0
% 6.77/2.27  #Sup     : 1121
% 6.77/2.27  #Fact    : 0
% 6.77/2.27  #Define  : 0
% 6.77/2.27  #Split   : 14
% 6.77/2.27  #Chain   : 0
% 6.77/2.27  #Close   : 0
% 6.77/2.27  
% 6.77/2.27  Ordering : KBO
% 6.77/2.27  
% 6.77/2.27  Simplification rules
% 6.77/2.27  ----------------------
% 6.77/2.27  #Subsume      : 168
% 6.77/2.27  #Demod        : 508
% 6.77/2.27  #Tautology    : 341
% 6.77/2.27  #SimpNegUnit  : 12
% 6.77/2.27  #BackRed      : 20
% 6.77/2.27  
% 6.77/2.27  #Partial instantiations: 0
% 6.77/2.27  #Strategies tried      : 1
% 6.77/2.27  
% 6.77/2.27  Timing (in seconds)
% 6.77/2.27  ----------------------
% 6.77/2.28  Preprocessing        : 0.43
% 6.77/2.28  Parsing              : 0.21
% 6.77/2.28  CNF conversion       : 0.04
% 6.77/2.28  Main loop            : 1.08
% 6.77/2.28  Inferencing          : 0.38
% 6.77/2.28  Reduction            : 0.34
% 6.77/2.28  Demodulation         : 0.24
% 6.77/2.28  BG Simplification    : 0.06
% 6.77/2.28  Subsumption          : 0.20
% 6.77/2.28  Abstraction          : 0.05
% 6.77/2.28  MUC search           : 0.00
% 6.77/2.28  Cooper               : 0.00
% 6.77/2.28  Total                : 1.55
% 6.77/2.28  Index Insertion      : 0.00
% 6.77/2.28  Index Deletion       : 0.00
% 6.77/2.28  Index Matching       : 0.00
% 6.77/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
