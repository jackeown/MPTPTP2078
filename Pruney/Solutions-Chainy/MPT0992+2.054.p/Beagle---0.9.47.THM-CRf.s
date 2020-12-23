%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:39 EST 2020

% Result     : Theorem 7.80s
% Output     : CNFRefutation 7.84s
% Verified   : 
% Statistics : Number of formulae       :  178 (1946 expanded)
%              Number of leaves         :   36 ( 604 expanded)
%              Depth                    :   15
%              Number of atoms          :  288 (5681 expanded)
%              Number of equality atoms :   84 (2095 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_151,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_117,axiom,(
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

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_131,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_125,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_66,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_6263,plain,(
    ! [C_511,A_512,B_513] :
      ( v1_relat_1(C_511)
      | ~ m1_subset_1(C_511,k1_zfmisc_1(k2_zfmisc_1(A_512,B_513))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6282,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_6263])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_81,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_6833,plain,(
    ! [A_555,B_556,C_557] :
      ( k1_relset_1(A_555,B_556,C_557) = k1_relat_1(C_557)
      | ~ m1_subset_1(C_557,k1_zfmisc_1(k2_zfmisc_1(A_555,B_556))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6858,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_6833])).

tff(c_8273,plain,(
    ! [B_686,A_687,C_688] :
      ( k1_xboole_0 = B_686
      | k1_relset_1(A_687,B_686,C_688) = A_687
      | ~ v1_funct_2(C_688,A_687,B_686)
      | ~ m1_subset_1(C_688,k1_zfmisc_1(k2_zfmisc_1(A_687,B_686))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_8290,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_8273])).

tff(c_8307,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_6858,c_8290])).

tff(c_8308,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_8307])).

tff(c_32,plain,(
    ! [B_21,A_20] :
      ( k1_relat_1(k7_relat_1(B_21,A_20)) = A_20
      | ~ r1_tarski(A_20,k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8327,plain,(
    ! [A_20] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_20)) = A_20
      | ~ r1_tarski(A_20,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8308,c_32])).

tff(c_8336,plain,(
    ! [A_20] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_20)) = A_20
      | ~ r1_tarski(A_20,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6282,c_8327])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_7956,plain,(
    ! [A_668,B_669,C_670,D_671] :
      ( k2_partfun1(A_668,B_669,C_670,D_671) = k7_relat_1(C_670,D_671)
      | ~ m1_subset_1(C_670,k1_zfmisc_1(k2_zfmisc_1(A_668,B_669)))
      | ~ v1_funct_1(C_670) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_7966,plain,(
    ! [D_671] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_671) = k7_relat_1('#skF_4',D_671)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_7956])).

tff(c_7980,plain,(
    ! [D_671] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_671) = k7_relat_1('#skF_4',D_671) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_7966])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1601,plain,(
    ! [C_171,A_172,B_173] :
      ( v1_relat_1(C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1620,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1601])).

tff(c_2164,plain,(
    ! [A_218,B_219,C_220] :
      ( k1_relset_1(A_218,B_219,C_220) = k1_relat_1(C_220)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2185,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_2164])).

tff(c_3333,plain,(
    ! [B_341,A_342,C_343] :
      ( k1_xboole_0 = B_341
      | k1_relset_1(A_342,B_341,C_343) = A_342
      | ~ v1_funct_2(C_343,A_342,B_341)
      | ~ m1_subset_1(C_343,k1_zfmisc_1(k2_zfmisc_1(A_342,B_341))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_3347,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_3333])).

tff(c_3362,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2185,c_3347])).

tff(c_3363,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_3362])).

tff(c_3389,plain,(
    ! [A_20] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_20)) = A_20
      | ~ r1_tarski(A_20,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3363,c_32])).

tff(c_3398,plain,(
    ! [A_20] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_20)) = A_20
      | ~ r1_tarski(A_20,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1620,c_3389])).

tff(c_30,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k7_relat_1(B_19,A_18),B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_129,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(A_60,B_61)
      | ~ m1_subset_1(A_60,k1_zfmisc_1(B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_138,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_129])).

tff(c_1651,plain,(
    ! [A_175,C_176,B_177] :
      ( r1_tarski(A_175,C_176)
      | ~ r1_tarski(B_177,C_176)
      | ~ r1_tarski(A_175,B_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1838,plain,(
    ! [A_197] :
      ( r1_tarski(A_197,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_197,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_138,c_1651])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1617,plain,(
    ! [A_10,A_172,B_173] :
      ( v1_relat_1(A_10)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_172,B_173)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1601])).

tff(c_1849,plain,(
    ! [A_198] :
      ( v1_relat_1(A_198)
      | ~ r1_tarski(A_198,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1838,c_1617])).

tff(c_1853,plain,(
    ! [A_18] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_18))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_1849])).

tff(c_1864,plain,(
    ! [A_18] : v1_relat_1(k7_relat_1('#skF_4',A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1620,c_1853])).

tff(c_34,plain,(
    ! [A_22] :
      ( k7_relat_1(A_22,k1_relat_1(A_22)) = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3392,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3363,c_34])).

tff(c_3400,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1620,c_3392])).

tff(c_1933,plain,(
    ! [A_204,B_205,A_206] :
      ( r1_tarski(A_204,B_205)
      | ~ r1_tarski(A_204,k7_relat_1(B_205,A_206))
      | ~ v1_relat_1(B_205) ) ),
    inference(resolution,[status(thm)],[c_30,c_1651])).

tff(c_5684,plain,(
    ! [B_491,A_492,A_493] :
      ( r1_tarski(k7_relat_1(k7_relat_1(B_491,A_492),A_493),B_491)
      | ~ v1_relat_1(B_491)
      | ~ v1_relat_1(k7_relat_1(B_491,A_492)) ) ),
    inference(resolution,[status(thm)],[c_30,c_1933])).

tff(c_5788,plain,(
    ! [A_493] :
      ( r1_tarski(k7_relat_1('#skF_4',A_493),'#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3400,c_5684])).

tff(c_5886,plain,(
    ! [A_493] : r1_tarski(k7_relat_1('#skF_4',A_493),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1864,c_1620,c_5788])).

tff(c_1662,plain,(
    ! [A_175] :
      ( r1_tarski(A_175,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_175,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_138,c_1651])).

tff(c_3064,plain,(
    ! [D_320,B_321,C_322,A_323] :
      ( m1_subset_1(D_320,k1_zfmisc_1(k2_zfmisc_1(B_321,C_322)))
      | ~ r1_tarski(k1_relat_1(D_320),B_321)
      | ~ m1_subset_1(D_320,k1_zfmisc_1(k2_zfmisc_1(A_323,C_322))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5537,plain,(
    ! [A_481,B_482,C_483,A_484] :
      ( m1_subset_1(A_481,k1_zfmisc_1(k2_zfmisc_1(B_482,C_483)))
      | ~ r1_tarski(k1_relat_1(A_481),B_482)
      | ~ r1_tarski(A_481,k2_zfmisc_1(A_484,C_483)) ) ),
    inference(resolution,[status(thm)],[c_22,c_3064])).

tff(c_6184,plain,(
    ! [A_507,B_508] :
      ( m1_subset_1(A_507,k1_zfmisc_1(k2_zfmisc_1(B_508,'#skF_2')))
      | ~ r1_tarski(k1_relat_1(A_507),B_508)
      | ~ r1_tarski(A_507,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1662,c_5537])).

tff(c_3200,plain,(
    ! [A_330,B_331,C_332,D_333] :
      ( k2_partfun1(A_330,B_331,C_332,D_333) = k7_relat_1(C_332,D_333)
      | ~ m1_subset_1(C_332,k1_zfmisc_1(k2_zfmisc_1(A_330,B_331)))
      | ~ v1_funct_1(C_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3210,plain,(
    ! [D_333] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_333) = k7_relat_1('#skF_4',D_333)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_3200])).

tff(c_3224,plain,(
    ! [D_333] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_333) = k7_relat_1('#skF_4',D_333) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3210])).

tff(c_1457,plain,(
    ! [A_156,B_157,C_158,D_159] :
      ( v1_funct_1(k2_partfun1(A_156,B_157,C_158,D_159))
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157)))
      | ~ v1_funct_1(C_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1465,plain,(
    ! [D_159] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_159))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_1457])).

tff(c_1474,plain,(
    ! [D_159] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_159)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1465])).

tff(c_62,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_144,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_1477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1474,c_144])).

tff(c_1478,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1589,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1478])).

tff(c_3248,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3224,c_1589])).

tff(c_6199,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_6184,c_3248])).

tff(c_6235,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5886,c_6199])).

tff(c_6246,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3398,c_6235])).

tff(c_6249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6,c_6246])).

tff(c_6251,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1478])).

tff(c_6854,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6251,c_6833])).

tff(c_8005,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7980,c_7980,c_6854])).

tff(c_6250,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1478])).

tff(c_8014,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7980,c_6250])).

tff(c_8013,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7980,c_6251])).

tff(c_8465,plain,(
    ! [B_691,C_692,A_693] :
      ( k1_xboole_0 = B_691
      | v1_funct_2(C_692,A_693,B_691)
      | k1_relset_1(A_693,B_691,C_692) != A_693
      | ~ m1_subset_1(C_692,k1_zfmisc_1(k2_zfmisc_1(A_693,B_691))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_8471,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_8013,c_8465])).

tff(c_8494,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_8014,c_81,c_8471])).

tff(c_8837,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8005,c_8494])).

tff(c_8844,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8336,c_8837])).

tff(c_8848,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8844])).

tff(c_8849,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8851,plain,(
    ! [A_6] : r1_tarski('#skF_1',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8849,c_10])).

tff(c_14,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8864,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8849,c_8849,c_14])).

tff(c_8850,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_8856,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8849,c_8850])).

tff(c_8862,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8856,c_68])).

tff(c_8865,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8864,c_8862])).

tff(c_9419,plain,(
    ! [A_785,B_786] :
      ( r1_tarski(A_785,B_786)
      | ~ m1_subset_1(A_785,k1_zfmisc_1(B_786)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_9430,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_8865,c_9419])).

tff(c_9461,plain,(
    ! [B_790,A_791] :
      ( B_790 = A_791
      | ~ r1_tarski(B_790,A_791)
      | ~ r1_tarski(A_791,B_790) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_9463,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_9430,c_9461])).

tff(c_9474,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8851,c_9463])).

tff(c_8857,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8856,c_70])).

tff(c_9500,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9474,c_9474,c_8857])).

tff(c_18,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8889,plain,(
    ! [A_9] : m1_subset_1('#skF_1',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8849,c_18])).

tff(c_9531,plain,(
    ! [A_796] : m1_subset_1('#skF_4',k1_zfmisc_1(A_796)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9474,c_8889])).

tff(c_36,plain,(
    ! [C_25,A_23,B_24] :
      ( v1_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_9539,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_9531,c_36])).

tff(c_9476,plain,(
    ! [A_6] :
      ( A_6 = '#skF_1'
      | ~ r1_tarski(A_6,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_8851,c_9461])).

tff(c_9570,plain,(
    ! [A_799] :
      ( A_799 = '#skF_4'
      | ~ r1_tarski(A_799,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9474,c_9474,c_9476])).

tff(c_9578,plain,(
    ! [A_18] :
      ( k7_relat_1('#skF_4',A_18) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_9570])).

tff(c_9587,plain,(
    ! [A_18] : k7_relat_1('#skF_4',A_18) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9539,c_9578])).

tff(c_9497,plain,(
    ! [A_9] : m1_subset_1('#skF_4',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9474,c_8889])).

tff(c_10233,plain,(
    ! [A_895,B_896,C_897,D_898] :
      ( k2_partfun1(A_895,B_896,C_897,D_898) = k7_relat_1(C_897,D_898)
      | ~ m1_subset_1(C_897,k1_zfmisc_1(k2_zfmisc_1(A_895,B_896)))
      | ~ v1_funct_1(C_897) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_10240,plain,(
    ! [A_895,B_896,D_898] :
      ( k2_partfun1(A_895,B_896,'#skF_4',D_898) = k7_relat_1('#skF_4',D_898)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_9497,c_10233])).

tff(c_10246,plain,(
    ! [A_895,B_896,D_898] : k2_partfun1(A_895,B_896,'#skF_4',D_898) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_9587,c_10240])).

tff(c_9471,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_9461])).

tff(c_9483,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8851,c_9471])).

tff(c_9491,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9474,c_9483])).

tff(c_8902,plain,(
    ! [A_720,B_721] :
      ( r1_tarski(A_720,B_721)
      | ~ m1_subset_1(A_720,k1_zfmisc_1(B_721)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8909,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_8865,c_8902])).

tff(c_8946,plain,(
    ! [B_729,A_730] :
      ( B_729 = A_730
      | ~ r1_tarski(B_729,A_730)
      | ~ r1_tarski(A_730,B_729) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8950,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_8909,c_8946])).

tff(c_8960,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8851,c_8950])).

tff(c_8983,plain,(
    ! [A_9] : m1_subset_1('#skF_4',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8960,c_8889])).

tff(c_9397,plain,(
    ! [A_777,B_778,C_779,D_780] :
      ( v1_funct_1(k2_partfun1(A_777,B_778,C_779,D_780))
      | ~ m1_subset_1(C_779,k1_zfmisc_1(k2_zfmisc_1(A_777,B_778)))
      | ~ v1_funct_1(C_779) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_9404,plain,(
    ! [A_777,B_778,D_780] :
      ( v1_funct_1(k2_partfun1(A_777,B_778,'#skF_4',D_780))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8983,c_9397])).

tff(c_9410,plain,(
    ! [A_777,B_778,D_780] : v1_funct_1(k2_partfun1(A_777,B_778,'#skF_4',D_780)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_9404])).

tff(c_8956,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_8946])).

tff(c_8968,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8851,c_8956])).

tff(c_8900,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8856,c_8856,c_8856,c_8864,c_8856,c_8856,c_62])).

tff(c_8901,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_8900])).

tff(c_8969,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8968,c_8901])).

tff(c_8976,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8960,c_8960,c_8960,c_8969])).

tff(c_9414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9410,c_8976])).

tff(c_9415,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_8900])).

tff(c_9643,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9491,c_9474,c_9474,c_9474,c_9491,c_9491,c_9474,c_9474,c_9474,c_9415])).

tff(c_9644,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_9643])).

tff(c_9760,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_9644])).

tff(c_10249,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10246,c_9760])).

tff(c_10254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10249])).

tff(c_10256,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_9643])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10418,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_10256,c_20])).

tff(c_9569,plain,(
    ! [A_6] :
      ( A_6 = '#skF_4'
      | ~ r1_tarski(A_6,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9474,c_9474,c_9476])).

tff(c_10439,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10418,c_9569])).

tff(c_10255,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_9643])).

tff(c_10446,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10439,c_10255])).

tff(c_10453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9500,c_10446])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:04:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.80/2.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.84/2.72  
% 7.84/2.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.84/2.73  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.84/2.73  
% 7.84/2.73  %Foreground sorts:
% 7.84/2.73  
% 7.84/2.73  
% 7.84/2.73  %Background operators:
% 7.84/2.73  
% 7.84/2.73  
% 7.84/2.73  %Foreground operators:
% 7.84/2.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.84/2.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.84/2.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.84/2.73  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.84/2.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.84/2.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.84/2.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.84/2.73  tff('#skF_2', type, '#skF_2': $i).
% 7.84/2.73  tff('#skF_3', type, '#skF_3': $i).
% 7.84/2.73  tff('#skF_1', type, '#skF_1': $i).
% 7.84/2.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.84/2.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.84/2.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.84/2.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.84/2.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.84/2.73  tff('#skF_4', type, '#skF_4': $i).
% 7.84/2.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.84/2.73  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.84/2.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.84/2.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.84/2.73  
% 7.84/2.75  tff(f_151, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 7.84/2.75  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.84/2.75  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.84/2.75  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.84/2.75  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 7.84/2.75  tff(f_131, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 7.84/2.75  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.84/2.75  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 7.84/2.75  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.84/2.75  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.84/2.75  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 7.84/2.75  tff(f_93, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 7.84/2.75  tff(f_125, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 7.84/2.75  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.84/2.75  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.84/2.75  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 7.84/2.75  tff(c_66, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.84/2.75  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.84/2.75  tff(c_6263, plain, (![C_511, A_512, B_513]: (v1_relat_1(C_511) | ~m1_subset_1(C_511, k1_zfmisc_1(k2_zfmisc_1(A_512, B_513))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.84/2.75  tff(c_6282, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_6263])).
% 7.84/2.75  tff(c_64, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.84/2.75  tff(c_81, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_64])).
% 7.84/2.75  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.84/2.75  tff(c_6833, plain, (![A_555, B_556, C_557]: (k1_relset_1(A_555, B_556, C_557)=k1_relat_1(C_557) | ~m1_subset_1(C_557, k1_zfmisc_1(k2_zfmisc_1(A_555, B_556))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.84/2.75  tff(c_6858, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_6833])).
% 7.84/2.75  tff(c_8273, plain, (![B_686, A_687, C_688]: (k1_xboole_0=B_686 | k1_relset_1(A_687, B_686, C_688)=A_687 | ~v1_funct_2(C_688, A_687, B_686) | ~m1_subset_1(C_688, k1_zfmisc_1(k2_zfmisc_1(A_687, B_686))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.84/2.75  tff(c_8290, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_8273])).
% 7.84/2.75  tff(c_8307, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_6858, c_8290])).
% 7.84/2.75  tff(c_8308, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_81, c_8307])).
% 7.84/2.75  tff(c_32, plain, (![B_21, A_20]: (k1_relat_1(k7_relat_1(B_21, A_20))=A_20 | ~r1_tarski(A_20, k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.84/2.75  tff(c_8327, plain, (![A_20]: (k1_relat_1(k7_relat_1('#skF_4', A_20))=A_20 | ~r1_tarski(A_20, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8308, c_32])).
% 7.84/2.75  tff(c_8336, plain, (![A_20]: (k1_relat_1(k7_relat_1('#skF_4', A_20))=A_20 | ~r1_tarski(A_20, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6282, c_8327])).
% 7.84/2.75  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.84/2.75  tff(c_7956, plain, (![A_668, B_669, C_670, D_671]: (k2_partfun1(A_668, B_669, C_670, D_671)=k7_relat_1(C_670, D_671) | ~m1_subset_1(C_670, k1_zfmisc_1(k2_zfmisc_1(A_668, B_669))) | ~v1_funct_1(C_670))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.84/2.75  tff(c_7966, plain, (![D_671]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_671)=k7_relat_1('#skF_4', D_671) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_7956])).
% 7.84/2.75  tff(c_7980, plain, (![D_671]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_671)=k7_relat_1('#skF_4', D_671))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_7966])).
% 7.84/2.75  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.84/2.75  tff(c_1601, plain, (![C_171, A_172, B_173]: (v1_relat_1(C_171) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.84/2.75  tff(c_1620, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_1601])).
% 7.84/2.75  tff(c_2164, plain, (![A_218, B_219, C_220]: (k1_relset_1(A_218, B_219, C_220)=k1_relat_1(C_220) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.84/2.75  tff(c_2185, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_2164])).
% 7.84/2.75  tff(c_3333, plain, (![B_341, A_342, C_343]: (k1_xboole_0=B_341 | k1_relset_1(A_342, B_341, C_343)=A_342 | ~v1_funct_2(C_343, A_342, B_341) | ~m1_subset_1(C_343, k1_zfmisc_1(k2_zfmisc_1(A_342, B_341))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.84/2.75  tff(c_3347, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_3333])).
% 7.84/2.75  tff(c_3362, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2185, c_3347])).
% 7.84/2.75  tff(c_3363, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_81, c_3362])).
% 7.84/2.75  tff(c_3389, plain, (![A_20]: (k1_relat_1(k7_relat_1('#skF_4', A_20))=A_20 | ~r1_tarski(A_20, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3363, c_32])).
% 7.84/2.75  tff(c_3398, plain, (![A_20]: (k1_relat_1(k7_relat_1('#skF_4', A_20))=A_20 | ~r1_tarski(A_20, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1620, c_3389])).
% 7.84/2.75  tff(c_30, plain, (![B_19, A_18]: (r1_tarski(k7_relat_1(B_19, A_18), B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.84/2.75  tff(c_129, plain, (![A_60, B_61]: (r1_tarski(A_60, B_61) | ~m1_subset_1(A_60, k1_zfmisc_1(B_61)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.84/2.75  tff(c_138, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_129])).
% 7.84/2.75  tff(c_1651, plain, (![A_175, C_176, B_177]: (r1_tarski(A_175, C_176) | ~r1_tarski(B_177, C_176) | ~r1_tarski(A_175, B_177))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.84/2.75  tff(c_1838, plain, (![A_197]: (r1_tarski(A_197, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_197, '#skF_4'))), inference(resolution, [status(thm)], [c_138, c_1651])).
% 7.84/2.75  tff(c_22, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.84/2.75  tff(c_1617, plain, (![A_10, A_172, B_173]: (v1_relat_1(A_10) | ~r1_tarski(A_10, k2_zfmisc_1(A_172, B_173)))), inference(resolution, [status(thm)], [c_22, c_1601])).
% 7.84/2.75  tff(c_1849, plain, (![A_198]: (v1_relat_1(A_198) | ~r1_tarski(A_198, '#skF_4'))), inference(resolution, [status(thm)], [c_1838, c_1617])).
% 7.84/2.75  tff(c_1853, plain, (![A_18]: (v1_relat_1(k7_relat_1('#skF_4', A_18)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_1849])).
% 7.84/2.75  tff(c_1864, plain, (![A_18]: (v1_relat_1(k7_relat_1('#skF_4', A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_1620, c_1853])).
% 7.84/2.75  tff(c_34, plain, (![A_22]: (k7_relat_1(A_22, k1_relat_1(A_22))=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.84/2.75  tff(c_3392, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3363, c_34])).
% 7.84/2.75  tff(c_3400, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1620, c_3392])).
% 7.84/2.75  tff(c_1933, plain, (![A_204, B_205, A_206]: (r1_tarski(A_204, B_205) | ~r1_tarski(A_204, k7_relat_1(B_205, A_206)) | ~v1_relat_1(B_205))), inference(resolution, [status(thm)], [c_30, c_1651])).
% 7.84/2.75  tff(c_5684, plain, (![B_491, A_492, A_493]: (r1_tarski(k7_relat_1(k7_relat_1(B_491, A_492), A_493), B_491) | ~v1_relat_1(B_491) | ~v1_relat_1(k7_relat_1(B_491, A_492)))), inference(resolution, [status(thm)], [c_30, c_1933])).
% 7.84/2.75  tff(c_5788, plain, (![A_493]: (r1_tarski(k7_relat_1('#skF_4', A_493), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3400, c_5684])).
% 7.84/2.75  tff(c_5886, plain, (![A_493]: (r1_tarski(k7_relat_1('#skF_4', A_493), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1864, c_1620, c_5788])).
% 7.84/2.75  tff(c_1662, plain, (![A_175]: (r1_tarski(A_175, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_175, '#skF_4'))), inference(resolution, [status(thm)], [c_138, c_1651])).
% 7.84/2.75  tff(c_3064, plain, (![D_320, B_321, C_322, A_323]: (m1_subset_1(D_320, k1_zfmisc_1(k2_zfmisc_1(B_321, C_322))) | ~r1_tarski(k1_relat_1(D_320), B_321) | ~m1_subset_1(D_320, k1_zfmisc_1(k2_zfmisc_1(A_323, C_322))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.84/2.75  tff(c_5537, plain, (![A_481, B_482, C_483, A_484]: (m1_subset_1(A_481, k1_zfmisc_1(k2_zfmisc_1(B_482, C_483))) | ~r1_tarski(k1_relat_1(A_481), B_482) | ~r1_tarski(A_481, k2_zfmisc_1(A_484, C_483)))), inference(resolution, [status(thm)], [c_22, c_3064])).
% 7.84/2.75  tff(c_6184, plain, (![A_507, B_508]: (m1_subset_1(A_507, k1_zfmisc_1(k2_zfmisc_1(B_508, '#skF_2'))) | ~r1_tarski(k1_relat_1(A_507), B_508) | ~r1_tarski(A_507, '#skF_4'))), inference(resolution, [status(thm)], [c_1662, c_5537])).
% 7.84/2.75  tff(c_3200, plain, (![A_330, B_331, C_332, D_333]: (k2_partfun1(A_330, B_331, C_332, D_333)=k7_relat_1(C_332, D_333) | ~m1_subset_1(C_332, k1_zfmisc_1(k2_zfmisc_1(A_330, B_331))) | ~v1_funct_1(C_332))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.84/2.75  tff(c_3210, plain, (![D_333]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_333)=k7_relat_1('#skF_4', D_333) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_3200])).
% 7.84/2.75  tff(c_3224, plain, (![D_333]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_333)=k7_relat_1('#skF_4', D_333))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3210])).
% 7.84/2.75  tff(c_1457, plain, (![A_156, B_157, C_158, D_159]: (v1_funct_1(k2_partfun1(A_156, B_157, C_158, D_159)) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))) | ~v1_funct_1(C_158))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.84/2.75  tff(c_1465, plain, (![D_159]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_159)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_1457])).
% 7.84/2.75  tff(c_1474, plain, (![D_159]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_159)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1465])).
% 7.84/2.75  tff(c_62, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.84/2.75  tff(c_144, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_62])).
% 7.84/2.75  tff(c_1477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1474, c_144])).
% 7.84/2.75  tff(c_1478, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_62])).
% 7.84/2.75  tff(c_1589, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1478])).
% 7.84/2.75  tff(c_3248, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3224, c_1589])).
% 7.84/2.75  tff(c_6199, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_6184, c_3248])).
% 7.84/2.75  tff(c_6235, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5886, c_6199])).
% 7.84/2.75  tff(c_6246, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3398, c_6235])).
% 7.84/2.75  tff(c_6249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_6, c_6246])).
% 7.84/2.75  tff(c_6251, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_1478])).
% 7.84/2.75  tff(c_6854, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_6251, c_6833])).
% 7.84/2.75  tff(c_8005, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7980, c_7980, c_6854])).
% 7.84/2.75  tff(c_6250, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_1478])).
% 7.84/2.75  tff(c_8014, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7980, c_6250])).
% 7.84/2.75  tff(c_8013, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_7980, c_6251])).
% 7.84/2.75  tff(c_8465, plain, (![B_691, C_692, A_693]: (k1_xboole_0=B_691 | v1_funct_2(C_692, A_693, B_691) | k1_relset_1(A_693, B_691, C_692)!=A_693 | ~m1_subset_1(C_692, k1_zfmisc_1(k2_zfmisc_1(A_693, B_691))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.84/2.75  tff(c_8471, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_8013, c_8465])).
% 7.84/2.75  tff(c_8494, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_8014, c_81, c_8471])).
% 7.84/2.75  tff(c_8837, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8005, c_8494])).
% 7.84/2.75  tff(c_8844, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8336, c_8837])).
% 7.84/2.75  tff(c_8848, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_8844])).
% 7.84/2.75  tff(c_8849, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_64])).
% 7.84/2.75  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.84/2.75  tff(c_8851, plain, (![A_6]: (r1_tarski('#skF_1', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_8849, c_10])).
% 7.84/2.75  tff(c_14, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.84/2.75  tff(c_8864, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8849, c_8849, c_14])).
% 7.84/2.75  tff(c_8850, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_64])).
% 7.84/2.75  tff(c_8856, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8849, c_8850])).
% 7.84/2.75  tff(c_8862, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8856, c_68])).
% 7.84/2.75  tff(c_8865, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8864, c_8862])).
% 7.84/2.75  tff(c_9419, plain, (![A_785, B_786]: (r1_tarski(A_785, B_786) | ~m1_subset_1(A_785, k1_zfmisc_1(B_786)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.84/2.75  tff(c_9430, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_8865, c_9419])).
% 7.84/2.75  tff(c_9461, plain, (![B_790, A_791]: (B_790=A_791 | ~r1_tarski(B_790, A_791) | ~r1_tarski(A_791, B_790))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.84/2.75  tff(c_9463, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_9430, c_9461])).
% 7.84/2.75  tff(c_9474, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8851, c_9463])).
% 7.84/2.75  tff(c_8857, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8856, c_70])).
% 7.84/2.75  tff(c_9500, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9474, c_9474, c_8857])).
% 7.84/2.75  tff(c_18, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.84/2.75  tff(c_8889, plain, (![A_9]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_8849, c_18])).
% 7.84/2.75  tff(c_9531, plain, (![A_796]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_796)))), inference(demodulation, [status(thm), theory('equality')], [c_9474, c_8889])).
% 7.84/2.75  tff(c_36, plain, (![C_25, A_23, B_24]: (v1_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.84/2.75  tff(c_9539, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_9531, c_36])).
% 7.84/2.75  tff(c_9476, plain, (![A_6]: (A_6='#skF_1' | ~r1_tarski(A_6, '#skF_1'))), inference(resolution, [status(thm)], [c_8851, c_9461])).
% 7.84/2.75  tff(c_9570, plain, (![A_799]: (A_799='#skF_4' | ~r1_tarski(A_799, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9474, c_9474, c_9476])).
% 7.84/2.75  tff(c_9578, plain, (![A_18]: (k7_relat_1('#skF_4', A_18)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_9570])).
% 7.84/2.75  tff(c_9587, plain, (![A_18]: (k7_relat_1('#skF_4', A_18)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9539, c_9578])).
% 7.84/2.75  tff(c_9497, plain, (![A_9]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_9474, c_8889])).
% 7.84/2.75  tff(c_10233, plain, (![A_895, B_896, C_897, D_898]: (k2_partfun1(A_895, B_896, C_897, D_898)=k7_relat_1(C_897, D_898) | ~m1_subset_1(C_897, k1_zfmisc_1(k2_zfmisc_1(A_895, B_896))) | ~v1_funct_1(C_897))), inference(cnfTransformation, [status(thm)], [f_131])).
% 7.84/2.75  tff(c_10240, plain, (![A_895, B_896, D_898]: (k2_partfun1(A_895, B_896, '#skF_4', D_898)=k7_relat_1('#skF_4', D_898) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_9497, c_10233])).
% 7.84/2.75  tff(c_10246, plain, (![A_895, B_896, D_898]: (k2_partfun1(A_895, B_896, '#skF_4', D_898)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_9587, c_10240])).
% 7.84/2.75  tff(c_9471, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_9461])).
% 7.84/2.75  tff(c_9483, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8851, c_9471])).
% 7.84/2.75  tff(c_9491, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9474, c_9483])).
% 7.84/2.75  tff(c_8902, plain, (![A_720, B_721]: (r1_tarski(A_720, B_721) | ~m1_subset_1(A_720, k1_zfmisc_1(B_721)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.84/2.75  tff(c_8909, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_8865, c_8902])).
% 7.84/2.75  tff(c_8946, plain, (![B_729, A_730]: (B_729=A_730 | ~r1_tarski(B_729, A_730) | ~r1_tarski(A_730, B_729))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.84/2.75  tff(c_8950, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_8909, c_8946])).
% 7.84/2.75  tff(c_8960, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8851, c_8950])).
% 7.84/2.75  tff(c_8983, plain, (![A_9]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_8960, c_8889])).
% 7.84/2.75  tff(c_9397, plain, (![A_777, B_778, C_779, D_780]: (v1_funct_1(k2_partfun1(A_777, B_778, C_779, D_780)) | ~m1_subset_1(C_779, k1_zfmisc_1(k2_zfmisc_1(A_777, B_778))) | ~v1_funct_1(C_779))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.84/2.75  tff(c_9404, plain, (![A_777, B_778, D_780]: (v1_funct_1(k2_partfun1(A_777, B_778, '#skF_4', D_780)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_8983, c_9397])).
% 7.84/2.75  tff(c_9410, plain, (![A_777, B_778, D_780]: (v1_funct_1(k2_partfun1(A_777, B_778, '#skF_4', D_780)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_9404])).
% 7.84/2.75  tff(c_8956, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_8946])).
% 7.84/2.75  tff(c_8968, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8851, c_8956])).
% 7.84/2.75  tff(c_8900, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8856, c_8856, c_8856, c_8864, c_8856, c_8856, c_62])).
% 7.84/2.75  tff(c_8901, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_8900])).
% 7.84/2.75  tff(c_8969, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_8968, c_8901])).
% 7.84/2.75  tff(c_8976, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8960, c_8960, c_8960, c_8969])).
% 7.84/2.75  tff(c_9414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9410, c_8976])).
% 7.84/2.75  tff(c_9415, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_8900])).
% 7.84/2.75  tff(c_9643, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9491, c_9474, c_9474, c_9474, c_9491, c_9491, c_9474, c_9474, c_9474, c_9415])).
% 7.84/2.75  tff(c_9644, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_9643])).
% 7.84/2.75  tff(c_9760, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_22, c_9644])).
% 7.84/2.75  tff(c_10249, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10246, c_9760])).
% 7.84/2.75  tff(c_10254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_10249])).
% 7.84/2.75  tff(c_10256, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_9643])).
% 7.84/2.75  tff(c_20, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.84/2.75  tff(c_10418, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_10256, c_20])).
% 7.84/2.75  tff(c_9569, plain, (![A_6]: (A_6='#skF_4' | ~r1_tarski(A_6, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9474, c_9474, c_9476])).
% 7.84/2.75  tff(c_10439, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_10418, c_9569])).
% 7.84/2.75  tff(c_10255, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_9643])).
% 7.84/2.75  tff(c_10446, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10439, c_10255])).
% 7.84/2.75  tff(c_10453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9500, c_10446])).
% 7.84/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.84/2.75  
% 7.84/2.75  Inference rules
% 7.84/2.75  ----------------------
% 7.84/2.75  #Ref     : 0
% 7.84/2.75  #Sup     : 2265
% 7.84/2.75  #Fact    : 0
% 7.84/2.75  #Define  : 0
% 7.84/2.75  #Split   : 29
% 7.84/2.75  #Chain   : 0
% 7.84/2.75  #Close   : 0
% 7.84/2.75  
% 7.84/2.75  Ordering : KBO
% 7.84/2.75  
% 7.84/2.75  Simplification rules
% 7.84/2.75  ----------------------
% 7.84/2.75  #Subsume      : 332
% 7.84/2.75  #Demod        : 2325
% 7.84/2.75  #Tautology    : 1191
% 7.84/2.75  #SimpNegUnit  : 36
% 7.84/2.75  #BackRed      : 110
% 7.84/2.75  
% 7.84/2.75  #Partial instantiations: 0
% 7.84/2.75  #Strategies tried      : 1
% 7.84/2.75  
% 7.84/2.75  Timing (in seconds)
% 7.84/2.75  ----------------------
% 7.84/2.76  Preprocessing        : 0.37
% 7.84/2.76  Parsing              : 0.20
% 7.84/2.76  CNF conversion       : 0.02
% 7.84/2.76  Main loop            : 1.56
% 7.84/2.76  Inferencing          : 0.53
% 7.84/2.76  Reduction            : 0.58
% 7.84/2.76  Demodulation         : 0.42
% 7.84/2.76  BG Simplification    : 0.05
% 7.84/2.76  Subsumption          : 0.29
% 7.84/2.76  Abstraction          : 0.06
% 7.84/2.76  MUC search           : 0.00
% 7.84/2.76  Cooper               : 0.00
% 7.84/2.76  Total                : 1.99
% 7.84/2.76  Index Insertion      : 0.00
% 7.84/2.76  Index Deletion       : 0.00
% 7.84/2.76  Index Matching       : 0.00
% 7.84/2.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
