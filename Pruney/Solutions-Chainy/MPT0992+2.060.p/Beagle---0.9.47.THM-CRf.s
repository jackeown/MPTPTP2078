%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:40 EST 2020

% Result     : Theorem 6.20s
% Output     : CNFRefutation 6.50s
% Verified   : 
% Statistics : Number of formulae       :  163 (1230 expanded)
%              Number of leaves         :   35 ( 395 expanded)
%              Depth                    :   15
%              Number of atoms          :  274 (3832 expanded)
%              Number of equality atoms :   89 (1412 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_140,negated_conjecture,(
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

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_120,axiom,(
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

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_58,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_18,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_128,plain,(
    ! [B_52,A_53] :
      ( v1_relat_1(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_131,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_128])).

tff(c_134,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_131])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_3678,plain,(
    ! [A_461,B_462,C_463] :
      ( k1_relset_1(A_461,B_462,C_463) = k1_relat_1(C_463)
      | ~ m1_subset_1(C_463,k1_zfmisc_1(k2_zfmisc_1(A_461,B_462))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3692,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_3678])).

tff(c_4189,plain,(
    ! [B_517,A_518,C_519] :
      ( k1_xboole_0 = B_517
      | k1_relset_1(A_518,B_517,C_519) = A_518
      | ~ v1_funct_2(C_519,A_518,B_517)
      | ~ m1_subset_1(C_519,k1_zfmisc_1(k2_zfmisc_1(A_518,B_517))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4207,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_4189])).

tff(c_4224,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3692,c_4207])).

tff(c_4225,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_4224])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( k1_relat_1(k7_relat_1(B_17,A_16)) = A_16
      | ~ r1_tarski(A_16,k1_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4240,plain,(
    ! [A_16] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_16)) = A_16
      | ~ r1_tarski(A_16,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4225,c_24])).

tff(c_4246,plain,(
    ! [A_16] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_16)) = A_16
      | ~ r1_tarski(A_16,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_4240])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_3859,plain,(
    ! [A_497,B_498,C_499,D_500] :
      ( k2_partfun1(A_497,B_498,C_499,D_500) = k7_relat_1(C_499,D_500)
      | ~ m1_subset_1(C_499,k1_zfmisc_1(k2_zfmisc_1(A_497,B_498)))
      | ~ v1_funct_1(C_499) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3869,plain,(
    ! [D_500] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_500) = k7_relat_1('#skF_4',D_500)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_3859])).

tff(c_3879,plain,(
    ! [D_500] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_500) = k7_relat_1('#skF_4',D_500) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3869])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1693,plain,(
    ! [A_231,B_232,C_233] :
      ( k1_relset_1(A_231,B_232,C_233) = k1_relat_1(C_233)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1703,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1693])).

tff(c_2267,plain,(
    ! [B_309,A_310,C_311] :
      ( k1_xboole_0 = B_309
      | k1_relset_1(A_310,B_309,C_311) = A_310
      | ~ v1_funct_2(C_311,A_310,B_309)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_310,B_309))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2279,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_2267])).

tff(c_2291,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1703,c_2279])).

tff(c_2292,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2291])).

tff(c_2317,plain,(
    ! [A_16] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_16)) = A_16
      | ~ r1_tarski(A_16,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2292,c_24])).

tff(c_2323,plain,(
    ! [A_16] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_16)) = A_16
      | ~ r1_tarski(A_16,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_2317])).

tff(c_1964,plain,(
    ! [A_277,B_278,C_279,D_280] :
      ( k2_partfun1(A_277,B_278,C_279,D_280) = k7_relat_1(C_279,D_280)
      | ~ m1_subset_1(C_279,k1_zfmisc_1(k2_zfmisc_1(A_277,B_278)))
      | ~ v1_funct_1(C_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1970,plain,(
    ! [D_280] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_280) = k7_relat_1('#skF_4',D_280)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_1964])).

tff(c_1977,plain,(
    ! [D_280] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_280) = k7_relat_1('#skF_4',D_280) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1970])).

tff(c_2401,plain,(
    ! [A_316,B_317,C_318,D_319] :
      ( m1_subset_1(k2_partfun1(A_316,B_317,C_318,D_319),k1_zfmisc_1(k2_zfmisc_1(A_316,B_317)))
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(A_316,B_317)))
      | ~ v1_funct_1(C_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2430,plain,(
    ! [D_280] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_280),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1977,c_2401])).

tff(c_2453,plain,(
    ! [D_320] : m1_subset_1(k7_relat_1('#skF_4',D_320),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_2430])).

tff(c_32,plain,(
    ! [D_27,B_25,C_26,A_24] :
      ( m1_subset_1(D_27,k1_zfmisc_1(k2_zfmisc_1(B_25,C_26)))
      | ~ r1_tarski(k1_relat_1(D_27),B_25)
      | ~ m1_subset_1(D_27,k1_zfmisc_1(k2_zfmisc_1(A_24,C_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3482,plain,(
    ! [D_448,B_449] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_448),k1_zfmisc_1(k2_zfmisc_1(B_449,'#skF_2')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_448)),B_449) ) ),
    inference(resolution,[status(thm)],[c_2453,c_32])).

tff(c_307,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( v1_funct_1(k2_partfun1(A_94,B_95,C_96,D_97))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ v1_funct_1(C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_311,plain,(
    ! [D_97] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_97))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_307])).

tff(c_316,plain,(
    ! [D_97] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_97)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_311])).

tff(c_54,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_146,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_146])).

tff(c_320,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_352,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_320])).

tff(c_1979,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1977,c_352])).

tff(c_3539,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_3482,c_1979])).

tff(c_3556,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2323,c_3539])).

tff(c_3559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_6,c_3556])).

tff(c_3561,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_320])).

tff(c_3691,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_3561,c_3678])).

tff(c_3948,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3879,c_3879,c_3691])).

tff(c_3560,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_320])).

tff(c_3954,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3879,c_3560])).

tff(c_3953,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3879,c_3561])).

tff(c_4125,plain,(
    ! [B_512,C_513,A_514] :
      ( k1_xboole_0 = B_512
      | v1_funct_2(C_513,A_514,B_512)
      | k1_relset_1(A_514,B_512,C_513) != A_514
      | ~ m1_subset_1(C_513,k1_zfmisc_1(k2_zfmisc_1(A_514,B_512))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4131,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_3953,c_4125])).

tff(c_4155,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_3954,c_72,c_4131])).

tff(c_4614,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3948,c_4155])).

tff(c_4621,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4246,c_4614])).

tff(c_4625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4621])).

tff(c_4626,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4644,plain,(
    ! [B_541] : k2_zfmisc_1('#skF_1',B_541) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4626,c_4626,c_14])).

tff(c_4648,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4644,c_18])).

tff(c_4642,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4626,c_4626,c_14])).

tff(c_4627,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_4633,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4626,c_4627])).

tff(c_4639,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4633,c_60])).

tff(c_4643,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4642,c_4639])).

tff(c_4945,plain,(
    ! [B_594,A_595] :
      ( v1_relat_1(B_594)
      | ~ m1_subset_1(B_594,k1_zfmisc_1(A_595))
      | ~ v1_relat_1(A_595) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4948,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4643,c_4945])).

tff(c_4951,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4648,c_4948])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4653,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4626,c_4626,c_12])).

tff(c_4971,plain,(
    ! [C_603,A_604,B_605] :
      ( v4_relat_1(C_603,A_604)
      | ~ m1_subset_1(C_603,k1_zfmisc_1(k2_zfmisc_1(A_604,B_605))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4979,plain,(
    ! [C_608,A_609] :
      ( v4_relat_1(C_608,A_609)
      | ~ m1_subset_1(C_608,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4653,c_4971])).

tff(c_4983,plain,(
    ! [A_610] : v4_relat_1('#skF_4',A_610) ),
    inference(resolution,[status(thm)],[c_4643,c_4979])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4986,plain,(
    ! [A_610] :
      ( k7_relat_1('#skF_4',A_610) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4983,c_22])).

tff(c_4989,plain,(
    ! [A_610] : k7_relat_1('#skF_4',A_610) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4951,c_4986])).

tff(c_5513,plain,(
    ! [A_710,B_711,C_712,D_713] :
      ( k2_partfun1(A_710,B_711,C_712,D_713) = k7_relat_1(C_712,D_713)
      | ~ m1_subset_1(C_712,k1_zfmisc_1(k2_zfmisc_1(A_710,B_711)))
      | ~ v1_funct_1(C_712) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_5521,plain,(
    ! [A_714,C_715,D_716] :
      ( k2_partfun1(A_714,'#skF_1',C_715,D_716) = k7_relat_1(C_715,D_716)
      | ~ m1_subset_1(C_715,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_715) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4653,c_5513])).

tff(c_5525,plain,(
    ! [A_714,D_716] :
      ( k2_partfun1(A_714,'#skF_1','#skF_4',D_716) = k7_relat_1('#skF_4',D_716)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4643,c_5521])).

tff(c_5530,plain,(
    ! [A_714,D_716] : k2_partfun1(A_714,'#skF_1','#skF_4',D_716) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4989,c_5525])).

tff(c_4904,plain,(
    ! [A_584,B_585,C_586,D_587] :
      ( v1_funct_1(k2_partfun1(A_584,B_585,C_586,D_587))
      | ~ m1_subset_1(C_586,k1_zfmisc_1(k2_zfmisc_1(A_584,B_585)))
      | ~ v1_funct_1(C_586) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_4909,plain,(
    ! [A_588,C_589,D_590] :
      ( v1_funct_1(k2_partfun1(A_588,'#skF_1',C_589,D_590))
      | ~ m1_subset_1(C_589,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_589) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4653,c_4904])).

tff(c_4911,plain,(
    ! [A_588,D_590] :
      ( v1_funct_1(k2_partfun1(A_588,'#skF_1','#skF_4',D_590))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4643,c_4909])).

tff(c_4914,plain,(
    ! [A_588,D_590] : v1_funct_1(k2_partfun1(A_588,'#skF_1','#skF_4',D_590)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4911])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4628,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4626,c_8])).

tff(c_4672,plain,(
    ! [B_543,A_544] :
      ( B_543 = A_544
      | ~ r1_tarski(B_543,A_544)
      | ~ r1_tarski(A_544,B_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4678,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_4672])).

tff(c_4686,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4628,c_4678])).

tff(c_4693,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4686,c_4633,c_4686,c_4686,c_4633,c_4633,c_4686,c_4653,c_4633,c_4633,c_54])).

tff(c_4694,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4693])).

tff(c_4917,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4914,c_4694])).

tff(c_4918,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4693])).

tff(c_4964,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4918])).

tff(c_5532,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5530,c_4964])).

tff(c_5536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4643,c_5532])).

tff(c_5538,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4918])).

tff(c_16,plain,(
    ! [B_8,A_6] :
      ( v1_relat_1(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_5549,plain,
    ( v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_5538,c_16])).

tff(c_5553,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4648,c_5549])).

tff(c_5555,plain,(
    ! [C_721,A_722,B_723] :
      ( v4_relat_1(C_721,A_722)
      | ~ m1_subset_1(C_721,k1_zfmisc_1(k2_zfmisc_1(A_722,B_723))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5562,plain,(
    ! [C_724,A_725] :
      ( v4_relat_1(C_724,A_725)
      | ~ m1_subset_1(C_724,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4653,c_5555])).

tff(c_5567,plain,(
    ! [A_725] : v4_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_725) ),
    inference(resolution,[status(thm)],[c_5538,c_5562])).

tff(c_5571,plain,(
    ! [B_728,A_729] :
      ( k7_relat_1(B_728,A_729) = B_728
      | ~ v4_relat_1(B_728,A_729)
      | ~ v1_relat_1(B_728) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5574,plain,(
    ! [A_725] :
      ( k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_725) = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')
      | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_5567,c_5571])).

tff(c_5670,plain,(
    ! [A_738] : k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_738) = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5553,c_5574])).

tff(c_5593,plain,(
    ! [B_731,A_732] :
      ( k1_relat_1(k7_relat_1(B_731,A_732)) = A_732
      | ~ r1_tarski(A_732,k1_relat_1(B_731))
      | ~ v1_relat_1(B_731) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5602,plain,(
    ! [B_731] :
      ( k1_relat_1(k7_relat_1(B_731,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(B_731) ) ),
    inference(resolution,[status(thm)],[c_4628,c_5593])).

tff(c_5680,plain,
    ( k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5670,c_5602])).

tff(c_5688,plain,(
    k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5553,c_5680])).

tff(c_5604,plain,(
    ! [A_733,B_734,C_735] :
      ( k1_relset_1(A_733,B_734,C_735) = k1_relat_1(C_735)
      | ~ m1_subset_1(C_735,k1_zfmisc_1(k2_zfmisc_1(A_733,B_734))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_5704,plain,(
    ! [B_739,C_740] :
      ( k1_relset_1('#skF_1',B_739,C_740) = k1_relat_1(C_740)
      | ~ m1_subset_1(C_740,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4642,c_5604])).

tff(c_5706,plain,(
    ! [B_739] : k1_relset_1('#skF_1',B_739,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_5538,c_5704])).

tff(c_5710,plain,(
    ! [B_739] : k1_relset_1('#skF_1',B_739,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5688,c_5706])).

tff(c_40,plain,(
    ! [C_34,B_33] :
      ( v1_funct_2(C_34,k1_xboole_0,B_33)
      | k1_relset_1(k1_xboole_0,B_33,C_34) != k1_xboole_0
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_66,plain,(
    ! [C_34,B_33] :
      ( v1_funct_2(C_34,k1_xboole_0,B_33)
      | k1_relset_1(k1_xboole_0,B_33,C_34) != k1_xboole_0
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_40])).

tff(c_5838,plain,(
    ! [C_772,B_773] :
      ( v1_funct_2(C_772,'#skF_1',B_773)
      | k1_relset_1('#skF_1',B_773,C_772) != '#skF_1'
      | ~ m1_subset_1(C_772,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4626,c_4626,c_4626,c_4626,c_66])).

tff(c_5840,plain,(
    ! [B_773] :
      ( v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',B_773)
      | k1_relset_1('#skF_1',B_773,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_5538,c_5838])).

tff(c_5845,plain,(
    ! [B_773] : v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',B_773) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5710,c_5840])).

tff(c_5537,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_4918])).

tff(c_5865,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5845,c_5537])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:33:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.20/2.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.50/2.32  
% 6.50/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.50/2.32  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.50/2.32  
% 6.50/2.32  %Foreground sorts:
% 6.50/2.32  
% 6.50/2.32  
% 6.50/2.32  %Background operators:
% 6.50/2.32  
% 6.50/2.32  
% 6.50/2.32  %Foreground operators:
% 6.50/2.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.50/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.50/2.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.50/2.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.50/2.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.50/2.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.50/2.32  tff('#skF_2', type, '#skF_2': $i).
% 6.50/2.32  tff('#skF_3', type, '#skF_3': $i).
% 6.50/2.32  tff('#skF_1', type, '#skF_1': $i).
% 6.50/2.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.50/2.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.50/2.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.50/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.50/2.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.50/2.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.50/2.32  tff('#skF_4', type, '#skF_4': $i).
% 6.50/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.50/2.32  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.50/2.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.50/2.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.50/2.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.50/2.32  
% 6.50/2.34  tff(f_140, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 6.50/2.34  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.50/2.34  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.50/2.34  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.50/2.34  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.50/2.34  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 6.50/2.34  tff(f_120, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.50/2.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.50/2.34  tff(f_114, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 6.50/2.34  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 6.50/2.34  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.50/2.34  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.50/2.34  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 6.50/2.34  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.50/2.34  tff(c_58, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.50/2.34  tff(c_18, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.50/2.34  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.50/2.34  tff(c_128, plain, (![B_52, A_53]: (v1_relat_1(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.50/2.34  tff(c_131, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_128])).
% 6.50/2.34  tff(c_134, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_131])).
% 6.50/2.34  tff(c_56, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.50/2.34  tff(c_72, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_56])).
% 6.50/2.34  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.50/2.34  tff(c_3678, plain, (![A_461, B_462, C_463]: (k1_relset_1(A_461, B_462, C_463)=k1_relat_1(C_463) | ~m1_subset_1(C_463, k1_zfmisc_1(k2_zfmisc_1(A_461, B_462))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.50/2.34  tff(c_3692, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_3678])).
% 6.50/2.34  tff(c_4189, plain, (![B_517, A_518, C_519]: (k1_xboole_0=B_517 | k1_relset_1(A_518, B_517, C_519)=A_518 | ~v1_funct_2(C_519, A_518, B_517) | ~m1_subset_1(C_519, k1_zfmisc_1(k2_zfmisc_1(A_518, B_517))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.50/2.34  tff(c_4207, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_4189])).
% 6.50/2.34  tff(c_4224, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3692, c_4207])).
% 6.50/2.34  tff(c_4225, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_72, c_4224])).
% 6.50/2.34  tff(c_24, plain, (![B_17, A_16]: (k1_relat_1(k7_relat_1(B_17, A_16))=A_16 | ~r1_tarski(A_16, k1_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.50/2.34  tff(c_4240, plain, (![A_16]: (k1_relat_1(k7_relat_1('#skF_4', A_16))=A_16 | ~r1_tarski(A_16, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4225, c_24])).
% 6.50/2.34  tff(c_4246, plain, (![A_16]: (k1_relat_1(k7_relat_1('#skF_4', A_16))=A_16 | ~r1_tarski(A_16, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_4240])).
% 6.50/2.34  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.50/2.34  tff(c_3859, plain, (![A_497, B_498, C_499, D_500]: (k2_partfun1(A_497, B_498, C_499, D_500)=k7_relat_1(C_499, D_500) | ~m1_subset_1(C_499, k1_zfmisc_1(k2_zfmisc_1(A_497, B_498))) | ~v1_funct_1(C_499))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.50/2.34  tff(c_3869, plain, (![D_500]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_500)=k7_relat_1('#skF_4', D_500) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_3859])).
% 6.50/2.34  tff(c_3879, plain, (![D_500]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_500)=k7_relat_1('#skF_4', D_500))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3869])).
% 6.50/2.34  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.50/2.34  tff(c_1693, plain, (![A_231, B_232, C_233]: (k1_relset_1(A_231, B_232, C_233)=k1_relat_1(C_233) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.50/2.34  tff(c_1703, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_1693])).
% 6.50/2.34  tff(c_2267, plain, (![B_309, A_310, C_311]: (k1_xboole_0=B_309 | k1_relset_1(A_310, B_309, C_311)=A_310 | ~v1_funct_2(C_311, A_310, B_309) | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(A_310, B_309))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.50/2.34  tff(c_2279, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_2267])).
% 6.50/2.34  tff(c_2291, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1703, c_2279])).
% 6.50/2.34  tff(c_2292, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_72, c_2291])).
% 6.50/2.34  tff(c_2317, plain, (![A_16]: (k1_relat_1(k7_relat_1('#skF_4', A_16))=A_16 | ~r1_tarski(A_16, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2292, c_24])).
% 6.50/2.34  tff(c_2323, plain, (![A_16]: (k1_relat_1(k7_relat_1('#skF_4', A_16))=A_16 | ~r1_tarski(A_16, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_2317])).
% 6.50/2.34  tff(c_1964, plain, (![A_277, B_278, C_279, D_280]: (k2_partfun1(A_277, B_278, C_279, D_280)=k7_relat_1(C_279, D_280) | ~m1_subset_1(C_279, k1_zfmisc_1(k2_zfmisc_1(A_277, B_278))) | ~v1_funct_1(C_279))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.50/2.34  tff(c_1970, plain, (![D_280]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_280)=k7_relat_1('#skF_4', D_280) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_1964])).
% 6.50/2.34  tff(c_1977, plain, (![D_280]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_280)=k7_relat_1('#skF_4', D_280))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1970])).
% 6.50/2.34  tff(c_2401, plain, (![A_316, B_317, C_318, D_319]: (m1_subset_1(k2_partfun1(A_316, B_317, C_318, D_319), k1_zfmisc_1(k2_zfmisc_1(A_316, B_317))) | ~m1_subset_1(C_318, k1_zfmisc_1(k2_zfmisc_1(A_316, B_317))) | ~v1_funct_1(C_318))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.50/2.34  tff(c_2430, plain, (![D_280]: (m1_subset_1(k7_relat_1('#skF_4', D_280), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1977, c_2401])).
% 6.50/2.34  tff(c_2453, plain, (![D_320]: (m1_subset_1(k7_relat_1('#skF_4', D_320), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_2430])).
% 6.50/2.34  tff(c_32, plain, (![D_27, B_25, C_26, A_24]: (m1_subset_1(D_27, k1_zfmisc_1(k2_zfmisc_1(B_25, C_26))) | ~r1_tarski(k1_relat_1(D_27), B_25) | ~m1_subset_1(D_27, k1_zfmisc_1(k2_zfmisc_1(A_24, C_26))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.50/2.34  tff(c_3482, plain, (![D_448, B_449]: (m1_subset_1(k7_relat_1('#skF_4', D_448), k1_zfmisc_1(k2_zfmisc_1(B_449, '#skF_2'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_448)), B_449))), inference(resolution, [status(thm)], [c_2453, c_32])).
% 6.50/2.34  tff(c_307, plain, (![A_94, B_95, C_96, D_97]: (v1_funct_1(k2_partfun1(A_94, B_95, C_96, D_97)) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~v1_funct_1(C_96))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.50/2.34  tff(c_311, plain, (![D_97]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_97)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_307])).
% 6.50/2.34  tff(c_316, plain, (![D_97]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_97)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_311])).
% 6.50/2.34  tff(c_54, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.50/2.34  tff(c_146, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_54])).
% 6.50/2.34  tff(c_319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_316, c_146])).
% 6.50/2.34  tff(c_320, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_54])).
% 6.50/2.34  tff(c_352, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_320])).
% 6.50/2.34  tff(c_1979, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1977, c_352])).
% 6.50/2.34  tff(c_3539, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(resolution, [status(thm)], [c_3482, c_1979])).
% 6.50/2.34  tff(c_3556, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2323, c_3539])).
% 6.50/2.34  tff(c_3559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_6, c_3556])).
% 6.50/2.34  tff(c_3561, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_320])).
% 6.50/2.34  tff(c_3691, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_3561, c_3678])).
% 6.50/2.34  tff(c_3948, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3879, c_3879, c_3691])).
% 6.50/2.34  tff(c_3560, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_320])).
% 6.50/2.34  tff(c_3954, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3879, c_3560])).
% 6.50/2.34  tff(c_3953, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3879, c_3561])).
% 6.50/2.34  tff(c_4125, plain, (![B_512, C_513, A_514]: (k1_xboole_0=B_512 | v1_funct_2(C_513, A_514, B_512) | k1_relset_1(A_514, B_512, C_513)!=A_514 | ~m1_subset_1(C_513, k1_zfmisc_1(k2_zfmisc_1(A_514, B_512))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.50/2.34  tff(c_4131, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_3953, c_4125])).
% 6.50/2.34  tff(c_4155, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_3954, c_72, c_4131])).
% 6.50/2.34  tff(c_4614, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3948, c_4155])).
% 6.50/2.34  tff(c_4621, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4246, c_4614])).
% 6.50/2.34  tff(c_4625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_4621])).
% 6.50/2.34  tff(c_4626, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_56])).
% 6.50/2.34  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.50/2.34  tff(c_4644, plain, (![B_541]: (k2_zfmisc_1('#skF_1', B_541)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4626, c_4626, c_14])).
% 6.50/2.34  tff(c_4648, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4644, c_18])).
% 6.50/2.34  tff(c_4642, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4626, c_4626, c_14])).
% 6.50/2.34  tff(c_4627, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_56])).
% 6.50/2.34  tff(c_4633, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4626, c_4627])).
% 6.50/2.34  tff(c_4639, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4633, c_60])).
% 6.50/2.34  tff(c_4643, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4642, c_4639])).
% 6.50/2.34  tff(c_4945, plain, (![B_594, A_595]: (v1_relat_1(B_594) | ~m1_subset_1(B_594, k1_zfmisc_1(A_595)) | ~v1_relat_1(A_595))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.50/2.34  tff(c_4948, plain, (v1_relat_1('#skF_4') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4643, c_4945])).
% 6.50/2.34  tff(c_4951, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4648, c_4948])).
% 6.50/2.34  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.50/2.34  tff(c_4653, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4626, c_4626, c_12])).
% 6.50/2.34  tff(c_4971, plain, (![C_603, A_604, B_605]: (v4_relat_1(C_603, A_604) | ~m1_subset_1(C_603, k1_zfmisc_1(k2_zfmisc_1(A_604, B_605))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.50/2.34  tff(c_4979, plain, (![C_608, A_609]: (v4_relat_1(C_608, A_609) | ~m1_subset_1(C_608, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4653, c_4971])).
% 6.50/2.34  tff(c_4983, plain, (![A_610]: (v4_relat_1('#skF_4', A_610))), inference(resolution, [status(thm)], [c_4643, c_4979])).
% 6.50/2.34  tff(c_22, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.50/2.34  tff(c_4986, plain, (![A_610]: (k7_relat_1('#skF_4', A_610)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4983, c_22])).
% 6.50/2.34  tff(c_4989, plain, (![A_610]: (k7_relat_1('#skF_4', A_610)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4951, c_4986])).
% 6.50/2.34  tff(c_5513, plain, (![A_710, B_711, C_712, D_713]: (k2_partfun1(A_710, B_711, C_712, D_713)=k7_relat_1(C_712, D_713) | ~m1_subset_1(C_712, k1_zfmisc_1(k2_zfmisc_1(A_710, B_711))) | ~v1_funct_1(C_712))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.50/2.34  tff(c_5521, plain, (![A_714, C_715, D_716]: (k2_partfun1(A_714, '#skF_1', C_715, D_716)=k7_relat_1(C_715, D_716) | ~m1_subset_1(C_715, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_715))), inference(superposition, [status(thm), theory('equality')], [c_4653, c_5513])).
% 6.50/2.34  tff(c_5525, plain, (![A_714, D_716]: (k2_partfun1(A_714, '#skF_1', '#skF_4', D_716)=k7_relat_1('#skF_4', D_716) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4643, c_5521])).
% 6.50/2.34  tff(c_5530, plain, (![A_714, D_716]: (k2_partfun1(A_714, '#skF_1', '#skF_4', D_716)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_4989, c_5525])).
% 6.50/2.34  tff(c_4904, plain, (![A_584, B_585, C_586, D_587]: (v1_funct_1(k2_partfun1(A_584, B_585, C_586, D_587)) | ~m1_subset_1(C_586, k1_zfmisc_1(k2_zfmisc_1(A_584, B_585))) | ~v1_funct_1(C_586))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.50/2.34  tff(c_4909, plain, (![A_588, C_589, D_590]: (v1_funct_1(k2_partfun1(A_588, '#skF_1', C_589, D_590)) | ~m1_subset_1(C_589, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_589))), inference(superposition, [status(thm), theory('equality')], [c_4653, c_4904])).
% 6.50/2.34  tff(c_4911, plain, (![A_588, D_590]: (v1_funct_1(k2_partfun1(A_588, '#skF_1', '#skF_4', D_590)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4643, c_4909])).
% 6.50/2.34  tff(c_4914, plain, (![A_588, D_590]: (v1_funct_1(k2_partfun1(A_588, '#skF_1', '#skF_4', D_590)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_4911])).
% 6.50/2.34  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.50/2.34  tff(c_4628, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4626, c_8])).
% 6.50/2.34  tff(c_4672, plain, (![B_543, A_544]: (B_543=A_544 | ~r1_tarski(B_543, A_544) | ~r1_tarski(A_544, B_543))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.50/2.34  tff(c_4678, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_4672])).
% 6.50/2.34  tff(c_4686, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4628, c_4678])).
% 6.50/2.34  tff(c_4693, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4686, c_4633, c_4686, c_4686, c_4633, c_4633, c_4686, c_4653, c_4633, c_4633, c_54])).
% 6.50/2.34  tff(c_4694, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_4693])).
% 6.50/2.34  tff(c_4917, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4914, c_4694])).
% 6.50/2.34  tff(c_4918, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_4693])).
% 6.50/2.34  tff(c_4964, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_4918])).
% 6.50/2.34  tff(c_5532, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5530, c_4964])).
% 6.50/2.34  tff(c_5536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4643, c_5532])).
% 6.50/2.34  tff(c_5538, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_4918])).
% 6.50/2.34  tff(c_16, plain, (![B_8, A_6]: (v1_relat_1(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.50/2.34  tff(c_5549, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_5538, c_16])).
% 6.50/2.34  tff(c_5553, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4648, c_5549])).
% 6.50/2.34  tff(c_5555, plain, (![C_721, A_722, B_723]: (v4_relat_1(C_721, A_722) | ~m1_subset_1(C_721, k1_zfmisc_1(k2_zfmisc_1(A_722, B_723))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.50/2.34  tff(c_5562, plain, (![C_724, A_725]: (v4_relat_1(C_724, A_725) | ~m1_subset_1(C_724, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4653, c_5555])).
% 6.50/2.34  tff(c_5567, plain, (![A_725]: (v4_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_725))), inference(resolution, [status(thm)], [c_5538, c_5562])).
% 6.50/2.34  tff(c_5571, plain, (![B_728, A_729]: (k7_relat_1(B_728, A_729)=B_728 | ~v4_relat_1(B_728, A_729) | ~v1_relat_1(B_728))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.50/2.34  tff(c_5574, plain, (![A_725]: (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_725)=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(resolution, [status(thm)], [c_5567, c_5571])).
% 6.50/2.34  tff(c_5670, plain, (![A_738]: (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_738)=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5553, c_5574])).
% 6.50/2.34  tff(c_5593, plain, (![B_731, A_732]: (k1_relat_1(k7_relat_1(B_731, A_732))=A_732 | ~r1_tarski(A_732, k1_relat_1(B_731)) | ~v1_relat_1(B_731))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.50/2.34  tff(c_5602, plain, (![B_731]: (k1_relat_1(k7_relat_1(B_731, '#skF_1'))='#skF_1' | ~v1_relat_1(B_731))), inference(resolution, [status(thm)], [c_4628, c_5593])).
% 6.50/2.34  tff(c_5680, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1' | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5670, c_5602])).
% 6.50/2.34  tff(c_5688, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5553, c_5680])).
% 6.50/2.34  tff(c_5604, plain, (![A_733, B_734, C_735]: (k1_relset_1(A_733, B_734, C_735)=k1_relat_1(C_735) | ~m1_subset_1(C_735, k1_zfmisc_1(k2_zfmisc_1(A_733, B_734))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.50/2.34  tff(c_5704, plain, (![B_739, C_740]: (k1_relset_1('#skF_1', B_739, C_740)=k1_relat_1(C_740) | ~m1_subset_1(C_740, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4642, c_5604])).
% 6.50/2.34  tff(c_5706, plain, (![B_739]: (k1_relset_1('#skF_1', B_739, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(resolution, [status(thm)], [c_5538, c_5704])).
% 6.50/2.34  tff(c_5710, plain, (![B_739]: (k1_relset_1('#skF_1', B_739, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5688, c_5706])).
% 6.50/2.34  tff(c_40, plain, (![C_34, B_33]: (v1_funct_2(C_34, k1_xboole_0, B_33) | k1_relset_1(k1_xboole_0, B_33, C_34)!=k1_xboole_0 | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_33))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.50/2.34  tff(c_66, plain, (![C_34, B_33]: (v1_funct_2(C_34, k1_xboole_0, B_33) | k1_relset_1(k1_xboole_0, B_33, C_34)!=k1_xboole_0 | ~m1_subset_1(C_34, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_40])).
% 6.50/2.34  tff(c_5838, plain, (![C_772, B_773]: (v1_funct_2(C_772, '#skF_1', B_773) | k1_relset_1('#skF_1', B_773, C_772)!='#skF_1' | ~m1_subset_1(C_772, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4626, c_4626, c_4626, c_4626, c_66])).
% 6.50/2.34  tff(c_5840, plain, (![B_773]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', B_773) | k1_relset_1('#skF_1', B_773, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))!='#skF_1')), inference(resolution, [status(thm)], [c_5538, c_5838])).
% 6.50/2.34  tff(c_5845, plain, (![B_773]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', B_773))), inference(demodulation, [status(thm), theory('equality')], [c_5710, c_5840])).
% 6.50/2.34  tff(c_5537, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_4918])).
% 6.50/2.34  tff(c_5865, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5845, c_5537])).
% 6.50/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.50/2.34  
% 6.50/2.34  Inference rules
% 6.50/2.34  ----------------------
% 6.50/2.34  #Ref     : 0
% 6.50/2.34  #Sup     : 1299
% 6.50/2.34  #Fact    : 0
% 6.50/2.34  #Define  : 0
% 6.50/2.34  #Split   : 27
% 6.50/2.34  #Chain   : 0
% 6.50/2.34  #Close   : 0
% 6.50/2.34  
% 6.50/2.34  Ordering : KBO
% 6.50/2.34  
% 6.50/2.34  Simplification rules
% 6.50/2.34  ----------------------
% 6.50/2.34  #Subsume      : 225
% 6.50/2.34  #Demod        : 1030
% 6.50/2.34  #Tautology    : 582
% 6.50/2.34  #SimpNegUnit  : 68
% 6.50/2.34  #BackRed      : 56
% 6.50/2.34  
% 6.50/2.34  #Partial instantiations: 0
% 6.50/2.34  #Strategies tried      : 1
% 6.50/2.34  
% 6.50/2.34  Timing (in seconds)
% 6.50/2.34  ----------------------
% 6.50/2.35  Preprocessing        : 0.37
% 6.50/2.35  Parsing              : 0.20
% 6.50/2.35  CNF conversion       : 0.02
% 6.50/2.35  Main loop            : 1.14
% 6.50/2.35  Inferencing          : 0.40
% 6.50/2.35  Reduction            : 0.40
% 6.50/2.35  Demodulation         : 0.29
% 6.50/2.35  BG Simplification    : 0.04
% 6.50/2.35  Subsumption          : 0.19
% 6.50/2.35  Abstraction          : 0.05
% 6.50/2.35  MUC search           : 0.00
% 6.50/2.35  Cooper               : 0.00
% 6.50/2.35  Total                : 1.56
% 6.50/2.35  Index Insertion      : 0.00
% 6.50/2.35  Index Deletion       : 0.00
% 6.50/2.35  Index Matching       : 0.00
% 6.50/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
