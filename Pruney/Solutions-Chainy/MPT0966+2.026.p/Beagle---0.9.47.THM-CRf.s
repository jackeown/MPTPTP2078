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
% DateTime   : Thu Dec  3 10:11:12 EST 2020

% Result     : Theorem 8.65s
% Output     : CNFRefutation 8.96s
% Verified   : 
% Statistics : Number of formulae       :  333 (5473 expanded)
%              Number of leaves         :   35 (1718 expanded)
%              Depth                    :   16
%              Number of atoms          :  580 (14876 expanded)
%              Number of equality atoms :  258 (5226 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_124,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_26,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_12108,plain,(
    ! [B_1082,A_1083] :
      ( v1_relat_1(B_1082)
      | ~ m1_subset_1(B_1082,k1_zfmisc_1(A_1083))
      | ~ v1_relat_1(A_1083) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12114,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_12108])).

tff(c_12118,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_12114])).

tff(c_12181,plain,(
    ! [C_1091,A_1092,B_1093] :
      ( v4_relat_1(C_1091,A_1092)
      | ~ m1_subset_1(C_1091,k1_zfmisc_1(k2_zfmisc_1(A_1092,B_1093))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12196,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_12181])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12359,plain,(
    ! [A_1120,B_1121,C_1122] :
      ( k2_relset_1(A_1120,B_1121,C_1122) = k2_relat_1(C_1122)
      | ~ m1_subset_1(C_1122,k1_zfmisc_1(k2_zfmisc_1(A_1120,B_1121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12374,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_12359])).

tff(c_58,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_12377,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12374,c_58])).

tff(c_12453,plain,(
    ! [C_1132,A_1133,B_1134] :
      ( m1_subset_1(C_1132,k1_zfmisc_1(k2_zfmisc_1(A_1133,B_1134)))
      | ~ r1_tarski(k2_relat_1(C_1132),B_1134)
      | ~ r1_tarski(k1_relat_1(C_1132),A_1133)
      | ~ v1_relat_1(C_1132) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_3935,plain,(
    ! [A_357,B_358,C_359] :
      ( k1_relset_1(A_357,B_358,C_359) = k1_relat_1(C_359)
      | ~ m1_subset_1(C_359,k1_zfmisc_1(k2_zfmisc_1(A_357,B_358))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3950,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_3935])).

tff(c_4116,plain,(
    ! [B_382,A_383,C_384] :
      ( k1_xboole_0 = B_382
      | k1_relset_1(A_383,B_382,C_384) = A_383
      | ~ v1_funct_2(C_384,A_383,B_382)
      | ~ m1_subset_1(C_384,k1_zfmisc_1(k2_zfmisc_1(A_383,B_382))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4126,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_4116])).

tff(c_4137,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3950,c_4126])).

tff(c_4138,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4137])).

tff(c_398,plain,(
    ! [B_82,A_83] :
      ( v1_relat_1(B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_83))
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_404,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_398])).

tff(c_408,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_404])).

tff(c_3814,plain,(
    ! [A_344,B_345,C_346] :
      ( k2_relset_1(A_344,B_345,C_346) = k2_relat_1(C_346)
      | ~ m1_subset_1(C_346,k1_zfmisc_1(k2_zfmisc_1(A_344,B_345))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3829,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_3814])).

tff(c_3834,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3829,c_58])).

tff(c_3971,plain,(
    ! [C_363,A_364,B_365] :
      ( m1_subset_1(C_363,k1_zfmisc_1(k2_zfmisc_1(A_364,B_365)))
      | ~ r1_tarski(k2_relat_1(C_363),B_365)
      | ~ r1_tarski(k1_relat_1(C_363),A_364)
      | ~ v1_relat_1(C_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5470,plain,(
    ! [C_489,A_490,B_491] :
      ( r1_tarski(C_489,k2_zfmisc_1(A_490,B_491))
      | ~ r1_tarski(k2_relat_1(C_489),B_491)
      | ~ r1_tarski(k1_relat_1(C_489),A_490)
      | ~ v1_relat_1(C_489) ) ),
    inference(resolution,[status(thm)],[c_3971,c_16])).

tff(c_5474,plain,(
    ! [A_490] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_490,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_490)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3834,c_5470])).

tff(c_5488,plain,(
    ! [A_492] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_492,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_492) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_4138,c_5474])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3949,plain,(
    ! [A_357,B_358,A_6] :
      ( k1_relset_1(A_357,B_358,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_357,B_358)) ) ),
    inference(resolution,[status(thm)],[c_18,c_3935])).

tff(c_5494,plain,(
    ! [A_492] :
      ( k1_relset_1(A_492,'#skF_3','#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',A_492) ) ),
    inference(resolution,[status(thm)],[c_5488,c_3949])).

tff(c_5521,plain,(
    ! [A_493] :
      ( k1_relset_1(A_493,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_493) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4138,c_5494])).

tff(c_5526,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_5521])).

tff(c_5484,plain,(
    ! [A_490] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_490,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_490) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_4138,c_5474])).

tff(c_5937,plain,(
    ! [B_512,A_513,A_514] :
      ( k1_xboole_0 = B_512
      | k1_relset_1(A_513,B_512,A_514) = A_513
      | ~ v1_funct_2(A_514,A_513,B_512)
      | ~ r1_tarski(A_514,k2_zfmisc_1(A_513,B_512)) ) ),
    inference(resolution,[status(thm)],[c_18,c_4116])).

tff(c_5966,plain,(
    ! [A_490] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1(A_490,'#skF_3','#skF_4') = A_490
      | ~ v1_funct_2('#skF_4',A_490,'#skF_3')
      | ~ r1_tarski('#skF_1',A_490) ) ),
    inference(resolution,[status(thm)],[c_5484,c_5937])).

tff(c_6083,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5966])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6160,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6083,c_8])).

tff(c_113,plain,(
    ! [B_41,A_42] :
      ( B_41 = A_42
      | ~ r1_tarski(B_41,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_123,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_113])).

tff(c_378,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_3833,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3829,c_378])).

tff(c_6251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6160,c_3833])).

tff(c_6253,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5966])).

tff(c_4301,plain,(
    ! [B_399,C_400,A_401] :
      ( k1_xboole_0 = B_399
      | v1_funct_2(C_400,A_401,B_399)
      | k1_relset_1(A_401,B_399,C_400) != A_401
      | ~ m1_subset_1(C_400,k1_zfmisc_1(k2_zfmisc_1(A_401,B_399))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6414,plain,(
    ! [B_532,A_533,A_534] :
      ( k1_xboole_0 = B_532
      | v1_funct_2(A_533,A_534,B_532)
      | k1_relset_1(A_534,B_532,A_533) != A_534
      | ~ r1_tarski(A_533,k2_zfmisc_1(A_534,B_532)) ) ),
    inference(resolution,[status(thm)],[c_18,c_4301])).

tff(c_6420,plain,(
    ! [A_490] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2('#skF_4',A_490,'#skF_3')
      | k1_relset_1(A_490,'#skF_3','#skF_4') != A_490
      | ~ r1_tarski('#skF_1',A_490) ) ),
    inference(resolution,[status(thm)],[c_5484,c_6414])).

tff(c_6475,plain,(
    ! [A_537] :
      ( v1_funct_2('#skF_4',A_537,'#skF_3')
      | k1_relset_1(A_537,'#skF_3','#skF_4') != A_537
      | ~ r1_tarski('#skF_1',A_537) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6253,c_6420])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_66,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_54])).

tff(c_151,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_6484,plain,
    ( k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_6475,c_151])).

tff(c_6490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5526,c_6484])).

tff(c_6491,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_6803,plain,(
    ! [A_583,B_584,C_585] :
      ( k2_relset_1(A_583,B_584,C_585) = k2_relat_1(C_585)
      | ~ m1_subset_1(C_585,k1_zfmisc_1(k2_zfmisc_1(A_583,B_584))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6810,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_6803])).

tff(c_6819,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6491,c_6810])).

tff(c_6508,plain,(
    ! [B_538,A_539] :
      ( v1_relat_1(B_538)
      | ~ m1_subset_1(B_538,k1_zfmisc_1(A_539))
      | ~ v1_relat_1(A_539) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6514,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_6508])).

tff(c_6518,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6514])).

tff(c_28,plain,(
    ! [A_15] :
      ( k1_relat_1(A_15) = k1_xboole_0
      | k2_relat_1(A_15) != k1_xboole_0
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6522,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6518,c_28])).

tff(c_6523,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6522])).

tff(c_6820,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6819,c_6523])).

tff(c_6690,plain,(
    ! [A_572,B_573,C_574] :
      ( k1_relset_1(A_572,B_573,C_574) = k1_relat_1(C_574)
      | ~ m1_subset_1(C_574,k1_zfmisc_1(k2_zfmisc_1(A_572,B_573))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6705,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_6690])).

tff(c_7164,plain,(
    ! [B_628,A_629,C_630] :
      ( k1_xboole_0 = B_628
      | k1_relset_1(A_629,B_628,C_630) = A_629
      | ~ v1_funct_2(C_630,A_629,B_628)
      | ~ m1_subset_1(C_630,k1_zfmisc_1(k2_zfmisc_1(A_629,B_628))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_7174,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_7164])).

tff(c_7185,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_6705,c_7174])).

tff(c_7186,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_7185])).

tff(c_6907,plain,(
    ! [C_597,A_598,B_599] :
      ( m1_subset_1(C_597,k1_zfmisc_1(k2_zfmisc_1(A_598,B_599)))
      | ~ r1_tarski(k2_relat_1(C_597),B_599)
      | ~ r1_tarski(k1_relat_1(C_597),A_598)
      | ~ v1_relat_1(C_597) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_8339,plain,(
    ! [C_717,A_718,B_719] :
      ( r1_tarski(C_717,k2_zfmisc_1(A_718,B_719))
      | ~ r1_tarski(k2_relat_1(C_717),B_719)
      | ~ r1_tarski(k1_relat_1(C_717),A_718)
      | ~ v1_relat_1(C_717) ) ),
    inference(resolution,[status(thm)],[c_6907,c_16])).

tff(c_8345,plain,(
    ! [A_718,B_719] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_718,B_719))
      | ~ r1_tarski('#skF_3',B_719)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_718)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6819,c_8339])).

tff(c_8360,plain,(
    ! [A_720,B_721] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_720,B_721))
      | ~ r1_tarski('#skF_3',B_721)
      | ~ r1_tarski('#skF_1',A_720) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6518,c_7186,c_8345])).

tff(c_6704,plain,(
    ! [A_572,B_573,A_6] :
      ( k1_relset_1(A_572,B_573,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_572,B_573)) ) ),
    inference(resolution,[status(thm)],[c_18,c_6690])).

tff(c_8363,plain,(
    ! [A_720,B_721] :
      ( k1_relset_1(A_720,B_721,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_3',B_721)
      | ~ r1_tarski('#skF_1',A_720) ) ),
    inference(resolution,[status(thm)],[c_8360,c_6704])).

tff(c_8396,plain,(
    ! [A_722,B_723] :
      ( k1_relset_1(A_722,B_723,'#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_3',B_723)
      | ~ r1_tarski('#skF_1',A_722) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7186,c_8363])).

tff(c_8401,plain,(
    ! [A_724] :
      ( k1_relset_1(A_724,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_724) ) ),
    inference(resolution,[status(thm)],[c_6,c_8396])).

tff(c_8406,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_8401])).

tff(c_8356,plain,(
    ! [A_718,B_719] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_718,B_719))
      | ~ r1_tarski('#skF_3',B_719)
      | ~ r1_tarski('#skF_1',A_718) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6518,c_7186,c_8345])).

tff(c_7043,plain,(
    ! [B_615,C_616,A_617] :
      ( k1_xboole_0 = B_615
      | v1_funct_2(C_616,A_617,B_615)
      | k1_relset_1(A_617,B_615,C_616) != A_617
      | ~ m1_subset_1(C_616,k1_zfmisc_1(k2_zfmisc_1(A_617,B_615))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_8751,plain,(
    ! [B_742,A_743,A_744] :
      ( k1_xboole_0 = B_742
      | v1_funct_2(A_743,A_744,B_742)
      | k1_relset_1(A_744,B_742,A_743) != A_744
      | ~ r1_tarski(A_743,k2_zfmisc_1(A_744,B_742)) ) ),
    inference(resolution,[status(thm)],[c_18,c_7043])).

tff(c_8892,plain,(
    ! [B_750,A_751] :
      ( k1_xboole_0 = B_750
      | v1_funct_2('#skF_4',A_751,B_750)
      | k1_relset_1(A_751,B_750,'#skF_4') != A_751
      | ~ r1_tarski('#skF_3',B_750)
      | ~ r1_tarski('#skF_1',A_751) ) ),
    inference(resolution,[status(thm)],[c_8356,c_8751])).

tff(c_8901,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_8892,c_151])).

tff(c_8906,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_8406,c_8901])).

tff(c_8908,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6820,c_8906])).

tff(c_8910,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6522])).

tff(c_9270,plain,(
    ! [A_802,B_803,C_804] :
      ( k2_relset_1(A_802,B_803,C_804) = k2_relat_1(C_804)
      | ~ m1_subset_1(C_804,k1_zfmisc_1(k2_zfmisc_1(A_802,B_803))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_9277,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_9270])).

tff(c_9286,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6491,c_8910,c_9277])).

tff(c_9312,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9286,c_74])).

tff(c_8909,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6522])).

tff(c_9172,plain,(
    ! [A_792,B_793,C_794] :
      ( k1_relset_1(A_792,B_793,C_794) = k1_relat_1(C_794)
      | ~ m1_subset_1(C_794,k1_zfmisc_1(k2_zfmisc_1(A_792,B_793))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_9179,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_9172])).

tff(c_9188,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8909,c_9179])).

tff(c_9293,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9286,c_9188])).

tff(c_52,plain,(
    ! [B_29,A_28,C_30] :
      ( k1_xboole_0 = B_29
      | k1_relset_1(A_28,B_29,C_30) = A_28
      | ~ v1_funct_2(C_30,A_28,B_29)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_9574,plain,(
    ! [B_826,A_827,C_828] :
      ( B_826 = '#skF_3'
      | k1_relset_1(A_827,B_826,C_828) = A_827
      | ~ v1_funct_2(C_828,A_827,B_826)
      | ~ m1_subset_1(C_828,k1_zfmisc_1(k2_zfmisc_1(A_827,B_826))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9286,c_52])).

tff(c_9590,plain,
    ( '#skF_2' = '#skF_3'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_9574])).

tff(c_9596,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_9293,c_9590])).

tff(c_9597,plain,(
    '#skF_3' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_9312,c_9596])).

tff(c_9313,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9286,c_8])).

tff(c_9612,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9597,c_9313])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_9311,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9286,c_9286,c_14])).

tff(c_9607,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9597,c_9597,c_9311])).

tff(c_103,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_107,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_103])).

tff(c_122,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_107,c_113])).

tff(c_8985,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_9773,plain,(
    ~ r1_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9607,c_8985])).

tff(c_9778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9612,c_9773])).

tff(c_9779,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_9782,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9779,c_60])).

tff(c_9987,plain,(
    ! [A_864,B_865,C_866] :
      ( k2_relset_1(A_864,B_865,C_866) = k2_relat_1(C_866)
      | ~ m1_subset_1(C_866,k1_zfmisc_1(k2_zfmisc_1(A_864,B_865))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10127,plain,(
    ! [C_882] :
      ( k2_relset_1('#skF_1','#skF_2',C_882) = k2_relat_1(C_882)
      | ~ m1_subset_1(C_882,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9779,c_9987])).

tff(c_10130,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_9782,c_10127])).

tff(c_10136,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6491,c_8910,c_10130])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_97,plain,(
    ! [A_35,B_36] : v1_relat_1(k2_zfmisc_1(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_99,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_97])).

tff(c_142,plain,(
    ! [A_44] :
      ( k1_relat_1(A_44) = k1_xboole_0
      | k2_relat_1(A_44) != k1_xboole_0
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_149,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99,c_142])).

tff(c_152,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_201,plain,(
    ! [A_51] :
      ( k2_relat_1(A_51) = k1_xboole_0
      | k1_relat_1(A_51) != k1_xboole_0
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_207,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99,c_201])).

tff(c_216,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_207])).

tff(c_42,plain,(
    ! [A_28] :
      ( v1_funct_2(k1_xboole_0,A_28,k1_xboole_0)
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_28,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_70,plain,(
    ! [A_28] :
      ( v1_funct_2(k1_xboole_0,A_28,k1_xboole_0)
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_42])).

tff(c_338,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_341,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_338])).

tff(c_345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_341])).

tff(c_347,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_311,plain,(
    ! [C_73,A_74,B_75] :
      ( v4_relat_1(C_73,A_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_321,plain,(
    ! [C_73,A_4] :
      ( v4_relat_1(C_73,A_4)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_311])).

tff(c_366,plain,(
    ! [A_80] : v4_relat_1(k1_xboole_0,A_80) ),
    inference(resolution,[status(thm)],[c_347,c_321])).

tff(c_277,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(k1_relat_1(B_67),A_68)
      | ~ v4_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_128,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_113])).

tff(c_297,plain,(
    ! [B_67] :
      ( k1_relat_1(B_67) = k1_xboole_0
      | ~ v4_relat_1(B_67,k1_xboole_0)
      | ~ v1_relat_1(B_67) ) ),
    inference(resolution,[status(thm)],[c_277,c_128])).

tff(c_370,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_366,c_297])).

tff(c_373,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_370])).

tff(c_375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_216,c_373])).

tff(c_376,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_10158,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10136,c_10136,c_376])).

tff(c_10165,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10136,c_8])).

tff(c_10189,plain,(
    ! [A_883,B_884,C_885] :
      ( k1_relset_1(A_883,B_884,C_885) = k1_relat_1(C_885)
      | ~ m1_subset_1(C_885,k1_zfmisc_1(k2_zfmisc_1(A_883,B_884))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10204,plain,(
    ! [C_888] :
      ( k1_relset_1('#skF_1','#skF_2',C_888) = k1_relat_1(C_888)
      | ~ m1_subset_1(C_888,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9779,c_10189])).

tff(c_10402,plain,(
    ! [A_903] :
      ( k1_relset_1('#skF_1','#skF_2',A_903) = k1_relat_1(A_903)
      | ~ r1_tarski(A_903,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_10204])).

tff(c_10406,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10165,c_10402])).

tff(c_10416,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10158,c_10406])).

tff(c_10161,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10136,c_99])).

tff(c_377,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_10157,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10136,c_10136,c_377])).

tff(c_10442,plain,(
    ! [C_908,A_909,B_910] :
      ( m1_subset_1(C_908,k1_zfmisc_1(k2_zfmisc_1(A_909,B_910)))
      | ~ r1_tarski(k2_relat_1(C_908),B_910)
      | ~ r1_tarski(k1_relat_1(C_908),A_909)
      | ~ v1_relat_1(C_908) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_10478,plain,(
    ! [C_911] :
      ( m1_subset_1(C_911,k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1(C_911),'#skF_2')
      | ~ r1_tarski(k1_relat_1(C_911),'#skF_1')
      | ~ v1_relat_1(C_911) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9779,c_10442])).

tff(c_10484,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski('#skF_3','#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10157,c_10478])).

tff(c_10488,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10161,c_10165,c_10158,c_10165,c_10484])).

tff(c_10164,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10136,c_74])).

tff(c_48,plain,(
    ! [B_29,C_30,A_28] :
      ( k1_xboole_0 = B_29
      | v1_funct_2(C_30,A_28,B_29)
      | k1_relset_1(A_28,B_29,C_30) != A_28
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_10560,plain,(
    ! [B_915,C_916,A_917] :
      ( B_915 = '#skF_3'
      | v1_funct_2(C_916,A_917,B_915)
      | k1_relset_1(A_917,B_915,C_916) != A_917
      | ~ m1_subset_1(C_916,k1_zfmisc_1(k2_zfmisc_1(A_917,B_915))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10136,c_48])).

tff(c_10572,plain,(
    ! [C_916] :
      ( '#skF_2' = '#skF_3'
      | v1_funct_2(C_916,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_916) != '#skF_1'
      | ~ m1_subset_1(C_916,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9779,c_10560])).

tff(c_10642,plain,(
    ! [C_921] :
      ( v1_funct_2(C_921,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_921) != '#skF_1'
      | ~ m1_subset_1(C_921,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10164,c_10572])).

tff(c_10645,plain,
    ( v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_10488,c_10642])).

tff(c_10654,plain,
    ( v1_funct_2('#skF_3','#skF_1','#skF_2')
    | '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10416,c_10645])).

tff(c_10658,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_10654])).

tff(c_10156,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10136,c_8909])).

tff(c_10207,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_9782,c_10204])).

tff(c_10213,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10156,c_10207])).

tff(c_10693,plain,(
    ! [B_925,A_926,C_927] :
      ( B_925 = '#skF_3'
      | k1_relset_1(A_926,B_925,C_927) = A_926
      | ~ v1_funct_2(C_927,A_926,B_925)
      | ~ m1_subset_1(C_927,k1_zfmisc_1(k2_zfmisc_1(A_926,B_925))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10136,c_52])).

tff(c_10705,plain,(
    ! [C_927] :
      ( '#skF_2' = '#skF_3'
      | k1_relset_1('#skF_1','#skF_2',C_927) = '#skF_1'
      | ~ v1_funct_2(C_927,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_927,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9779,c_10693])).

tff(c_10745,plain,(
    ! [C_932] :
      ( k1_relset_1('#skF_1','#skF_2',C_932) = '#skF_1'
      | ~ v1_funct_2(C_932,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_932,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10164,c_10705])).

tff(c_10751,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_9782,c_10745])).

tff(c_10761,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_10213,c_10751])).

tff(c_10763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10658,c_10761])).

tff(c_10765,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10654])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_9790,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_9779,c_10])).

tff(c_9795,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_9790])).

tff(c_9809,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_9795])).

tff(c_10150,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10136,c_9809])).

tff(c_10795,plain,(
    '#skF_1' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10765,c_10150])).

tff(c_10163,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10136,c_10136,c_14])).

tff(c_11001,plain,(
    ! [B_942] : k2_zfmisc_1('#skF_1',B_942) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10765,c_10765,c_10163])).

tff(c_11035,plain,(
    '#skF_1' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_11001,c_9779])).

tff(c_11053,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10795,c_11035])).

tff(c_11055,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9795])).

tff(c_11054,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9795])).

tff(c_11075,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11055,c_11054])).

tff(c_11063,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11054,c_11054,c_376])).

tff(c_11115,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11075,c_11075,c_11063])).

tff(c_11067,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11054,c_11054,c_12])).

tff(c_11164,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11075,c_11075,c_11067])).

tff(c_11294,plain,(
    ! [A_968,B_969,C_970] :
      ( k1_relset_1(A_968,B_969,C_970) = k1_relat_1(C_970)
      | ~ m1_subset_1(C_970,k1_zfmisc_1(k2_zfmisc_1(A_968,B_969))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_11595,plain,(
    ! [A_1009,C_1010] :
      ( k1_relset_1(A_1009,'#skF_4',C_1010) = k1_relat_1(C_1010)
      | ~ m1_subset_1(C_1010,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11164,c_11294])).

tff(c_11597,plain,(
    ! [A_1009] : k1_relset_1(A_1009,'#skF_4','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_9782,c_11595])).

tff(c_11602,plain,(
    ! [A_1009] : k1_relset_1(A_1009,'#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11115,c_11597])).

tff(c_11062,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11054,c_11054,c_377])).

tff(c_11110,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11075,c_11075,c_11062])).

tff(c_11068,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11054,c_11054,c_14])).

tff(c_11146,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11075,c_11075,c_11068])).

tff(c_11333,plain,(
    ! [A_977,B_978,C_979] :
      ( k2_relset_1(A_977,B_978,C_979) = k2_relat_1(C_979)
      | ~ m1_subset_1(C_979,k1_zfmisc_1(k2_zfmisc_1(A_977,B_978))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_11721,plain,(
    ! [B_1025,C_1026] :
      ( k2_relset_1('#skF_4',B_1025,C_1026) = k2_relat_1(C_1026)
      | ~ m1_subset_1(C_1026,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11146,c_11333])).

tff(c_11723,plain,(
    ! [B_1025] : k2_relset_1('#skF_4',B_1025,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_9782,c_11721])).

tff(c_11728,plain,(
    ! [B_1025] : k2_relset_1('#skF_4',B_1025,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11110,c_11723])).

tff(c_11092,plain,(
    k2_relset_1('#skF_4','#skF_2','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11075,c_6491])).

tff(c_11730,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11728,c_11092])).

tff(c_46,plain,(
    ! [C_30,B_29] :
      ( v1_funct_2(C_30,k1_xboole_0,B_29)
      | k1_relset_1(k1_xboole_0,B_29,C_30) != k1_xboole_0
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_68,plain,(
    ! [C_30,B_29] :
      ( v1_funct_2(C_30,k1_xboole_0,B_29)
      | k1_relset_1(k1_xboole_0,B_29,C_30) != k1_xboole_0
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_46])).

tff(c_11575,plain,(
    ! [C_1006,B_1007] :
      ( v1_funct_2(C_1006,'#skF_4',B_1007)
      | k1_relset_1('#skF_4',B_1007,C_1006) != '#skF_4'
      | ~ m1_subset_1(C_1006,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11055,c_11055,c_11055,c_11055,c_68])).

tff(c_11583,plain,(
    ! [B_1008] :
      ( v1_funct_2('#skF_4','#skF_4',B_1008)
      | k1_relset_1('#skF_4',B_1008,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_9782,c_11575])).

tff(c_11093,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11075,c_151])).

tff(c_11594,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_11583,c_11093])).

tff(c_11746,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11730,c_11594])).

tff(c_11750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11602,c_11746])).

tff(c_11751,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_12471,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12453,c_11751])).

tff(c_12490,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12118,c_12377,c_12471])).

tff(c_12494,plain,
    ( ~ v4_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_12490])).

tff(c_12498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12118,c_12196,c_12494])).

tff(c_12499,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_12501,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12499,c_8])).

tff(c_12513,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12499,c_12499,c_14])).

tff(c_12500,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_12506,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12499,c_12500])).

tff(c_12544,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12513,c_12506,c_60])).

tff(c_12545,plain,(
    ! [A_1140,B_1141] :
      ( r1_tarski(A_1140,B_1141)
      | ~ m1_subset_1(A_1140,k1_zfmisc_1(B_1141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12549,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_12544,c_12545])).

tff(c_13225,plain,(
    ! [B_1216,A_1217] :
      ( B_1216 = A_1217
      | ~ r1_tarski(B_1216,A_1217)
      | ~ r1_tarski(A_1217,B_1216) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_13227,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_12549,c_13225])).

tff(c_13236,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12501,c_13227])).

tff(c_13123,plain,(
    ! [B_1209,A_1210] :
      ( B_1209 = A_1210
      | ~ r1_tarski(B_1209,A_1210)
      | ~ r1_tarski(A_1210,B_1209) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_13125,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_12549,c_13123])).

tff(c_13134,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12501,c_13125])).

tff(c_13001,plain,(
    ! [B_1201,A_1202] :
      ( B_1201 = A_1202
      | ~ r1_tarski(B_1201,A_1202)
      | ~ r1_tarski(A_1202,B_1201) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_13003,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_12549,c_13001])).

tff(c_13012,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12501,c_13003])).

tff(c_12623,plain,(
    ! [B_1150,A_1151] :
      ( B_1150 = A_1151
      | ~ r1_tarski(B_1150,A_1151)
      | ~ r1_tarski(A_1151,B_1150) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12625,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_12549,c_12623])).

tff(c_12634,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12501,c_12625])).

tff(c_12521,plain,(
    ! [A_1137,B_1138] : v1_relat_1(k2_zfmisc_1(A_1137,B_1138)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12523,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12513,c_12521])).

tff(c_12565,plain,(
    ! [B_1145,A_1146] :
      ( v1_relat_1(B_1145)
      | ~ m1_subset_1(B_1145,k1_zfmisc_1(A_1146))
      | ~ v1_relat_1(A_1146) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12571,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12544,c_12565])).

tff(c_12575,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12523,c_12571])).

tff(c_12555,plain,(
    ! [A_15] :
      ( k1_relat_1(A_15) = '#skF_1'
      | k2_relat_1(A_15) != '#skF_1'
      | ~ v1_relat_1(A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12499,c_12499,c_28])).

tff(c_12579,plain,
    ( k1_relat_1('#skF_4') = '#skF_1'
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_12575,c_12555])).

tff(c_12583,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_12579])).

tff(c_30,plain,(
    ! [A_15] :
      ( k2_relat_1(A_15) = k1_xboole_0
      | k1_relat_1(A_15) != k1_xboole_0
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12606,plain,(
    ! [A_1149] :
      ( k2_relat_1(A_1149) = '#skF_1'
      | k1_relat_1(A_1149) != '#skF_1'
      | ~ v1_relat_1(A_1149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12499,c_12499,c_30])).

tff(c_12609,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | k1_relat_1('#skF_4') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_12575,c_12606])).

tff(c_12618,plain,(
    k1_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_12583,c_12609])).

tff(c_12643,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12634,c_12618])).

tff(c_12654,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12634,c_12634,c_12513])).

tff(c_12832,plain,(
    ! [C_1173,A_1174,B_1175] :
      ( v4_relat_1(C_1173,A_1174)
      | ~ m1_subset_1(C_1173,k1_zfmisc_1(k2_zfmisc_1(A_1174,B_1175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12858,plain,(
    ! [A_1184,A_1185,B_1186] :
      ( v4_relat_1(A_1184,A_1185)
      | ~ r1_tarski(A_1184,k2_zfmisc_1(A_1185,B_1186)) ) ),
    inference(resolution,[status(thm)],[c_18,c_12832])).

tff(c_12880,plain,(
    ! [A_1185,B_1186] : v4_relat_1(k2_zfmisc_1(A_1185,B_1186),A_1185) ),
    inference(resolution,[status(thm)],[c_6,c_12858])).

tff(c_12804,plain,(
    ! [B_1167,A_1168] :
      ( r1_tarski(k1_relat_1(B_1167),A_1168)
      | ~ v4_relat_1(B_1167,A_1168)
      | ~ v1_relat_1(B_1167) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12636,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_12501,c_12623])).

tff(c_12733,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ r1_tarski(A_3,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12634,c_12634,c_12636])).

tff(c_12934,plain,(
    ! [B_1197] :
      ( k1_relat_1(B_1197) = '#skF_4'
      | ~ v4_relat_1(B_1197,'#skF_4')
      | ~ v1_relat_1(B_1197) ) ),
    inference(resolution,[status(thm)],[c_12804,c_12733])).

tff(c_12938,plain,(
    ! [B_1186] :
      ( k1_relat_1(k2_zfmisc_1('#skF_4',B_1186)) = '#skF_4'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_4',B_1186)) ) ),
    inference(resolution,[status(thm)],[c_12880,c_12934])).

tff(c_12949,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_12654,c_12938])).

tff(c_12951,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12643,c_12949])).

tff(c_12953,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12579])).

tff(c_13021,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13012,c_12953])).

tff(c_12556,plain,(
    ! [A_1144] :
      ( k1_relat_1(A_1144) = '#skF_1'
      | k2_relat_1(A_1144) != '#skF_1'
      | ~ v1_relat_1(A_1144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12499,c_12499,c_28])).

tff(c_12563,plain,
    ( k1_relat_1('#skF_1') = '#skF_1'
    | k2_relat_1('#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_12523,c_12556])).

tff(c_12580,plain,(
    k2_relat_1('#skF_1') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_12563])).

tff(c_13024,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13012,c_13012,c_12580])).

tff(c_13070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13021,c_13024])).

tff(c_13072,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12563])).

tff(c_13145,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13134,c_13134,c_13072])).

tff(c_13083,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_12579])).

tff(c_13144,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13134,c_13083])).

tff(c_13193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13145,c_13144])).

tff(c_13194,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12579])).

tff(c_13244,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13236,c_13194])).

tff(c_13256,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13236,c_12501])).

tff(c_13605,plain,(
    ! [A_1266,B_1267,C_1268] :
      ( k1_relset_1(A_1266,B_1267,C_1268) = k1_relat_1(C_1268)
      | ~ m1_subset_1(C_1268,k1_zfmisc_1(k2_zfmisc_1(A_1266,B_1267))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_13918,plain,(
    ! [A_1307,B_1308,A_1309] :
      ( k1_relset_1(A_1307,B_1308,A_1309) = k1_relat_1(A_1309)
      | ~ r1_tarski(A_1309,k2_zfmisc_1(A_1307,B_1308)) ) ),
    inference(resolution,[status(thm)],[c_18,c_13605])).

tff(c_13932,plain,(
    ! [A_1307,B_1308] : k1_relset_1(A_1307,B_1308,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_13256,c_13918])).

tff(c_13939,plain,(
    ! [A_1307,B_1308] : k1_relset_1(A_1307,B_1308,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13244,c_13932])).

tff(c_13250,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13236,c_12544])).

tff(c_13258,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13236,c_12499])).

tff(c_14112,plain,(
    ! [C_1333,B_1334] :
      ( v1_funct_2(C_1333,'#skF_4',B_1334)
      | k1_relset_1('#skF_4',B_1334,C_1333) != '#skF_4'
      | ~ m1_subset_1(C_1333,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13258,c_13258,c_13258,c_13258,c_68])).

tff(c_14114,plain,(
    ! [B_1334] :
      ( v1_funct_2('#skF_4','#skF_4',B_1334)
      | k1_relset_1('#skF_4',B_1334,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_13250,c_14112])).

tff(c_14120,plain,(
    ! [B_1334] : v1_funct_2('#skF_4','#skF_4',B_1334) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13939,c_14114])).

tff(c_13078,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12544,c_12513,c_66])).

tff(c_13246,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13236,c_13078])).

tff(c_14125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14120,c_13246])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:48:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.65/3.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.96/3.10  
% 8.96/3.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.96/3.11  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.96/3.11  
% 8.96/3.11  %Foreground sorts:
% 8.96/3.11  
% 8.96/3.11  
% 8.96/3.11  %Background operators:
% 8.96/3.11  
% 8.96/3.11  
% 8.96/3.11  %Foreground operators:
% 8.96/3.11  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.96/3.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.96/3.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.96/3.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.96/3.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.96/3.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.96/3.11  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.96/3.11  tff('#skF_2', type, '#skF_2': $i).
% 8.96/3.11  tff('#skF_3', type, '#skF_3': $i).
% 8.96/3.11  tff('#skF_1', type, '#skF_1': $i).
% 8.96/3.11  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.96/3.11  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.96/3.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.96/3.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.96/3.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.96/3.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.96/3.11  tff('#skF_4', type, '#skF_4': $i).
% 8.96/3.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.96/3.11  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.96/3.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.96/3.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.96/3.11  
% 8.96/3.14  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.96/3.14  tff(f_124, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 8.96/3.14  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.96/3.14  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.96/3.14  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 8.96/3.14  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.96/3.14  tff(f_86, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 8.96/3.14  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.96/3.14  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.96/3.14  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.96/3.14  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.96/3.14  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.96/3.14  tff(f_64, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 8.96/3.14  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.96/3.14  tff(c_26, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.96/3.14  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.96/3.14  tff(c_12108, plain, (![B_1082, A_1083]: (v1_relat_1(B_1082) | ~m1_subset_1(B_1082, k1_zfmisc_1(A_1083)) | ~v1_relat_1(A_1083))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.96/3.14  tff(c_12114, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_12108])).
% 8.96/3.14  tff(c_12118, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_12114])).
% 8.96/3.14  tff(c_12181, plain, (![C_1091, A_1092, B_1093]: (v4_relat_1(C_1091, A_1092) | ~m1_subset_1(C_1091, k1_zfmisc_1(k2_zfmisc_1(A_1092, B_1093))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.96/3.14  tff(c_12196, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_12181])).
% 8.96/3.14  tff(c_24, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.96/3.14  tff(c_12359, plain, (![A_1120, B_1121, C_1122]: (k2_relset_1(A_1120, B_1121, C_1122)=k2_relat_1(C_1122) | ~m1_subset_1(C_1122, k1_zfmisc_1(k2_zfmisc_1(A_1120, B_1121))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.96/3.14  tff(c_12374, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_12359])).
% 8.96/3.14  tff(c_58, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.96/3.14  tff(c_12377, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12374, c_58])).
% 8.96/3.14  tff(c_12453, plain, (![C_1132, A_1133, B_1134]: (m1_subset_1(C_1132, k1_zfmisc_1(k2_zfmisc_1(A_1133, B_1134))) | ~r1_tarski(k2_relat_1(C_1132), B_1134) | ~r1_tarski(k1_relat_1(C_1132), A_1133) | ~v1_relat_1(C_1132))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.96/3.14  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.96/3.14  tff(c_56, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.96/3.14  tff(c_74, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_56])).
% 8.96/3.14  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.96/3.14  tff(c_3935, plain, (![A_357, B_358, C_359]: (k1_relset_1(A_357, B_358, C_359)=k1_relat_1(C_359) | ~m1_subset_1(C_359, k1_zfmisc_1(k2_zfmisc_1(A_357, B_358))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.96/3.14  tff(c_3950, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_3935])).
% 8.96/3.14  tff(c_4116, plain, (![B_382, A_383, C_384]: (k1_xboole_0=B_382 | k1_relset_1(A_383, B_382, C_384)=A_383 | ~v1_funct_2(C_384, A_383, B_382) | ~m1_subset_1(C_384, k1_zfmisc_1(k2_zfmisc_1(A_383, B_382))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.96/3.14  tff(c_4126, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_4116])).
% 8.96/3.14  tff(c_4137, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3950, c_4126])).
% 8.96/3.14  tff(c_4138, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_74, c_4137])).
% 8.96/3.14  tff(c_398, plain, (![B_82, A_83]: (v1_relat_1(B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(A_83)) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.96/3.14  tff(c_404, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_398])).
% 8.96/3.14  tff(c_408, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_404])).
% 8.96/3.14  tff(c_3814, plain, (![A_344, B_345, C_346]: (k2_relset_1(A_344, B_345, C_346)=k2_relat_1(C_346) | ~m1_subset_1(C_346, k1_zfmisc_1(k2_zfmisc_1(A_344, B_345))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.96/3.14  tff(c_3829, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_3814])).
% 8.96/3.14  tff(c_3834, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3829, c_58])).
% 8.96/3.14  tff(c_3971, plain, (![C_363, A_364, B_365]: (m1_subset_1(C_363, k1_zfmisc_1(k2_zfmisc_1(A_364, B_365))) | ~r1_tarski(k2_relat_1(C_363), B_365) | ~r1_tarski(k1_relat_1(C_363), A_364) | ~v1_relat_1(C_363))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.96/3.14  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.96/3.14  tff(c_5470, plain, (![C_489, A_490, B_491]: (r1_tarski(C_489, k2_zfmisc_1(A_490, B_491)) | ~r1_tarski(k2_relat_1(C_489), B_491) | ~r1_tarski(k1_relat_1(C_489), A_490) | ~v1_relat_1(C_489))), inference(resolution, [status(thm)], [c_3971, c_16])).
% 8.96/3.14  tff(c_5474, plain, (![A_490]: (r1_tarski('#skF_4', k2_zfmisc_1(A_490, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_490) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_3834, c_5470])).
% 8.96/3.14  tff(c_5488, plain, (![A_492]: (r1_tarski('#skF_4', k2_zfmisc_1(A_492, '#skF_3')) | ~r1_tarski('#skF_1', A_492))), inference(demodulation, [status(thm), theory('equality')], [c_408, c_4138, c_5474])).
% 8.96/3.14  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.96/3.14  tff(c_3949, plain, (![A_357, B_358, A_6]: (k1_relset_1(A_357, B_358, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_357, B_358)))), inference(resolution, [status(thm)], [c_18, c_3935])).
% 8.96/3.14  tff(c_5494, plain, (![A_492]: (k1_relset_1(A_492, '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', A_492))), inference(resolution, [status(thm)], [c_5488, c_3949])).
% 8.96/3.14  tff(c_5521, plain, (![A_493]: (k1_relset_1(A_493, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_493))), inference(demodulation, [status(thm), theory('equality')], [c_4138, c_5494])).
% 8.96/3.14  tff(c_5526, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_5521])).
% 8.96/3.14  tff(c_5484, plain, (![A_490]: (r1_tarski('#skF_4', k2_zfmisc_1(A_490, '#skF_3')) | ~r1_tarski('#skF_1', A_490))), inference(demodulation, [status(thm), theory('equality')], [c_408, c_4138, c_5474])).
% 8.96/3.14  tff(c_5937, plain, (![B_512, A_513, A_514]: (k1_xboole_0=B_512 | k1_relset_1(A_513, B_512, A_514)=A_513 | ~v1_funct_2(A_514, A_513, B_512) | ~r1_tarski(A_514, k2_zfmisc_1(A_513, B_512)))), inference(resolution, [status(thm)], [c_18, c_4116])).
% 8.96/3.14  tff(c_5966, plain, (![A_490]: (k1_xboole_0='#skF_3' | k1_relset_1(A_490, '#skF_3', '#skF_4')=A_490 | ~v1_funct_2('#skF_4', A_490, '#skF_3') | ~r1_tarski('#skF_1', A_490))), inference(resolution, [status(thm)], [c_5484, c_5937])).
% 8.96/3.14  tff(c_6083, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_5966])).
% 8.96/3.14  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.96/3.14  tff(c_6160, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_6083, c_8])).
% 8.96/3.14  tff(c_113, plain, (![B_41, A_42]: (B_41=A_42 | ~r1_tarski(B_41, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.96/3.14  tff(c_123, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_113])).
% 8.96/3.14  tff(c_378, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_123])).
% 8.96/3.14  tff(c_3833, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3829, c_378])).
% 8.96/3.14  tff(c_6251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6160, c_3833])).
% 8.96/3.14  tff(c_6253, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_5966])).
% 8.96/3.14  tff(c_4301, plain, (![B_399, C_400, A_401]: (k1_xboole_0=B_399 | v1_funct_2(C_400, A_401, B_399) | k1_relset_1(A_401, B_399, C_400)!=A_401 | ~m1_subset_1(C_400, k1_zfmisc_1(k2_zfmisc_1(A_401, B_399))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.96/3.14  tff(c_6414, plain, (![B_532, A_533, A_534]: (k1_xboole_0=B_532 | v1_funct_2(A_533, A_534, B_532) | k1_relset_1(A_534, B_532, A_533)!=A_534 | ~r1_tarski(A_533, k2_zfmisc_1(A_534, B_532)))), inference(resolution, [status(thm)], [c_18, c_4301])).
% 8.96/3.14  tff(c_6420, plain, (![A_490]: (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', A_490, '#skF_3') | k1_relset_1(A_490, '#skF_3', '#skF_4')!=A_490 | ~r1_tarski('#skF_1', A_490))), inference(resolution, [status(thm)], [c_5484, c_6414])).
% 8.96/3.14  tff(c_6475, plain, (![A_537]: (v1_funct_2('#skF_4', A_537, '#skF_3') | k1_relset_1(A_537, '#skF_3', '#skF_4')!=A_537 | ~r1_tarski('#skF_1', A_537))), inference(negUnitSimplification, [status(thm)], [c_6253, c_6420])).
% 8.96/3.14  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.96/3.14  tff(c_54, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.96/3.14  tff(c_66, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_54])).
% 8.96/3.14  tff(c_151, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 8.96/3.14  tff(c_6484, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_6475, c_151])).
% 8.96/3.14  tff(c_6490, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5526, c_6484])).
% 8.96/3.14  tff(c_6491, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_123])).
% 8.96/3.14  tff(c_6803, plain, (![A_583, B_584, C_585]: (k2_relset_1(A_583, B_584, C_585)=k2_relat_1(C_585) | ~m1_subset_1(C_585, k1_zfmisc_1(k2_zfmisc_1(A_583, B_584))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.96/3.14  tff(c_6810, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_6803])).
% 8.96/3.14  tff(c_6819, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6491, c_6810])).
% 8.96/3.14  tff(c_6508, plain, (![B_538, A_539]: (v1_relat_1(B_538) | ~m1_subset_1(B_538, k1_zfmisc_1(A_539)) | ~v1_relat_1(A_539))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.96/3.14  tff(c_6514, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_6508])).
% 8.96/3.14  tff(c_6518, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_6514])).
% 8.96/3.14  tff(c_28, plain, (![A_15]: (k1_relat_1(A_15)=k1_xboole_0 | k2_relat_1(A_15)!=k1_xboole_0 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.96/3.14  tff(c_6522, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6518, c_28])).
% 8.96/3.14  tff(c_6523, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6522])).
% 8.96/3.14  tff(c_6820, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6819, c_6523])).
% 8.96/3.14  tff(c_6690, plain, (![A_572, B_573, C_574]: (k1_relset_1(A_572, B_573, C_574)=k1_relat_1(C_574) | ~m1_subset_1(C_574, k1_zfmisc_1(k2_zfmisc_1(A_572, B_573))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.96/3.14  tff(c_6705, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_6690])).
% 8.96/3.14  tff(c_7164, plain, (![B_628, A_629, C_630]: (k1_xboole_0=B_628 | k1_relset_1(A_629, B_628, C_630)=A_629 | ~v1_funct_2(C_630, A_629, B_628) | ~m1_subset_1(C_630, k1_zfmisc_1(k2_zfmisc_1(A_629, B_628))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.96/3.14  tff(c_7174, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_7164])).
% 8.96/3.14  tff(c_7185, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_6705, c_7174])).
% 8.96/3.14  tff(c_7186, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_74, c_7185])).
% 8.96/3.14  tff(c_6907, plain, (![C_597, A_598, B_599]: (m1_subset_1(C_597, k1_zfmisc_1(k2_zfmisc_1(A_598, B_599))) | ~r1_tarski(k2_relat_1(C_597), B_599) | ~r1_tarski(k1_relat_1(C_597), A_598) | ~v1_relat_1(C_597))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.96/3.14  tff(c_8339, plain, (![C_717, A_718, B_719]: (r1_tarski(C_717, k2_zfmisc_1(A_718, B_719)) | ~r1_tarski(k2_relat_1(C_717), B_719) | ~r1_tarski(k1_relat_1(C_717), A_718) | ~v1_relat_1(C_717))), inference(resolution, [status(thm)], [c_6907, c_16])).
% 8.96/3.14  tff(c_8345, plain, (![A_718, B_719]: (r1_tarski('#skF_4', k2_zfmisc_1(A_718, B_719)) | ~r1_tarski('#skF_3', B_719) | ~r1_tarski(k1_relat_1('#skF_4'), A_718) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6819, c_8339])).
% 8.96/3.14  tff(c_8360, plain, (![A_720, B_721]: (r1_tarski('#skF_4', k2_zfmisc_1(A_720, B_721)) | ~r1_tarski('#skF_3', B_721) | ~r1_tarski('#skF_1', A_720))), inference(demodulation, [status(thm), theory('equality')], [c_6518, c_7186, c_8345])).
% 8.96/3.14  tff(c_6704, plain, (![A_572, B_573, A_6]: (k1_relset_1(A_572, B_573, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_572, B_573)))), inference(resolution, [status(thm)], [c_18, c_6690])).
% 8.96/3.14  tff(c_8363, plain, (![A_720, B_721]: (k1_relset_1(A_720, B_721, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_3', B_721) | ~r1_tarski('#skF_1', A_720))), inference(resolution, [status(thm)], [c_8360, c_6704])).
% 8.96/3.14  tff(c_8396, plain, (![A_722, B_723]: (k1_relset_1(A_722, B_723, '#skF_4')='#skF_1' | ~r1_tarski('#skF_3', B_723) | ~r1_tarski('#skF_1', A_722))), inference(demodulation, [status(thm), theory('equality')], [c_7186, c_8363])).
% 8.96/3.14  tff(c_8401, plain, (![A_724]: (k1_relset_1(A_724, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_724))), inference(resolution, [status(thm)], [c_6, c_8396])).
% 8.96/3.14  tff(c_8406, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_8401])).
% 8.96/3.14  tff(c_8356, plain, (![A_718, B_719]: (r1_tarski('#skF_4', k2_zfmisc_1(A_718, B_719)) | ~r1_tarski('#skF_3', B_719) | ~r1_tarski('#skF_1', A_718))), inference(demodulation, [status(thm), theory('equality')], [c_6518, c_7186, c_8345])).
% 8.96/3.14  tff(c_7043, plain, (![B_615, C_616, A_617]: (k1_xboole_0=B_615 | v1_funct_2(C_616, A_617, B_615) | k1_relset_1(A_617, B_615, C_616)!=A_617 | ~m1_subset_1(C_616, k1_zfmisc_1(k2_zfmisc_1(A_617, B_615))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.96/3.14  tff(c_8751, plain, (![B_742, A_743, A_744]: (k1_xboole_0=B_742 | v1_funct_2(A_743, A_744, B_742) | k1_relset_1(A_744, B_742, A_743)!=A_744 | ~r1_tarski(A_743, k2_zfmisc_1(A_744, B_742)))), inference(resolution, [status(thm)], [c_18, c_7043])).
% 8.96/3.14  tff(c_8892, plain, (![B_750, A_751]: (k1_xboole_0=B_750 | v1_funct_2('#skF_4', A_751, B_750) | k1_relset_1(A_751, B_750, '#skF_4')!=A_751 | ~r1_tarski('#skF_3', B_750) | ~r1_tarski('#skF_1', A_751))), inference(resolution, [status(thm)], [c_8356, c_8751])).
% 8.96/3.14  tff(c_8901, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_8892, c_151])).
% 8.96/3.14  tff(c_8906, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_8406, c_8901])).
% 8.96/3.14  tff(c_8908, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6820, c_8906])).
% 8.96/3.14  tff(c_8910, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_6522])).
% 8.96/3.14  tff(c_9270, plain, (![A_802, B_803, C_804]: (k2_relset_1(A_802, B_803, C_804)=k2_relat_1(C_804) | ~m1_subset_1(C_804, k1_zfmisc_1(k2_zfmisc_1(A_802, B_803))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.96/3.14  tff(c_9277, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_9270])).
% 8.96/3.14  tff(c_9286, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6491, c_8910, c_9277])).
% 8.96/3.14  tff(c_9312, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9286, c_74])).
% 8.96/3.14  tff(c_8909, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_6522])).
% 8.96/3.14  tff(c_9172, plain, (![A_792, B_793, C_794]: (k1_relset_1(A_792, B_793, C_794)=k1_relat_1(C_794) | ~m1_subset_1(C_794, k1_zfmisc_1(k2_zfmisc_1(A_792, B_793))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.96/3.14  tff(c_9179, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_9172])).
% 8.96/3.14  tff(c_9188, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8909, c_9179])).
% 8.96/3.14  tff(c_9293, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9286, c_9188])).
% 8.96/3.14  tff(c_52, plain, (![B_29, A_28, C_30]: (k1_xboole_0=B_29 | k1_relset_1(A_28, B_29, C_30)=A_28 | ~v1_funct_2(C_30, A_28, B_29) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.96/3.14  tff(c_9574, plain, (![B_826, A_827, C_828]: (B_826='#skF_3' | k1_relset_1(A_827, B_826, C_828)=A_827 | ~v1_funct_2(C_828, A_827, B_826) | ~m1_subset_1(C_828, k1_zfmisc_1(k2_zfmisc_1(A_827, B_826))))), inference(demodulation, [status(thm), theory('equality')], [c_9286, c_52])).
% 8.96/3.14  tff(c_9590, plain, ('#skF_2'='#skF_3' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_9574])).
% 8.96/3.14  tff(c_9596, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_9293, c_9590])).
% 8.96/3.14  tff(c_9597, plain, ('#skF_3'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_9312, c_9596])).
% 8.96/3.14  tff(c_9313, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_9286, c_8])).
% 8.96/3.14  tff(c_9612, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_9597, c_9313])).
% 8.96/3.14  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.96/3.14  tff(c_9311, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9286, c_9286, c_14])).
% 8.96/3.14  tff(c_9607, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9597, c_9597, c_9311])).
% 8.96/3.14  tff(c_103, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.96/3.14  tff(c_107, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_103])).
% 8.96/3.14  tff(c_122, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_107, c_113])).
% 8.96/3.14  tff(c_8985, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_122])).
% 8.96/3.14  tff(c_9773, plain, (~r1_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9607, c_8985])).
% 8.96/3.14  tff(c_9778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9612, c_9773])).
% 8.96/3.14  tff(c_9779, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_4'), inference(splitRight, [status(thm)], [c_122])).
% 8.96/3.14  tff(c_9782, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9779, c_60])).
% 8.96/3.14  tff(c_9987, plain, (![A_864, B_865, C_866]: (k2_relset_1(A_864, B_865, C_866)=k2_relat_1(C_866) | ~m1_subset_1(C_866, k1_zfmisc_1(k2_zfmisc_1(A_864, B_865))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.96/3.14  tff(c_10127, plain, (![C_882]: (k2_relset_1('#skF_1', '#skF_2', C_882)=k2_relat_1(C_882) | ~m1_subset_1(C_882, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_9779, c_9987])).
% 8.96/3.14  tff(c_10130, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_9782, c_10127])).
% 8.96/3.14  tff(c_10136, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6491, c_8910, c_10130])).
% 8.96/3.14  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.96/3.14  tff(c_97, plain, (![A_35, B_36]: (v1_relat_1(k2_zfmisc_1(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.96/3.14  tff(c_99, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_97])).
% 8.96/3.14  tff(c_142, plain, (![A_44]: (k1_relat_1(A_44)=k1_xboole_0 | k2_relat_1(A_44)!=k1_xboole_0 | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.96/3.14  tff(c_149, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_99, c_142])).
% 8.96/3.14  tff(c_152, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_149])).
% 8.96/3.14  tff(c_201, plain, (![A_51]: (k2_relat_1(A_51)=k1_xboole_0 | k1_relat_1(A_51)!=k1_xboole_0 | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.96/3.14  tff(c_207, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_99, c_201])).
% 8.96/3.14  tff(c_216, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_152, c_207])).
% 8.96/3.14  tff(c_42, plain, (![A_28]: (v1_funct_2(k1_xboole_0, A_28, k1_xboole_0) | k1_xboole_0=A_28 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_28, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.96/3.14  tff(c_70, plain, (![A_28]: (v1_funct_2(k1_xboole_0, A_28, k1_xboole_0) | k1_xboole_0=A_28 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_42])).
% 8.96/3.14  tff(c_338, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_70])).
% 8.96/3.14  tff(c_341, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_338])).
% 8.96/3.14  tff(c_345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_341])).
% 8.96/3.14  tff(c_347, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_70])).
% 8.96/3.14  tff(c_311, plain, (![C_73, A_74, B_75]: (v4_relat_1(C_73, A_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.96/3.14  tff(c_321, plain, (![C_73, A_4]: (v4_relat_1(C_73, A_4) | ~m1_subset_1(C_73, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_311])).
% 8.96/3.14  tff(c_366, plain, (![A_80]: (v4_relat_1(k1_xboole_0, A_80))), inference(resolution, [status(thm)], [c_347, c_321])).
% 8.96/3.14  tff(c_277, plain, (![B_67, A_68]: (r1_tarski(k1_relat_1(B_67), A_68) | ~v4_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.96/3.14  tff(c_128, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_113])).
% 8.96/3.14  tff(c_297, plain, (![B_67]: (k1_relat_1(B_67)=k1_xboole_0 | ~v4_relat_1(B_67, k1_xboole_0) | ~v1_relat_1(B_67))), inference(resolution, [status(thm)], [c_277, c_128])).
% 8.96/3.14  tff(c_370, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_366, c_297])).
% 8.96/3.14  tff(c_373, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_99, c_370])).
% 8.96/3.14  tff(c_375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_216, c_373])).
% 8.96/3.14  tff(c_376, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_149])).
% 8.96/3.14  tff(c_10158, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10136, c_10136, c_376])).
% 8.96/3.14  tff(c_10165, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_10136, c_8])).
% 8.96/3.14  tff(c_10189, plain, (![A_883, B_884, C_885]: (k1_relset_1(A_883, B_884, C_885)=k1_relat_1(C_885) | ~m1_subset_1(C_885, k1_zfmisc_1(k2_zfmisc_1(A_883, B_884))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.96/3.14  tff(c_10204, plain, (![C_888]: (k1_relset_1('#skF_1', '#skF_2', C_888)=k1_relat_1(C_888) | ~m1_subset_1(C_888, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_9779, c_10189])).
% 8.96/3.14  tff(c_10402, plain, (![A_903]: (k1_relset_1('#skF_1', '#skF_2', A_903)=k1_relat_1(A_903) | ~r1_tarski(A_903, '#skF_4'))), inference(resolution, [status(thm)], [c_18, c_10204])).
% 8.96/3.14  tff(c_10406, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10165, c_10402])).
% 8.96/3.14  tff(c_10416, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10158, c_10406])).
% 8.96/3.14  tff(c_10161, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10136, c_99])).
% 8.96/3.14  tff(c_377, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_149])).
% 8.96/3.14  tff(c_10157, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10136, c_10136, c_377])).
% 8.96/3.14  tff(c_10442, plain, (![C_908, A_909, B_910]: (m1_subset_1(C_908, k1_zfmisc_1(k2_zfmisc_1(A_909, B_910))) | ~r1_tarski(k2_relat_1(C_908), B_910) | ~r1_tarski(k1_relat_1(C_908), A_909) | ~v1_relat_1(C_908))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.96/3.14  tff(c_10478, plain, (![C_911]: (m1_subset_1(C_911, k1_zfmisc_1('#skF_4')) | ~r1_tarski(k2_relat_1(C_911), '#skF_2') | ~r1_tarski(k1_relat_1(C_911), '#skF_1') | ~v1_relat_1(C_911))), inference(superposition, [status(thm), theory('equality')], [c_9779, c_10442])).
% 8.96/3.14  tff(c_10484, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_4')) | ~r1_tarski('#skF_3', '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10157, c_10478])).
% 8.96/3.14  tff(c_10488, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10161, c_10165, c_10158, c_10165, c_10484])).
% 8.96/3.14  tff(c_10164, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10136, c_74])).
% 8.96/3.14  tff(c_48, plain, (![B_29, C_30, A_28]: (k1_xboole_0=B_29 | v1_funct_2(C_30, A_28, B_29) | k1_relset_1(A_28, B_29, C_30)!=A_28 | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.96/3.14  tff(c_10560, plain, (![B_915, C_916, A_917]: (B_915='#skF_3' | v1_funct_2(C_916, A_917, B_915) | k1_relset_1(A_917, B_915, C_916)!=A_917 | ~m1_subset_1(C_916, k1_zfmisc_1(k2_zfmisc_1(A_917, B_915))))), inference(demodulation, [status(thm), theory('equality')], [c_10136, c_48])).
% 8.96/3.14  tff(c_10572, plain, (![C_916]: ('#skF_2'='#skF_3' | v1_funct_2(C_916, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_916)!='#skF_1' | ~m1_subset_1(C_916, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_9779, c_10560])).
% 8.96/3.14  tff(c_10642, plain, (![C_921]: (v1_funct_2(C_921, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_921)!='#skF_1' | ~m1_subset_1(C_921, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_10164, c_10572])).
% 8.96/3.14  tff(c_10645, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_10488, c_10642])).
% 8.96/3.14  tff(c_10654, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2') | '#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10416, c_10645])).
% 8.96/3.14  tff(c_10658, plain, ('#skF_3'!='#skF_1'), inference(splitLeft, [status(thm)], [c_10654])).
% 8.96/3.14  tff(c_10156, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10136, c_8909])).
% 8.96/3.14  tff(c_10207, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_9782, c_10204])).
% 8.96/3.14  tff(c_10213, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10156, c_10207])).
% 8.96/3.14  tff(c_10693, plain, (![B_925, A_926, C_927]: (B_925='#skF_3' | k1_relset_1(A_926, B_925, C_927)=A_926 | ~v1_funct_2(C_927, A_926, B_925) | ~m1_subset_1(C_927, k1_zfmisc_1(k2_zfmisc_1(A_926, B_925))))), inference(demodulation, [status(thm), theory('equality')], [c_10136, c_52])).
% 8.96/3.14  tff(c_10705, plain, (![C_927]: ('#skF_2'='#skF_3' | k1_relset_1('#skF_1', '#skF_2', C_927)='#skF_1' | ~v1_funct_2(C_927, '#skF_1', '#skF_2') | ~m1_subset_1(C_927, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_9779, c_10693])).
% 8.96/3.14  tff(c_10745, plain, (![C_932]: (k1_relset_1('#skF_1', '#skF_2', C_932)='#skF_1' | ~v1_funct_2(C_932, '#skF_1', '#skF_2') | ~m1_subset_1(C_932, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_10164, c_10705])).
% 8.96/3.14  tff(c_10751, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_9782, c_10745])).
% 8.96/3.14  tff(c_10761, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_10213, c_10751])).
% 8.96/3.14  tff(c_10763, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10658, c_10761])).
% 8.96/3.14  tff(c_10765, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_10654])).
% 8.96/3.14  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.96/3.14  tff(c_9790, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_9779, c_10])).
% 8.96/3.14  tff(c_9795, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_74, c_9790])).
% 8.96/3.14  tff(c_9809, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_9795])).
% 8.96/3.14  tff(c_10150, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10136, c_9809])).
% 8.96/3.14  tff(c_10795, plain, ('#skF_1'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10765, c_10150])).
% 8.96/3.14  tff(c_10163, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10136, c_10136, c_14])).
% 8.96/3.14  tff(c_11001, plain, (![B_942]: (k2_zfmisc_1('#skF_1', B_942)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10765, c_10765, c_10163])).
% 8.96/3.14  tff(c_11035, plain, ('#skF_1'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_11001, c_9779])).
% 8.96/3.14  tff(c_11053, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10795, c_11035])).
% 8.96/3.14  tff(c_11055, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_9795])).
% 8.96/3.14  tff(c_11054, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_9795])).
% 8.96/3.14  tff(c_11075, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11055, c_11054])).
% 8.96/3.14  tff(c_11063, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11054, c_11054, c_376])).
% 8.96/3.14  tff(c_11115, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11075, c_11075, c_11063])).
% 8.96/3.14  tff(c_11067, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11054, c_11054, c_12])).
% 8.96/3.14  tff(c_11164, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11075, c_11075, c_11067])).
% 8.96/3.14  tff(c_11294, plain, (![A_968, B_969, C_970]: (k1_relset_1(A_968, B_969, C_970)=k1_relat_1(C_970) | ~m1_subset_1(C_970, k1_zfmisc_1(k2_zfmisc_1(A_968, B_969))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.96/3.14  tff(c_11595, plain, (![A_1009, C_1010]: (k1_relset_1(A_1009, '#skF_4', C_1010)=k1_relat_1(C_1010) | ~m1_subset_1(C_1010, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_11164, c_11294])).
% 8.96/3.14  tff(c_11597, plain, (![A_1009]: (k1_relset_1(A_1009, '#skF_4', '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_9782, c_11595])).
% 8.96/3.14  tff(c_11602, plain, (![A_1009]: (k1_relset_1(A_1009, '#skF_4', '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11115, c_11597])).
% 8.96/3.14  tff(c_11062, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11054, c_11054, c_377])).
% 8.96/3.14  tff(c_11110, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11075, c_11075, c_11062])).
% 8.96/3.14  tff(c_11068, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11054, c_11054, c_14])).
% 8.96/3.14  tff(c_11146, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11075, c_11075, c_11068])).
% 8.96/3.14  tff(c_11333, plain, (![A_977, B_978, C_979]: (k2_relset_1(A_977, B_978, C_979)=k2_relat_1(C_979) | ~m1_subset_1(C_979, k1_zfmisc_1(k2_zfmisc_1(A_977, B_978))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.96/3.14  tff(c_11721, plain, (![B_1025, C_1026]: (k2_relset_1('#skF_4', B_1025, C_1026)=k2_relat_1(C_1026) | ~m1_subset_1(C_1026, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_11146, c_11333])).
% 8.96/3.14  tff(c_11723, plain, (![B_1025]: (k2_relset_1('#skF_4', B_1025, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_9782, c_11721])).
% 8.96/3.14  tff(c_11728, plain, (![B_1025]: (k2_relset_1('#skF_4', B_1025, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11110, c_11723])).
% 8.96/3.14  tff(c_11092, plain, (k2_relset_1('#skF_4', '#skF_2', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_11075, c_6491])).
% 8.96/3.14  tff(c_11730, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11728, c_11092])).
% 8.96/3.14  tff(c_46, plain, (![C_30, B_29]: (v1_funct_2(C_30, k1_xboole_0, B_29) | k1_relset_1(k1_xboole_0, B_29, C_30)!=k1_xboole_0 | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_29))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.96/3.14  tff(c_68, plain, (![C_30, B_29]: (v1_funct_2(C_30, k1_xboole_0, B_29) | k1_relset_1(k1_xboole_0, B_29, C_30)!=k1_xboole_0 | ~m1_subset_1(C_30, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_46])).
% 8.96/3.14  tff(c_11575, plain, (![C_1006, B_1007]: (v1_funct_2(C_1006, '#skF_4', B_1007) | k1_relset_1('#skF_4', B_1007, C_1006)!='#skF_4' | ~m1_subset_1(C_1006, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11055, c_11055, c_11055, c_11055, c_68])).
% 8.96/3.14  tff(c_11583, plain, (![B_1008]: (v1_funct_2('#skF_4', '#skF_4', B_1008) | k1_relset_1('#skF_4', B_1008, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_9782, c_11575])).
% 8.96/3.14  tff(c_11093, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11075, c_151])).
% 8.96/3.14  tff(c_11594, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_11583, c_11093])).
% 8.96/3.14  tff(c_11746, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11730, c_11594])).
% 8.96/3.14  tff(c_11750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11602, c_11746])).
% 8.96/3.14  tff(c_11751, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_66])).
% 8.96/3.14  tff(c_12471, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12453, c_11751])).
% 8.96/3.14  tff(c_12490, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12118, c_12377, c_12471])).
% 8.96/3.14  tff(c_12494, plain, (~v4_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_12490])).
% 8.96/3.14  tff(c_12498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12118, c_12196, c_12494])).
% 8.96/3.14  tff(c_12499, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_56])).
% 8.96/3.14  tff(c_12501, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_12499, c_8])).
% 8.96/3.14  tff(c_12513, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12499, c_12499, c_14])).
% 8.96/3.14  tff(c_12500, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_56])).
% 8.96/3.14  tff(c_12506, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12499, c_12500])).
% 8.96/3.14  tff(c_12544, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12513, c_12506, c_60])).
% 8.96/3.14  tff(c_12545, plain, (![A_1140, B_1141]: (r1_tarski(A_1140, B_1141) | ~m1_subset_1(A_1140, k1_zfmisc_1(B_1141)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.96/3.14  tff(c_12549, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_12544, c_12545])).
% 8.96/3.14  tff(c_13225, plain, (![B_1216, A_1217]: (B_1216=A_1217 | ~r1_tarski(B_1216, A_1217) | ~r1_tarski(A_1217, B_1216))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.96/3.14  tff(c_13227, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_12549, c_13225])).
% 8.96/3.14  tff(c_13236, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12501, c_13227])).
% 8.96/3.14  tff(c_13123, plain, (![B_1209, A_1210]: (B_1209=A_1210 | ~r1_tarski(B_1209, A_1210) | ~r1_tarski(A_1210, B_1209))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.96/3.14  tff(c_13125, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_12549, c_13123])).
% 8.96/3.14  tff(c_13134, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12501, c_13125])).
% 8.96/3.14  tff(c_13001, plain, (![B_1201, A_1202]: (B_1201=A_1202 | ~r1_tarski(B_1201, A_1202) | ~r1_tarski(A_1202, B_1201))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.96/3.14  tff(c_13003, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_12549, c_13001])).
% 8.96/3.14  tff(c_13012, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12501, c_13003])).
% 8.96/3.14  tff(c_12623, plain, (![B_1150, A_1151]: (B_1150=A_1151 | ~r1_tarski(B_1150, A_1151) | ~r1_tarski(A_1151, B_1150))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.96/3.14  tff(c_12625, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_12549, c_12623])).
% 8.96/3.14  tff(c_12634, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12501, c_12625])).
% 8.96/3.14  tff(c_12521, plain, (![A_1137, B_1138]: (v1_relat_1(k2_zfmisc_1(A_1137, B_1138)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.96/3.14  tff(c_12523, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12513, c_12521])).
% 8.96/3.14  tff(c_12565, plain, (![B_1145, A_1146]: (v1_relat_1(B_1145) | ~m1_subset_1(B_1145, k1_zfmisc_1(A_1146)) | ~v1_relat_1(A_1146))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.96/3.14  tff(c_12571, plain, (v1_relat_1('#skF_4') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_12544, c_12565])).
% 8.96/3.14  tff(c_12575, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12523, c_12571])).
% 8.96/3.14  tff(c_12555, plain, (![A_15]: (k1_relat_1(A_15)='#skF_1' | k2_relat_1(A_15)!='#skF_1' | ~v1_relat_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_12499, c_12499, c_28])).
% 8.96/3.14  tff(c_12579, plain, (k1_relat_1('#skF_4')='#skF_1' | k2_relat_1('#skF_4')!='#skF_1'), inference(resolution, [status(thm)], [c_12575, c_12555])).
% 8.96/3.14  tff(c_12583, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_12579])).
% 8.96/3.14  tff(c_30, plain, (![A_15]: (k2_relat_1(A_15)=k1_xboole_0 | k1_relat_1(A_15)!=k1_xboole_0 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.96/3.14  tff(c_12606, plain, (![A_1149]: (k2_relat_1(A_1149)='#skF_1' | k1_relat_1(A_1149)!='#skF_1' | ~v1_relat_1(A_1149))), inference(demodulation, [status(thm), theory('equality')], [c_12499, c_12499, c_30])).
% 8.96/3.14  tff(c_12609, plain, (k2_relat_1('#skF_4')='#skF_1' | k1_relat_1('#skF_4')!='#skF_1'), inference(resolution, [status(thm)], [c_12575, c_12606])).
% 8.96/3.14  tff(c_12618, plain, (k1_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_12583, c_12609])).
% 8.96/3.14  tff(c_12643, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12634, c_12618])).
% 8.96/3.14  tff(c_12654, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12634, c_12634, c_12513])).
% 8.96/3.14  tff(c_12832, plain, (![C_1173, A_1174, B_1175]: (v4_relat_1(C_1173, A_1174) | ~m1_subset_1(C_1173, k1_zfmisc_1(k2_zfmisc_1(A_1174, B_1175))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.96/3.14  tff(c_12858, plain, (![A_1184, A_1185, B_1186]: (v4_relat_1(A_1184, A_1185) | ~r1_tarski(A_1184, k2_zfmisc_1(A_1185, B_1186)))), inference(resolution, [status(thm)], [c_18, c_12832])).
% 8.96/3.14  tff(c_12880, plain, (![A_1185, B_1186]: (v4_relat_1(k2_zfmisc_1(A_1185, B_1186), A_1185))), inference(resolution, [status(thm)], [c_6, c_12858])).
% 8.96/3.14  tff(c_12804, plain, (![B_1167, A_1168]: (r1_tarski(k1_relat_1(B_1167), A_1168) | ~v4_relat_1(B_1167, A_1168) | ~v1_relat_1(B_1167))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.96/3.14  tff(c_12636, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(resolution, [status(thm)], [c_12501, c_12623])).
% 8.96/3.14  tff(c_12733, plain, (![A_3]: (A_3='#skF_4' | ~r1_tarski(A_3, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12634, c_12634, c_12636])).
% 8.96/3.14  tff(c_12934, plain, (![B_1197]: (k1_relat_1(B_1197)='#skF_4' | ~v4_relat_1(B_1197, '#skF_4') | ~v1_relat_1(B_1197))), inference(resolution, [status(thm)], [c_12804, c_12733])).
% 8.96/3.14  tff(c_12938, plain, (![B_1186]: (k1_relat_1(k2_zfmisc_1('#skF_4', B_1186))='#skF_4' | ~v1_relat_1(k2_zfmisc_1('#skF_4', B_1186)))), inference(resolution, [status(thm)], [c_12880, c_12934])).
% 8.96/3.14  tff(c_12949, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_12654, c_12938])).
% 8.96/3.14  tff(c_12951, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12643, c_12949])).
% 8.96/3.14  tff(c_12953, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_12579])).
% 8.96/3.14  tff(c_13021, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13012, c_12953])).
% 8.96/3.14  tff(c_12556, plain, (![A_1144]: (k1_relat_1(A_1144)='#skF_1' | k2_relat_1(A_1144)!='#skF_1' | ~v1_relat_1(A_1144))), inference(demodulation, [status(thm), theory('equality')], [c_12499, c_12499, c_28])).
% 8.96/3.14  tff(c_12563, plain, (k1_relat_1('#skF_1')='#skF_1' | k2_relat_1('#skF_1')!='#skF_1'), inference(resolution, [status(thm)], [c_12523, c_12556])).
% 8.96/3.14  tff(c_12580, plain, (k2_relat_1('#skF_1')!='#skF_1'), inference(splitLeft, [status(thm)], [c_12563])).
% 8.96/3.14  tff(c_13024, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13012, c_13012, c_12580])).
% 8.96/3.14  tff(c_13070, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13021, c_13024])).
% 8.96/3.14  tff(c_13072, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_12563])).
% 8.96/3.14  tff(c_13145, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13134, c_13134, c_13072])).
% 8.96/3.14  tff(c_13083, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_12579])).
% 8.96/3.14  tff(c_13144, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13134, c_13083])).
% 8.96/3.14  tff(c_13193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13145, c_13144])).
% 8.96/3.14  tff(c_13194, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_12579])).
% 8.96/3.14  tff(c_13244, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13236, c_13194])).
% 8.96/3.14  tff(c_13256, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_13236, c_12501])).
% 8.96/3.14  tff(c_13605, plain, (![A_1266, B_1267, C_1268]: (k1_relset_1(A_1266, B_1267, C_1268)=k1_relat_1(C_1268) | ~m1_subset_1(C_1268, k1_zfmisc_1(k2_zfmisc_1(A_1266, B_1267))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.96/3.14  tff(c_13918, plain, (![A_1307, B_1308, A_1309]: (k1_relset_1(A_1307, B_1308, A_1309)=k1_relat_1(A_1309) | ~r1_tarski(A_1309, k2_zfmisc_1(A_1307, B_1308)))), inference(resolution, [status(thm)], [c_18, c_13605])).
% 8.96/3.14  tff(c_13932, plain, (![A_1307, B_1308]: (k1_relset_1(A_1307, B_1308, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_13256, c_13918])).
% 8.96/3.14  tff(c_13939, plain, (![A_1307, B_1308]: (k1_relset_1(A_1307, B_1308, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13244, c_13932])).
% 8.96/3.14  tff(c_13250, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13236, c_12544])).
% 8.96/3.14  tff(c_13258, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13236, c_12499])).
% 8.96/3.14  tff(c_14112, plain, (![C_1333, B_1334]: (v1_funct_2(C_1333, '#skF_4', B_1334) | k1_relset_1('#skF_4', B_1334, C_1333)!='#skF_4' | ~m1_subset_1(C_1333, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_13258, c_13258, c_13258, c_13258, c_68])).
% 8.96/3.14  tff(c_14114, plain, (![B_1334]: (v1_funct_2('#skF_4', '#skF_4', B_1334) | k1_relset_1('#skF_4', B_1334, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_13250, c_14112])).
% 8.96/3.14  tff(c_14120, plain, (![B_1334]: (v1_funct_2('#skF_4', '#skF_4', B_1334))), inference(demodulation, [status(thm), theory('equality')], [c_13939, c_14114])).
% 8.96/3.14  tff(c_13078, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12544, c_12513, c_66])).
% 8.96/3.14  tff(c_13246, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13236, c_13078])).
% 8.96/3.14  tff(c_14125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14120, c_13246])).
% 8.96/3.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.96/3.14  
% 8.96/3.14  Inference rules
% 8.96/3.14  ----------------------
% 8.96/3.14  #Ref     : 0
% 8.96/3.14  #Sup     : 2941
% 8.96/3.14  #Fact    : 0
% 8.96/3.14  #Define  : 0
% 8.96/3.14  #Split   : 68
% 8.96/3.14  #Chain   : 0
% 8.96/3.14  #Close   : 0
% 8.96/3.14  
% 8.96/3.14  Ordering : KBO
% 8.96/3.14  
% 8.96/3.14  Simplification rules
% 8.96/3.14  ----------------------
% 8.96/3.14  #Subsume      : 501
% 8.96/3.14  #Demod        : 3395
% 8.96/3.14  #Tautology    : 1456
% 8.96/3.14  #SimpNegUnit  : 106
% 8.96/3.14  #BackRed      : 415
% 8.96/3.14  
% 8.96/3.14  #Partial instantiations: 0
% 8.96/3.14  #Strategies tried      : 1
% 8.96/3.14  
% 8.96/3.14  Timing (in seconds)
% 8.96/3.14  ----------------------
% 8.96/3.15  Preprocessing        : 0.34
% 8.96/3.15  Parsing              : 0.18
% 8.96/3.15  CNF conversion       : 0.02
% 8.96/3.15  Main loop            : 1.98
% 8.96/3.15  Inferencing          : 0.64
% 8.96/3.15  Reduction            : 0.71
% 8.96/3.15  Demodulation         : 0.50
% 8.96/3.15  BG Simplification    : 0.07
% 8.96/3.15  Subsumption          : 0.40
% 8.96/3.15  Abstraction          : 0.08
% 8.96/3.15  MUC search           : 0.00
% 8.96/3.15  Cooper               : 0.00
% 8.96/3.15  Total                : 2.42
% 8.96/3.15  Index Insertion      : 0.00
% 8.96/3.15  Index Deletion       : 0.00
% 8.96/3.15  Index Matching       : 0.00
% 8.96/3.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
