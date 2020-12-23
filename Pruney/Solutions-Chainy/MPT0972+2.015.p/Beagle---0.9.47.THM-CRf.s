%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:36 EST 2020

% Result     : Theorem 5.43s
% Output     : CNFRefutation 5.43s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 512 expanded)
%              Number of leaves         :   35 ( 186 expanded)
%              Depth                    :   11
%              Number of atoms          :  176 (1447 expanded)
%              Number of equality atoms :   58 ( 263 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1897,plain,(
    ! [C_270,B_271,A_272] :
      ( v1_xboole_0(C_270)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(B_271,A_272)))
      | ~ v1_xboole_0(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1909,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_1897])).

tff(c_1911,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1909])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1996,plain,(
    ! [A_282,B_283,D_284] :
      ( r2_relset_1(A_282,B_283,D_284,D_284)
      | ~ m1_subset_1(D_284,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2008,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_1996])).

tff(c_155,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_167,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_155])).

tff(c_58,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_56,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2157,plain,(
    ! [A_302,B_303,C_304] :
      ( k1_relset_1(A_302,B_303,C_304) = k1_relat_1(C_304)
      | ~ m1_subset_1(C_304,k1_zfmisc_1(k2_zfmisc_1(A_302,B_303))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2175,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_2157])).

tff(c_2530,plain,(
    ! [B_372,A_373,C_374] :
      ( k1_xboole_0 = B_372
      | k1_relset_1(A_373,B_372,C_374) = A_373
      | ~ v1_funct_2(C_374,A_373,B_372)
      | ~ m1_subset_1(C_374,k1_zfmisc_1(k2_zfmisc_1(A_373,B_372))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2543,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_2530])).

tff(c_2551,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2175,c_2543])).

tff(c_2555,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2551])).

tff(c_168,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_155])).

tff(c_64,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_62,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2176,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_2157])).

tff(c_2546,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_2530])).

tff(c_2554,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2176,c_2546])).

tff(c_2561,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2554])).

tff(c_2898,plain,(
    ! [A_411,B_412] :
      ( r2_hidden('#skF_3'(A_411,B_412),k1_relat_1(A_411))
      | B_412 = A_411
      | k1_relat_1(B_412) != k1_relat_1(A_411)
      | ~ v1_funct_1(B_412)
      | ~ v1_relat_1(B_412)
      | ~ v1_funct_1(A_411)
      | ~ v1_relat_1(A_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2906,plain,(
    ! [B_412] :
      ( r2_hidden('#skF_3'('#skF_6',B_412),'#skF_4')
      | B_412 = '#skF_6'
      | k1_relat_1(B_412) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_412)
      | ~ v1_relat_1(B_412)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2561,c_2898])).

tff(c_3351,plain,(
    ! [B_449] :
      ( r2_hidden('#skF_3'('#skF_6',B_449),'#skF_4')
      | B_449 = '#skF_6'
      | k1_relat_1(B_449) != '#skF_4'
      | ~ v1_funct_1(B_449)
      | ~ v1_relat_1(B_449) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_64,c_2561,c_2906])).

tff(c_52,plain,(
    ! [E_41] :
      ( k1_funct_1('#skF_7',E_41) = k1_funct_1('#skF_6',E_41)
      | ~ r2_hidden(E_41,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3558,plain,(
    ! [B_461] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_461)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_461))
      | B_461 = '#skF_6'
      | k1_relat_1(B_461) != '#skF_4'
      | ~ v1_funct_1(B_461)
      | ~ v1_relat_1(B_461) ) ),
    inference(resolution,[status(thm)],[c_3351,c_52])).

tff(c_24,plain,(
    ! [B_18,A_14] :
      ( k1_funct_1(B_18,'#skF_3'(A_14,B_18)) != k1_funct_1(A_14,'#skF_3'(A_14,B_18))
      | B_18 = A_14
      | k1_relat_1(B_18) != k1_relat_1(A_14)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3565,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3558,c_24])).

tff(c_3572,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_58,c_2555,c_168,c_64,c_2555,c_2561,c_3565])).

tff(c_50,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3599,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3572,c_50])).

tff(c_3610,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2008,c_3599])).

tff(c_3611,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2554])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3636,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3611,c_12])).

tff(c_3638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1911,c_3636])).

tff(c_3639,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2551])).

tff(c_3664,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3639,c_12])).

tff(c_3666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1911,c_3664])).

tff(c_3668,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1909])).

tff(c_1910,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_1897])).

tff(c_3730,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3668,c_1910])).

tff(c_101,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_2'(A_54,B_55),A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_111,plain,(
    ! [A_54,B_55] :
      ( ~ v1_xboole_0(A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_101,c_2])).

tff(c_112,plain,(
    ! [A_56,B_57] :
      ( ~ v1_xboole_0(A_56)
      | r1_tarski(A_56,B_57) ) ),
    inference(resolution,[status(thm)],[c_101,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_127,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(B_59,A_60)
      | ~ v1_xboole_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_112,c_14])).

tff(c_140,plain,(
    ! [B_55,A_54] :
      ( B_55 = A_54
      | ~ v1_xboole_0(B_55)
      | ~ v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_111,c_127])).

tff(c_3739,plain,(
    ! [A_465] :
      ( A_465 = '#skF_5'
      | ~ v1_xboole_0(A_465) ) ),
    inference(resolution,[status(thm)],[c_3668,c_140])).

tff(c_3746,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3730,c_3739])).

tff(c_145,plain,(
    ! [B_61,A_62] :
      ( B_61 = A_62
      | ~ v1_xboole_0(B_61)
      | ~ v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_111,c_127])).

tff(c_148,plain,(
    ! [A_62] :
      ( k1_xboole_0 = A_62
      | ~ v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_12,c_145])).

tff(c_3690,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3668,c_148])).

tff(c_3667,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1909])).

tff(c_3679,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3667,c_148])).

tff(c_3712,plain,(
    '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3690,c_3679])).

tff(c_3751,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3746,c_3712])).

tff(c_3692,plain,(
    ! [A_462,B_463,D_464] :
      ( r2_relset_1(A_462,B_463,D_464,D_464)
      | ~ m1_subset_1(D_464,k1_zfmisc_1(k2_zfmisc_1(A_462,B_463))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3701,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_3692])).

tff(c_3789,plain,(
    r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3751,c_3751,c_3746,c_3701])).

tff(c_3720,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3712,c_50])).

tff(c_3798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3789,c_3746,c_3746,c_3720])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:43:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.43/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/2.03  
% 5.43/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/2.03  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 5.43/2.03  
% 5.43/2.03  %Foreground sorts:
% 5.43/2.03  
% 5.43/2.03  
% 5.43/2.03  %Background operators:
% 5.43/2.03  
% 5.43/2.03  
% 5.43/2.03  %Foreground operators:
% 5.43/2.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.43/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.43/2.03  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.43/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.43/2.03  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.43/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.43/2.03  tff('#skF_7', type, '#skF_7': $i).
% 5.43/2.03  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.43/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.43/2.03  tff('#skF_5', type, '#skF_5': $i).
% 5.43/2.03  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.43/2.03  tff('#skF_6', type, '#skF_6': $i).
% 5.43/2.03  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.43/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.43/2.03  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.43/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.43/2.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.43/2.03  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.43/2.03  tff('#skF_4', type, '#skF_4': $i).
% 5.43/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.43/2.03  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.43/2.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.43/2.03  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.43/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.43/2.03  
% 5.43/2.05  tff(f_129, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 5.43/2.05  tff(f_78, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.43/2.05  tff(f_90, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.43/2.05  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.43/2.05  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.43/2.05  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.43/2.05  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 5.43/2.05  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.43/2.05  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.43/2.05  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.43/2.05  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.43/2.05  tff(c_54, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.43/2.05  tff(c_1897, plain, (![C_270, B_271, A_272]: (v1_xboole_0(C_270) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(B_271, A_272))) | ~v1_xboole_0(A_272))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.43/2.05  tff(c_1909, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_1897])).
% 5.43/2.05  tff(c_1911, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1909])).
% 5.43/2.05  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.43/2.05  tff(c_1996, plain, (![A_282, B_283, D_284]: (r2_relset_1(A_282, B_283, D_284, D_284) | ~m1_subset_1(D_284, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.43/2.05  tff(c_2008, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_1996])).
% 5.43/2.05  tff(c_155, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.43/2.05  tff(c_167, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_54, c_155])).
% 5.43/2.05  tff(c_58, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.43/2.05  tff(c_56, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.43/2.05  tff(c_2157, plain, (![A_302, B_303, C_304]: (k1_relset_1(A_302, B_303, C_304)=k1_relat_1(C_304) | ~m1_subset_1(C_304, k1_zfmisc_1(k2_zfmisc_1(A_302, B_303))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.43/2.05  tff(c_2175, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_54, c_2157])).
% 5.43/2.05  tff(c_2530, plain, (![B_372, A_373, C_374]: (k1_xboole_0=B_372 | k1_relset_1(A_373, B_372, C_374)=A_373 | ~v1_funct_2(C_374, A_373, B_372) | ~m1_subset_1(C_374, k1_zfmisc_1(k2_zfmisc_1(A_373, B_372))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.43/2.05  tff(c_2543, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_2530])).
% 5.43/2.05  tff(c_2551, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2175, c_2543])).
% 5.43/2.05  tff(c_2555, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_2551])).
% 5.43/2.05  tff(c_168, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_155])).
% 5.43/2.05  tff(c_64, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.43/2.05  tff(c_62, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.43/2.05  tff(c_2176, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_2157])).
% 5.43/2.05  tff(c_2546, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_2530])).
% 5.43/2.05  tff(c_2554, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2176, c_2546])).
% 5.43/2.05  tff(c_2561, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_2554])).
% 5.43/2.05  tff(c_2898, plain, (![A_411, B_412]: (r2_hidden('#skF_3'(A_411, B_412), k1_relat_1(A_411)) | B_412=A_411 | k1_relat_1(B_412)!=k1_relat_1(A_411) | ~v1_funct_1(B_412) | ~v1_relat_1(B_412) | ~v1_funct_1(A_411) | ~v1_relat_1(A_411))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.43/2.05  tff(c_2906, plain, (![B_412]: (r2_hidden('#skF_3'('#skF_6', B_412), '#skF_4') | B_412='#skF_6' | k1_relat_1(B_412)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_412) | ~v1_relat_1(B_412) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2561, c_2898])).
% 5.43/2.05  tff(c_3351, plain, (![B_449]: (r2_hidden('#skF_3'('#skF_6', B_449), '#skF_4') | B_449='#skF_6' | k1_relat_1(B_449)!='#skF_4' | ~v1_funct_1(B_449) | ~v1_relat_1(B_449))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_64, c_2561, c_2906])).
% 5.43/2.05  tff(c_52, plain, (![E_41]: (k1_funct_1('#skF_7', E_41)=k1_funct_1('#skF_6', E_41) | ~r2_hidden(E_41, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.43/2.05  tff(c_3558, plain, (![B_461]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_461))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_461)) | B_461='#skF_6' | k1_relat_1(B_461)!='#skF_4' | ~v1_funct_1(B_461) | ~v1_relat_1(B_461))), inference(resolution, [status(thm)], [c_3351, c_52])).
% 5.43/2.05  tff(c_24, plain, (![B_18, A_14]: (k1_funct_1(B_18, '#skF_3'(A_14, B_18))!=k1_funct_1(A_14, '#skF_3'(A_14, B_18)) | B_18=A_14 | k1_relat_1(B_18)!=k1_relat_1(A_14) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.43/2.05  tff(c_3565, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3558, c_24])).
% 5.43/2.05  tff(c_3572, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_167, c_58, c_2555, c_168, c_64, c_2555, c_2561, c_3565])).
% 5.43/2.05  tff(c_50, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.43/2.05  tff(c_3599, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3572, c_50])).
% 5.43/2.05  tff(c_3610, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2008, c_3599])).
% 5.43/2.05  tff(c_3611, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2554])).
% 5.43/2.05  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.43/2.05  tff(c_3636, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3611, c_12])).
% 5.43/2.05  tff(c_3638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1911, c_3636])).
% 5.43/2.05  tff(c_3639, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2551])).
% 5.43/2.05  tff(c_3664, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3639, c_12])).
% 5.43/2.05  tff(c_3666, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1911, c_3664])).
% 5.43/2.05  tff(c_3668, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_1909])).
% 5.43/2.05  tff(c_1910, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_60, c_1897])).
% 5.43/2.05  tff(c_3730, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3668, c_1910])).
% 5.43/2.05  tff(c_101, plain, (![A_54, B_55]: (r2_hidden('#skF_2'(A_54, B_55), A_54) | r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.43/2.05  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.43/2.05  tff(c_111, plain, (![A_54, B_55]: (~v1_xboole_0(A_54) | r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_101, c_2])).
% 5.43/2.05  tff(c_112, plain, (![A_56, B_57]: (~v1_xboole_0(A_56) | r1_tarski(A_56, B_57))), inference(resolution, [status(thm)], [c_101, c_2])).
% 5.43/2.05  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.43/2.05  tff(c_127, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(B_59, A_60) | ~v1_xboole_0(A_60))), inference(resolution, [status(thm)], [c_112, c_14])).
% 5.43/2.05  tff(c_140, plain, (![B_55, A_54]: (B_55=A_54 | ~v1_xboole_0(B_55) | ~v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_111, c_127])).
% 5.43/2.05  tff(c_3739, plain, (![A_465]: (A_465='#skF_5' | ~v1_xboole_0(A_465))), inference(resolution, [status(thm)], [c_3668, c_140])).
% 5.43/2.05  tff(c_3746, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_3730, c_3739])).
% 5.43/2.05  tff(c_145, plain, (![B_61, A_62]: (B_61=A_62 | ~v1_xboole_0(B_61) | ~v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_111, c_127])).
% 5.43/2.05  tff(c_148, plain, (![A_62]: (k1_xboole_0=A_62 | ~v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_12, c_145])).
% 5.43/2.05  tff(c_3690, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3668, c_148])).
% 5.43/2.05  tff(c_3667, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_1909])).
% 5.43/2.05  tff(c_3679, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_3667, c_148])).
% 5.43/2.05  tff(c_3712, plain, ('#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3690, c_3679])).
% 5.43/2.05  tff(c_3751, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3746, c_3712])).
% 5.43/2.05  tff(c_3692, plain, (![A_462, B_463, D_464]: (r2_relset_1(A_462, B_463, D_464, D_464) | ~m1_subset_1(D_464, k1_zfmisc_1(k2_zfmisc_1(A_462, B_463))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.43/2.05  tff(c_3701, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_3692])).
% 5.43/2.05  tff(c_3789, plain, (r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3751, c_3751, c_3746, c_3701])).
% 5.43/2.05  tff(c_3720, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3712, c_50])).
% 5.43/2.05  tff(c_3798, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3789, c_3746, c_3746, c_3720])).
% 5.43/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/2.05  
% 5.43/2.05  Inference rules
% 5.43/2.05  ----------------------
% 5.43/2.05  #Ref     : 2
% 5.43/2.05  #Sup     : 780
% 5.43/2.05  #Fact    : 0
% 5.43/2.05  #Define  : 0
% 5.43/2.05  #Split   : 20
% 5.43/2.05  #Chain   : 0
% 5.43/2.05  #Close   : 0
% 5.43/2.05  
% 5.43/2.05  Ordering : KBO
% 5.43/2.05  
% 5.43/2.05  Simplification rules
% 5.43/2.05  ----------------------
% 5.43/2.05  #Subsume      : 242
% 5.43/2.05  #Demod        : 688
% 5.43/2.05  #Tautology    : 338
% 5.43/2.05  #SimpNegUnit  : 27
% 5.43/2.05  #BackRed      : 166
% 5.43/2.05  
% 5.43/2.05  #Partial instantiations: 0
% 5.43/2.05  #Strategies tried      : 1
% 5.43/2.05  
% 5.43/2.05  Timing (in seconds)
% 5.43/2.05  ----------------------
% 5.43/2.05  Preprocessing        : 0.33
% 5.43/2.05  Parsing              : 0.17
% 5.43/2.05  CNF conversion       : 0.02
% 5.43/2.05  Main loop            : 0.96
% 5.43/2.05  Inferencing          : 0.32
% 5.43/2.05  Reduction            : 0.30
% 5.43/2.05  Demodulation         : 0.20
% 5.43/2.05  BG Simplification    : 0.03
% 5.43/2.05  Subsumption          : 0.22
% 5.43/2.05  Abstraction          : 0.04
% 5.43/2.05  MUC search           : 0.00
% 5.43/2.05  Cooper               : 0.00
% 5.43/2.05  Total                : 1.33
% 5.43/2.05  Index Insertion      : 0.00
% 5.43/2.05  Index Deletion       : 0.00
% 5.43/2.05  Index Matching       : 0.00
% 5.43/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
