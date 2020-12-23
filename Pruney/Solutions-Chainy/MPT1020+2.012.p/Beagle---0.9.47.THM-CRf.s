%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:51 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 637 expanded)
%              Number of leaves         :   40 ( 227 expanded)
%              Depth                    :   15
%              Number of atoms          :  228 (1897 expanded)
%              Number of equality atoms :   43 ( 198 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_182,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_160,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( ( k2_relset_1(A,B,C) = B
              & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
              & v2_funct_1(C) )
           => ( A = k1_xboole_0
              | B = k1_xboole_0
              | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_328,plain,(
    ! [A_101,B_102,D_103] :
      ( r2_relset_1(A_101,B_102,D_103,D_103)
      | ~ m1_subset_1(D_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_334,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_328])).

tff(c_60,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_105,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_xboole_0(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_112,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_105])).

tff(c_114,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_66,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_64,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_56,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_77,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_84,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_77])).

tff(c_86,plain,(
    ! [C_50,B_51,A_52] :
      ( v5_relat_1(C_50,B_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_52,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_93,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_86])).

tff(c_124,plain,(
    ! [B_63,A_64] :
      ( k2_relat_1(B_63) = A_64
      | ~ v2_funct_2(B_63,A_64)
      | ~ v5_relat_1(B_63,A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_130,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_93,c_124])).

tff(c_136,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_130])).

tff(c_265,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_62,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_304,plain,(
    ! [C_98,B_99,A_100] :
      ( v2_funct_2(C_98,B_99)
      | ~ v3_funct_2(C_98,A_100,B_99)
      | ~ v1_funct_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_307,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_304])).

tff(c_313,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_307])).

tff(c_315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_265,c_313])).

tff(c_316,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_335,plain,(
    ! [A_104,B_105,C_106] :
      ( k2_relset_1(A_104,B_105,C_106) = k2_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_338,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_335])).

tff(c_343,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_338])).

tff(c_354,plain,(
    ! [C_107,A_108,B_109] :
      ( v2_funct_1(C_107)
      | ~ v3_funct_2(C_107,A_108,B_109)
      | ~ v1_funct_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_357,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_354])).

tff(c_363,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_357])).

tff(c_50,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_687,plain,(
    ! [C_135,D_136,B_137,A_138] :
      ( k2_funct_1(C_135) = D_136
      | k1_xboole_0 = B_137
      | k1_xboole_0 = A_138
      | ~ v2_funct_1(C_135)
      | ~ r2_relset_1(A_138,A_138,k1_partfun1(A_138,B_137,B_137,A_138,C_135,D_136),k6_partfun1(A_138))
      | k2_relset_1(A_138,B_137,C_135) != B_137
      | ~ m1_subset_1(D_136,k1_zfmisc_1(k2_zfmisc_1(B_137,A_138)))
      | ~ v1_funct_2(D_136,B_137,A_138)
      | ~ v1_funct_1(D_136)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137)))
      | ~ v1_funct_2(C_135,A_138,B_137)
      | ~ v1_funct_1(C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_690,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_687])).

tff(c_693,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_56,c_52,c_343,c_363,c_690])).

tff(c_694,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_693])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_697,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_694,c_2])).

tff(c_699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_697])).

tff(c_700,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_693])).

tff(c_409,plain,(
    ! [A_119,B_120] :
      ( k2_funct_2(A_119,B_120) = k2_funct_1(B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k2_zfmisc_1(A_119,A_119)))
      | ~ v3_funct_2(B_120,A_119,A_119)
      | ~ v1_funct_2(B_120,A_119,A_119)
      | ~ v1_funct_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_412,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_409])).

tff(c_418,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_412])).

tff(c_48,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_424,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_48])).

tff(c_712,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_700,c_424])).

tff(c_727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_712])).

tff(c_729,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_67,plain,(
    ! [B_44,A_45] :
      ( ~ v1_xboole_0(B_44)
      | B_44 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_70,plain,(
    ! [A_45] :
      ( k1_xboole_0 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_2,c_67])).

tff(c_742,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_729,c_70])).

tff(c_728,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_735,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_728,c_70])).

tff(c_751,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_735])).

tff(c_762,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_60])).

tff(c_884,plain,(
    ! [A_157,B_158,D_159] :
      ( r2_relset_1(A_157,B_158,D_159,D_159)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_887,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_762,c_884])).

tff(c_765,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_66])).

tff(c_764,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_64])).

tff(c_763,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_62])).

tff(c_943,plain,(
    ! [A_175,B_176] :
      ( k2_funct_2(A_175,B_176) = k2_funct_1(B_176)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(k2_zfmisc_1(A_175,A_175)))
      | ~ v3_funct_2(B_176,A_175,A_175)
      | ~ v1_funct_2(B_176,A_175,A_175)
      | ~ v1_funct_1(B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_946,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_762,c_943])).

tff(c_949,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_765,c_764,c_763,c_946])).

tff(c_968,plain,(
    ! [A_181,B_182] :
      ( m1_subset_1(k2_funct_2(A_181,B_182),k1_zfmisc_1(k2_zfmisc_1(A_181,A_181)))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(k2_zfmisc_1(A_181,A_181)))
      | ~ v3_funct_2(B_182,A_181,A_181)
      | ~ v1_funct_2(B_182,A_181,A_181)
      | ~ v1_funct_1(B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1007,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_949,c_968])).

tff(c_1022,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_765,c_764,c_763,c_762,c_1007])).

tff(c_14,plain,(
    ! [C_16,B_14,A_13] :
      ( v1_xboole_0(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(B_14,A_13)))
      | ~ v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1046,plain,
    ( v1_xboole_0(k2_funct_1('#skF_1'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1022,c_14])).

tff(c_1081,plain,(
    v1_xboole_0(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_729,c_1046])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_743,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_729,c_4])).

tff(c_1093,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1081,c_743])).

tff(c_771,plain,(
    ! [C_139,B_140,A_141] :
      ( v1_xboole_0(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(B_140,A_141)))
      | ~ v1_xboole_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_774,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_771])).

tff(c_777,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_729,c_774])).

tff(c_783,plain,(
    ! [A_142] :
      ( A_142 = '#skF_1'
      | ~ v1_xboole_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_729,c_4])).

tff(c_790,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_777,c_783])).

tff(c_761,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_48])).

tff(c_899,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_761])).

tff(c_951,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_949,c_899])).

tff(c_1108,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1093,c_951])).

tff(c_1119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_1108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.54  
% 3.24/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.54  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.24/1.54  
% 3.24/1.54  %Foreground sorts:
% 3.24/1.54  
% 3.24/1.54  
% 3.24/1.54  %Background operators:
% 3.24/1.54  
% 3.24/1.54  
% 3.24/1.54  %Foreground operators:
% 3.24/1.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.24/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.24/1.54  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.24/1.54  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.24/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.54  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.24/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.54  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 3.24/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.24/1.54  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.24/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.24/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.24/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.24/1.54  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 3.24/1.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.24/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.24/1.54  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.24/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.24/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.24/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.24/1.54  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 3.24/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.24/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.24/1.54  
% 3.24/1.56  tff(f_182, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_2)).
% 3.24/1.56  tff(f_70, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.24/1.56  tff(f_51, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 3.24/1.56  tff(f_38, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.24/1.56  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.24/1.56  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 3.24/1.56  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 3.24/1.56  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.24/1.56  tff(f_160, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 3.24/1.56  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.24/1.56  tff(f_116, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 3.24/1.56  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 3.24/1.56  tff(f_106, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 3.24/1.56  tff(f_58, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.24/1.56  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.24/1.56  tff(c_328, plain, (![A_101, B_102, D_103]: (r2_relset_1(A_101, B_102, D_103, D_103) | ~m1_subset_1(D_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.24/1.56  tff(c_334, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_328])).
% 3.24/1.56  tff(c_60, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.24/1.56  tff(c_105, plain, (![C_57, A_58, B_59]: (v1_xboole_0(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.24/1.56  tff(c_112, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_105])).
% 3.24/1.56  tff(c_114, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_112])).
% 3.24/1.56  tff(c_66, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.24/1.56  tff(c_64, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.24/1.56  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.24/1.56  tff(c_56, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.24/1.56  tff(c_77, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.24/1.56  tff(c_84, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_60, c_77])).
% 3.24/1.56  tff(c_86, plain, (![C_50, B_51, A_52]: (v5_relat_1(C_50, B_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_52, B_51))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.24/1.56  tff(c_93, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_86])).
% 3.24/1.56  tff(c_124, plain, (![B_63, A_64]: (k2_relat_1(B_63)=A_64 | ~v2_funct_2(B_63, A_64) | ~v5_relat_1(B_63, A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.24/1.56  tff(c_130, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_93, c_124])).
% 3.24/1.56  tff(c_136, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_130])).
% 3.24/1.56  tff(c_265, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_136])).
% 3.24/1.56  tff(c_62, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.24/1.56  tff(c_304, plain, (![C_98, B_99, A_100]: (v2_funct_2(C_98, B_99) | ~v3_funct_2(C_98, A_100, B_99) | ~v1_funct_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.24/1.56  tff(c_307, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_60, c_304])).
% 3.24/1.56  tff(c_313, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_307])).
% 3.24/1.56  tff(c_315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_265, c_313])).
% 3.24/1.56  tff(c_316, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_136])).
% 3.24/1.56  tff(c_335, plain, (![A_104, B_105, C_106]: (k2_relset_1(A_104, B_105, C_106)=k2_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.24/1.56  tff(c_338, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_60, c_335])).
% 3.24/1.56  tff(c_343, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_316, c_338])).
% 3.24/1.56  tff(c_354, plain, (![C_107, A_108, B_109]: (v2_funct_1(C_107) | ~v3_funct_2(C_107, A_108, B_109) | ~v1_funct_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.24/1.56  tff(c_357, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_60, c_354])).
% 3.24/1.56  tff(c_363, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_357])).
% 3.24/1.56  tff(c_50, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.24/1.56  tff(c_687, plain, (![C_135, D_136, B_137, A_138]: (k2_funct_1(C_135)=D_136 | k1_xboole_0=B_137 | k1_xboole_0=A_138 | ~v2_funct_1(C_135) | ~r2_relset_1(A_138, A_138, k1_partfun1(A_138, B_137, B_137, A_138, C_135, D_136), k6_partfun1(A_138)) | k2_relset_1(A_138, B_137, C_135)!=B_137 | ~m1_subset_1(D_136, k1_zfmisc_1(k2_zfmisc_1(B_137, A_138))) | ~v1_funct_2(D_136, B_137, A_138) | ~v1_funct_1(D_136) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))) | ~v1_funct_2(C_135, A_138, B_137) | ~v1_funct_1(C_135))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.24/1.56  tff(c_690, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_50, c_687])).
% 3.24/1.56  tff(c_693, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_56, c_52, c_343, c_363, c_690])).
% 3.24/1.56  tff(c_694, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_693])).
% 3.24/1.56  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.24/1.56  tff(c_697, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_694, c_2])).
% 3.24/1.56  tff(c_699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_697])).
% 3.24/1.56  tff(c_700, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_693])).
% 3.24/1.56  tff(c_409, plain, (![A_119, B_120]: (k2_funct_2(A_119, B_120)=k2_funct_1(B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(k2_zfmisc_1(A_119, A_119))) | ~v3_funct_2(B_120, A_119, A_119) | ~v1_funct_2(B_120, A_119, A_119) | ~v1_funct_1(B_120))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.24/1.56  tff(c_412, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_60, c_409])).
% 3.24/1.56  tff(c_418, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_412])).
% 3.24/1.56  tff(c_48, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 3.24/1.56  tff(c_424, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_48])).
% 3.24/1.56  tff(c_712, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_700, c_424])).
% 3.24/1.56  tff(c_727, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_334, c_712])).
% 3.24/1.56  tff(c_729, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_112])).
% 3.24/1.56  tff(c_67, plain, (![B_44, A_45]: (~v1_xboole_0(B_44) | B_44=A_45 | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.24/1.56  tff(c_70, plain, (![A_45]: (k1_xboole_0=A_45 | ~v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_2, c_67])).
% 3.24/1.56  tff(c_742, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_729, c_70])).
% 3.24/1.56  tff(c_728, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_112])).
% 3.24/1.56  tff(c_735, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_728, c_70])).
% 3.24/1.56  tff(c_751, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_742, c_735])).
% 3.24/1.56  tff(c_762, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_751, c_60])).
% 3.24/1.56  tff(c_884, plain, (![A_157, B_158, D_159]: (r2_relset_1(A_157, B_158, D_159, D_159) | ~m1_subset_1(D_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.24/1.56  tff(c_887, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_762, c_884])).
% 3.24/1.56  tff(c_765, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_751, c_66])).
% 3.24/1.56  tff(c_764, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_751, c_64])).
% 3.24/1.56  tff(c_763, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_751, c_62])).
% 3.24/1.56  tff(c_943, plain, (![A_175, B_176]: (k2_funct_2(A_175, B_176)=k2_funct_1(B_176) | ~m1_subset_1(B_176, k1_zfmisc_1(k2_zfmisc_1(A_175, A_175))) | ~v3_funct_2(B_176, A_175, A_175) | ~v1_funct_2(B_176, A_175, A_175) | ~v1_funct_1(B_176))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.24/1.56  tff(c_946, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_762, c_943])).
% 3.24/1.56  tff(c_949, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_765, c_764, c_763, c_946])).
% 3.24/1.56  tff(c_968, plain, (![A_181, B_182]: (m1_subset_1(k2_funct_2(A_181, B_182), k1_zfmisc_1(k2_zfmisc_1(A_181, A_181))) | ~m1_subset_1(B_182, k1_zfmisc_1(k2_zfmisc_1(A_181, A_181))) | ~v3_funct_2(B_182, A_181, A_181) | ~v1_funct_2(B_182, A_181, A_181) | ~v1_funct_1(B_182))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.24/1.56  tff(c_1007, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_949, c_968])).
% 3.24/1.56  tff(c_1022, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_765, c_764, c_763, c_762, c_1007])).
% 3.24/1.56  tff(c_14, plain, (![C_16, B_14, A_13]: (v1_xboole_0(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(B_14, A_13))) | ~v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.24/1.56  tff(c_1046, plain, (v1_xboole_0(k2_funct_1('#skF_1')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_1022, c_14])).
% 3.24/1.56  tff(c_1081, plain, (v1_xboole_0(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_729, c_1046])).
% 3.24/1.56  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.24/1.56  tff(c_743, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_729, c_4])).
% 3.24/1.56  tff(c_1093, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_1081, c_743])).
% 3.24/1.56  tff(c_771, plain, (![C_139, B_140, A_141]: (v1_xboole_0(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(B_140, A_141))) | ~v1_xboole_0(A_141))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.24/1.56  tff(c_774, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_771])).
% 3.24/1.56  tff(c_777, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_729, c_774])).
% 3.24/1.56  tff(c_783, plain, (![A_142]: (A_142='#skF_1' | ~v1_xboole_0(A_142))), inference(resolution, [status(thm)], [c_729, c_4])).
% 3.24/1.56  tff(c_790, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_777, c_783])).
% 3.24/1.56  tff(c_761, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_751, c_48])).
% 3.24/1.56  tff(c_899, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_790, c_761])).
% 3.24/1.56  tff(c_951, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_949, c_899])).
% 3.24/1.56  tff(c_1108, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1093, c_951])).
% 3.24/1.56  tff(c_1119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_887, c_1108])).
% 3.24/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.56  
% 3.24/1.56  Inference rules
% 3.24/1.56  ----------------------
% 3.24/1.56  #Ref     : 0
% 3.24/1.56  #Sup     : 212
% 3.24/1.56  #Fact    : 0
% 3.24/1.56  #Define  : 0
% 3.24/1.56  #Split   : 8
% 3.24/1.56  #Chain   : 0
% 3.24/1.56  #Close   : 0
% 3.24/1.56  
% 3.24/1.56  Ordering : KBO
% 3.24/1.56  
% 3.24/1.56  Simplification rules
% 3.24/1.56  ----------------------
% 3.24/1.56  #Subsume      : 10
% 3.24/1.56  #Demod        : 307
% 3.24/1.56  #Tautology    : 96
% 3.24/1.56  #SimpNegUnit  : 5
% 3.24/1.56  #BackRed      : 53
% 3.24/1.56  
% 3.24/1.56  #Partial instantiations: 0
% 3.24/1.56  #Strategies tried      : 1
% 3.24/1.56  
% 3.24/1.56  Timing (in seconds)
% 3.24/1.56  ----------------------
% 3.66/1.56  Preprocessing        : 0.35
% 3.66/1.56  Parsing              : 0.19
% 3.66/1.56  CNF conversion       : 0.02
% 3.66/1.56  Main loop            : 0.43
% 3.66/1.56  Inferencing          : 0.15
% 3.66/1.56  Reduction            : 0.15
% 3.66/1.56  Demodulation         : 0.10
% 3.66/1.56  BG Simplification    : 0.02
% 3.66/1.56  Subsumption          : 0.07
% 3.66/1.56  Abstraction          : 0.02
% 3.66/1.56  MUC search           : 0.00
% 3.66/1.56  Cooper               : 0.00
% 3.66/1.56  Total                : 0.82
% 3.66/1.56  Index Insertion      : 0.00
% 3.66/1.56  Index Deletion       : 0.00
% 3.66/1.56  Index Matching       : 0.00
% 3.66/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
