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
% DateTime   : Thu Dec  3 10:15:54 EST 2020

% Result     : Theorem 4.74s
% Output     : CNFRefutation 4.88s
% Verified   : 
% Statistics : Number of formulae       :  166 (2984 expanded)
%              Number of leaves         :   37 ( 982 expanded)
%              Depth                    :   17
%              Number of atoms          :  328 (9125 expanded)
%              Number of equality atoms :   76 (1740 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_167,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_145,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_65,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_73,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_65])).

tff(c_309,plain,(
    ! [A_85,B_86,D_87] :
      ( r2_relset_1(A_85,B_86,D_87,D_87)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_315,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_309])).

tff(c_91,plain,(
    ! [C_40,B_41,A_42] :
      ( v5_relat_1(C_40,B_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_42,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_99,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_91])).

tff(c_113,plain,(
    ! [B_47,A_48] :
      ( k2_relat_1(B_47) = A_48
      | ~ v2_funct_2(B_47,A_48)
      | ~ v5_relat_1(B_47,A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_116,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_99,c_113])).

tff(c_122,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_116])).

tff(c_126,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_50,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_228,plain,(
    ! [C_70,B_71,A_72] :
      ( v2_funct_2(C_70,B_71)
      | ~ v3_funct_2(C_70,A_72,B_71)
      | ~ v1_funct_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_72,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_234,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_228])).

tff(c_240,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_234])).

tff(c_242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_240])).

tff(c_243,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(A_1) != k1_xboole_0
      | k1_xboole_0 = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_89,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_73,c_2])).

tff(c_101,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_316,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_101])).

tff(c_62,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_60,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_56,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_52,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_72,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_65])).

tff(c_98,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_91])).

tff(c_119,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_113])).

tff(c_125,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_119])).

tff(c_245,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_58,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_295,plain,(
    ! [C_82,B_83,A_84] :
      ( v2_funct_2(C_82,B_83)
      | ~ v3_funct_2(C_82,A_84,B_83)
      | ~ v1_funct_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_298,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_295])).

tff(c_304,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_298])).

tff(c_306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_245,c_304])).

tff(c_307,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_338,plain,(
    ! [A_88,B_89,C_90] :
      ( k2_relset_1(A_88,B_89,C_90) = k2_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_341,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_338])).

tff(c_346,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_341])).

tff(c_357,plain,(
    ! [C_91,A_92,B_93] :
      ( v2_funct_1(C_91)
      | ~ v3_funct_2(C_91,A_92,B_93)
      | ~ v1_funct_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_360,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_357])).

tff(c_366,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_360])).

tff(c_46,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_692,plain,(
    ! [C_119,D_120,B_121,A_122] :
      ( k2_funct_1(C_119) = D_120
      | k1_xboole_0 = B_121
      | k1_xboole_0 = A_122
      | ~ v2_funct_1(C_119)
      | ~ r2_relset_1(A_122,A_122,k1_partfun1(A_122,B_121,B_121,A_122,C_119,D_120),k6_partfun1(A_122))
      | k2_relset_1(A_122,B_121,C_119) != B_121
      | ~ m1_subset_1(D_120,k1_zfmisc_1(k2_zfmisc_1(B_121,A_122)))
      | ~ v1_funct_2(D_120,B_121,A_122)
      | ~ v1_funct_1(D_120)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121)))
      | ~ v1_funct_2(C_119,A_122,B_121)
      | ~ v1_funct_1(C_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_695,plain,
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
    inference(resolution,[status(thm)],[c_46,c_692])).

tff(c_698,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_48,c_346,c_366,c_695])).

tff(c_699,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_698])).

tff(c_412,plain,(
    ! [A_103,B_104] :
      ( k2_funct_2(A_103,B_104) = k2_funct_1(B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(k2_zfmisc_1(A_103,A_103)))
      | ~ v3_funct_2(B_104,A_103,A_103)
      | ~ v1_funct_2(B_104,A_103,A_103)
      | ~ v1_funct_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_415,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_412])).

tff(c_421,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_415])).

tff(c_44,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_426,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_44])).

tff(c_711,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_426])).

tff(c_727,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_711])).

tff(c_728,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_729,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_738,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_728,c_729])).

tff(c_1343,plain,(
    ! [B_210,A_211] :
      ( k2_relat_1(B_210) = A_211
      | ~ v2_funct_2(B_210,A_211)
      | ~ v5_relat_1(B_210,A_211)
      | ~ v1_relat_1(B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1346,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_99,c_1343])).

tff(c_1349,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_738,c_1346])).

tff(c_1356,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1349])).

tff(c_1378,plain,(
    ! [C_221,B_222,A_223] :
      ( v2_funct_2(C_221,B_222)
      | ~ v3_funct_2(C_221,A_223,B_222)
      | ~ v1_funct_1(C_221)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_223,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1381,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1378])).

tff(c_1384,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_1381])).

tff(c_1386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1356,c_1384])).

tff(c_1387,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1349])).

tff(c_1402,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1387,c_48])).

tff(c_14,plain,(
    ! [A_11,B_12,D_14] :
      ( r2_relset_1(A_11,B_12,D_14,D_14)
      | ~ m1_subset_1(D_14,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1448,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_1402,c_14])).

tff(c_1405,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1387,c_54])).

tff(c_1404,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1387,c_52])).

tff(c_1403,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1387,c_50])).

tff(c_1511,plain,(
    ! [A_244,B_245] :
      ( k2_funct_2(A_244,B_245) = k2_funct_1(B_245)
      | ~ m1_subset_1(B_245,k1_zfmisc_1(k2_zfmisc_1(A_244,A_244)))
      | ~ v3_funct_2(B_245,A_244,A_244)
      | ~ v1_funct_2(B_245,A_244,A_244)
      | ~ v1_funct_1(B_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1514,plain,
    ( k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1402,c_1511])).

tff(c_1517,plain,(
    k2_funct_2('#skF_1','#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1405,c_1404,c_1403,c_1514])).

tff(c_1536,plain,(
    ! [A_250,B_251] :
      ( m1_subset_1(k2_funct_2(A_250,B_251),k1_zfmisc_1(k2_zfmisc_1(A_250,A_250)))
      | ~ m1_subset_1(B_251,k1_zfmisc_1(k2_zfmisc_1(A_250,A_250)))
      | ~ v3_funct_2(B_251,A_250,A_250)
      | ~ v1_funct_2(B_251,A_250,A_250)
      | ~ v1_funct_1(B_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1569,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1517,c_1536])).

tff(c_1582,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1405,c_1404,c_1403,c_1402,c_1569])).

tff(c_6,plain,(
    ! [C_4,A_2,B_3] :
      ( v1_relat_1(C_4)
      | ~ m1_subset_1(C_4,k1_zfmisc_1(k2_zfmisc_1(A_2,B_3))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1642,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1582,c_6])).

tff(c_733,plain,(
    ! [A_1] :
      ( k2_relat_1(A_1) != '#skF_3'
      | A_1 = '#skF_3'
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_728,c_728,c_2])).

tff(c_1394,plain,(
    ! [A_1] :
      ( k2_relat_1(A_1) != '#skF_1'
      | A_1 = '#skF_1'
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1387,c_1387,c_733])).

tff(c_1650,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != '#skF_1'
    | k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1642,c_1394])).

tff(c_1683,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1650])).

tff(c_1504,plain,(
    ! [A_242,B_243] :
      ( v1_funct_1(k2_funct_2(A_242,B_243))
      | ~ m1_subset_1(B_243,k1_zfmisc_1(k2_zfmisc_1(A_242,A_242)))
      | ~ v3_funct_2(B_243,A_242,A_242)
      | ~ v1_funct_2(B_243,A_242,A_242)
      | ~ v1_funct_1(B_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1507,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_1'))
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1402,c_1504])).

tff(c_1510,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1405,c_1404,c_1403,c_1507])).

tff(c_1518,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1517,c_1510])).

tff(c_1530,plain,(
    ! [A_248,B_249] :
      ( v3_funct_2(k2_funct_2(A_248,B_249),A_248,A_248)
      | ~ m1_subset_1(B_249,k1_zfmisc_1(k2_zfmisc_1(A_248,A_248)))
      | ~ v3_funct_2(B_249,A_248,A_248)
      | ~ v1_funct_2(B_249,A_248,A_248)
      | ~ v1_funct_1(B_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1532,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_1'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1402,c_1530])).

tff(c_1535,plain,(
    v3_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1405,c_1404,c_1403,c_1517,c_1532])).

tff(c_18,plain,(
    ! [C_17,B_16,A_15] :
      ( v2_funct_2(C_17,B_16)
      | ~ v3_funct_2(C_17,A_15,B_16)
      | ~ v1_funct_1(C_17)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1602,plain,
    ( v2_funct_2(k2_funct_1('#skF_1'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1582,c_18])).

tff(c_1634,plain,(
    v2_funct_2(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1518,c_1535,c_1602])).

tff(c_8,plain,(
    ! [C_7,B_6,A_5] :
      ( v5_relat_1(C_7,B_6)
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1641,plain,(
    v5_relat_1(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1582,c_8])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( k2_relat_1(B_19) = A_18
      | ~ v2_funct_2(B_19,A_18)
      | ~ v5_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1654,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_1'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1641,c_26])).

tff(c_1657,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1642,c_1654])).

tff(c_1699,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1634,c_1657])).

tff(c_1700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1683,c_1699])).

tff(c_1701,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1650])).

tff(c_970,plain,(
    ! [B_158,A_159] :
      ( k2_relat_1(B_158) = A_159
      | ~ v2_funct_2(B_158,A_159)
      | ~ v5_relat_1(B_158,A_159)
      | ~ v1_relat_1(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_976,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_99,c_970])).

tff(c_985,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_738,c_976])).

tff(c_989,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_985])).

tff(c_1079,plain,(
    ! [C_175,B_176,A_177] :
      ( v2_funct_2(C_175,B_176)
      | ~ v3_funct_2(C_175,A_177,B_176)
      | ~ v1_funct_1(C_175)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_177,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1085,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1079])).

tff(c_1091,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_1085])).

tff(c_1093,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_989,c_1091])).

tff(c_1094,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_985])).

tff(c_81,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_72,c_2])).

tff(c_743,plain,
    ( k2_relat_1('#skF_2') != '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_728,c_728,c_81])).

tff(c_744,plain,(
    k2_relat_1('#skF_2') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_743])).

tff(c_1102,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1094,c_744])).

tff(c_1187,plain,(
    ! [C_184,B_185,A_186] :
      ( v2_funct_2(C_184,B_185)
      | ~ v3_funct_2(C_184,A_186,B_185)
      | ~ v1_funct_1(C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_186,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1193,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1187])).

tff(c_1199,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_1193])).

tff(c_979,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_970])).

tff(c_988,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_979])).

tff(c_1205,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_988])).

tff(c_1206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1102,c_1205])).

tff(c_1207,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_743])).

tff(c_1212,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1207,c_44])).

tff(c_1392,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1387,c_1387,c_1212])).

tff(c_1519,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1517,c_1392])).

tff(c_1721,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1701,c_1519])).

tff(c_1739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1448,c_1721])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:54:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.74/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/1.84  
% 4.88/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/1.84  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.88/1.84  
% 4.88/1.84  %Foreground sorts:
% 4.88/1.84  
% 4.88/1.84  
% 4.88/1.84  %Background operators:
% 4.88/1.84  
% 4.88/1.84  
% 4.88/1.84  %Foreground operators:
% 4.88/1.84  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.88/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.88/1.84  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.88/1.84  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.88/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.88/1.84  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.88/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.88/1.84  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 4.88/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.88/1.84  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.88/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.88/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.88/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.88/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.88/1.84  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.88/1.84  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.88/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.88/1.84  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.88/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.88/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.88/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.88/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.88/1.84  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.88/1.84  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 4.88/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.88/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.88/1.84  
% 4.88/1.87  tff(f_167, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 4.88/1.87  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.88/1.87  tff(f_55, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.88/1.87  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.88/1.87  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.88/1.87  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 4.88/1.87  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.88/1.87  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.88/1.87  tff(f_145, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.88/1.87  tff(f_101, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 4.88/1.87  tff(f_91, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 4.88/1.87  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.88/1.87  tff(c_65, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.88/1.87  tff(c_73, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_65])).
% 4.88/1.87  tff(c_309, plain, (![A_85, B_86, D_87]: (r2_relset_1(A_85, B_86, D_87, D_87) | ~m1_subset_1(D_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.88/1.87  tff(c_315, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_309])).
% 4.88/1.87  tff(c_91, plain, (![C_40, B_41, A_42]: (v5_relat_1(C_40, B_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_42, B_41))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.88/1.87  tff(c_99, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_91])).
% 4.88/1.87  tff(c_113, plain, (![B_47, A_48]: (k2_relat_1(B_47)=A_48 | ~v2_funct_2(B_47, A_48) | ~v5_relat_1(B_47, A_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.88/1.87  tff(c_116, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_99, c_113])).
% 4.88/1.87  tff(c_122, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_116])).
% 4.88/1.87  tff(c_126, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_122])).
% 4.88/1.87  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.88/1.87  tff(c_50, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.88/1.87  tff(c_228, plain, (![C_70, B_71, A_72]: (v2_funct_2(C_70, B_71) | ~v3_funct_2(C_70, A_72, B_71) | ~v1_funct_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_72, B_71))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.88/1.87  tff(c_234, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_228])).
% 4.88/1.87  tff(c_240, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_234])).
% 4.88/1.87  tff(c_242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_240])).
% 4.88/1.87  tff(c_243, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_122])).
% 4.88/1.87  tff(c_2, plain, (![A_1]: (k2_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.88/1.87  tff(c_89, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_73, c_2])).
% 4.88/1.87  tff(c_101, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_89])).
% 4.88/1.87  tff(c_316, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_243, c_101])).
% 4.88/1.87  tff(c_62, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.88/1.87  tff(c_60, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.88/1.87  tff(c_56, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.88/1.87  tff(c_52, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.88/1.87  tff(c_72, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_65])).
% 4.88/1.87  tff(c_98, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_91])).
% 4.88/1.87  tff(c_119, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_98, c_113])).
% 4.88/1.87  tff(c_125, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_119])).
% 4.88/1.87  tff(c_245, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_125])).
% 4.88/1.87  tff(c_58, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.88/1.87  tff(c_295, plain, (![C_82, B_83, A_84]: (v2_funct_2(C_82, B_83) | ~v3_funct_2(C_82, A_84, B_83) | ~v1_funct_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.88/1.87  tff(c_298, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_295])).
% 4.88/1.87  tff(c_304, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_298])).
% 4.88/1.87  tff(c_306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_245, c_304])).
% 4.88/1.87  tff(c_307, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_125])).
% 4.88/1.87  tff(c_338, plain, (![A_88, B_89, C_90]: (k2_relset_1(A_88, B_89, C_90)=k2_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.88/1.87  tff(c_341, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_338])).
% 4.88/1.87  tff(c_346, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_307, c_341])).
% 4.88/1.87  tff(c_357, plain, (![C_91, A_92, B_93]: (v2_funct_1(C_91) | ~v3_funct_2(C_91, A_92, B_93) | ~v1_funct_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.88/1.87  tff(c_360, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_357])).
% 4.88/1.87  tff(c_366, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_360])).
% 4.88/1.87  tff(c_46, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.88/1.87  tff(c_692, plain, (![C_119, D_120, B_121, A_122]: (k2_funct_1(C_119)=D_120 | k1_xboole_0=B_121 | k1_xboole_0=A_122 | ~v2_funct_1(C_119) | ~r2_relset_1(A_122, A_122, k1_partfun1(A_122, B_121, B_121, A_122, C_119, D_120), k6_partfun1(A_122)) | k2_relset_1(A_122, B_121, C_119)!=B_121 | ~m1_subset_1(D_120, k1_zfmisc_1(k2_zfmisc_1(B_121, A_122))) | ~v1_funct_2(D_120, B_121, A_122) | ~v1_funct_1(D_120) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))) | ~v1_funct_2(C_119, A_122, B_121) | ~v1_funct_1(C_119))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.88/1.87  tff(c_695, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_46, c_692])).
% 4.88/1.87  tff(c_698, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_48, c_346, c_366, c_695])).
% 4.88/1.87  tff(c_699, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_316, c_698])).
% 4.88/1.87  tff(c_412, plain, (![A_103, B_104]: (k2_funct_2(A_103, B_104)=k2_funct_1(B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(k2_zfmisc_1(A_103, A_103))) | ~v3_funct_2(B_104, A_103, A_103) | ~v1_funct_2(B_104, A_103, A_103) | ~v1_funct_1(B_104))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.88/1.87  tff(c_415, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_412])).
% 4.88/1.87  tff(c_421, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_415])).
% 4.88/1.87  tff(c_44, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.88/1.87  tff(c_426, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_421, c_44])).
% 4.88/1.87  tff(c_711, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_699, c_426])).
% 4.88/1.87  tff(c_727, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_315, c_711])).
% 4.88/1.87  tff(c_728, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_89])).
% 4.88/1.87  tff(c_729, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_89])).
% 4.88/1.87  tff(c_738, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_728, c_729])).
% 4.88/1.87  tff(c_1343, plain, (![B_210, A_211]: (k2_relat_1(B_210)=A_211 | ~v2_funct_2(B_210, A_211) | ~v5_relat_1(B_210, A_211) | ~v1_relat_1(B_210))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.88/1.87  tff(c_1346, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_99, c_1343])).
% 4.88/1.87  tff(c_1349, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_738, c_1346])).
% 4.88/1.87  tff(c_1356, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1349])).
% 4.88/1.87  tff(c_1378, plain, (![C_221, B_222, A_223]: (v2_funct_2(C_221, B_222) | ~v3_funct_2(C_221, A_223, B_222) | ~v1_funct_1(C_221) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_223, B_222))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.88/1.87  tff(c_1381, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1378])).
% 4.88/1.87  tff(c_1384, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_1381])).
% 4.88/1.87  tff(c_1386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1356, c_1384])).
% 4.88/1.87  tff(c_1387, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_1349])).
% 4.88/1.87  tff(c_1402, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1387, c_48])).
% 4.88/1.87  tff(c_14, plain, (![A_11, B_12, D_14]: (r2_relset_1(A_11, B_12, D_14, D_14) | ~m1_subset_1(D_14, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.88/1.87  tff(c_1448, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_1402, c_14])).
% 4.88/1.87  tff(c_1405, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1387, c_54])).
% 4.88/1.87  tff(c_1404, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1387, c_52])).
% 4.88/1.87  tff(c_1403, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1387, c_50])).
% 4.88/1.87  tff(c_1511, plain, (![A_244, B_245]: (k2_funct_2(A_244, B_245)=k2_funct_1(B_245) | ~m1_subset_1(B_245, k1_zfmisc_1(k2_zfmisc_1(A_244, A_244))) | ~v3_funct_2(B_245, A_244, A_244) | ~v1_funct_2(B_245, A_244, A_244) | ~v1_funct_1(B_245))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.88/1.87  tff(c_1514, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_1402, c_1511])).
% 4.88/1.87  tff(c_1517, plain, (k2_funct_2('#skF_1', '#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1405, c_1404, c_1403, c_1514])).
% 4.88/1.87  tff(c_1536, plain, (![A_250, B_251]: (m1_subset_1(k2_funct_2(A_250, B_251), k1_zfmisc_1(k2_zfmisc_1(A_250, A_250))) | ~m1_subset_1(B_251, k1_zfmisc_1(k2_zfmisc_1(A_250, A_250))) | ~v3_funct_2(B_251, A_250, A_250) | ~v1_funct_2(B_251, A_250, A_250) | ~v1_funct_1(B_251))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.88/1.87  tff(c_1569, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1517, c_1536])).
% 4.88/1.87  tff(c_1582, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1405, c_1404, c_1403, c_1402, c_1569])).
% 4.88/1.87  tff(c_6, plain, (![C_4, A_2, B_3]: (v1_relat_1(C_4) | ~m1_subset_1(C_4, k1_zfmisc_1(k2_zfmisc_1(A_2, B_3))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.88/1.87  tff(c_1642, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_1582, c_6])).
% 4.88/1.87  tff(c_733, plain, (![A_1]: (k2_relat_1(A_1)!='#skF_3' | A_1='#skF_3' | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_728, c_728, c_2])).
% 4.88/1.87  tff(c_1394, plain, (![A_1]: (k2_relat_1(A_1)!='#skF_1' | A_1='#skF_1' | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1387, c_1387, c_733])).
% 4.88/1.87  tff(c_1650, plain, (k2_relat_1(k2_funct_1('#skF_1'))!='#skF_1' | k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_1642, c_1394])).
% 4.88/1.87  tff(c_1683, plain, (k2_relat_1(k2_funct_1('#skF_1'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_1650])).
% 4.88/1.87  tff(c_1504, plain, (![A_242, B_243]: (v1_funct_1(k2_funct_2(A_242, B_243)) | ~m1_subset_1(B_243, k1_zfmisc_1(k2_zfmisc_1(A_242, A_242))) | ~v3_funct_2(B_243, A_242, A_242) | ~v1_funct_2(B_243, A_242, A_242) | ~v1_funct_1(B_243))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.88/1.87  tff(c_1507, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_1')) | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_1402, c_1504])).
% 4.88/1.87  tff(c_1510, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1405, c_1404, c_1403, c_1507])).
% 4.88/1.87  tff(c_1518, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1517, c_1510])).
% 4.88/1.87  tff(c_1530, plain, (![A_248, B_249]: (v3_funct_2(k2_funct_2(A_248, B_249), A_248, A_248) | ~m1_subset_1(B_249, k1_zfmisc_1(k2_zfmisc_1(A_248, A_248))) | ~v3_funct_2(B_249, A_248, A_248) | ~v1_funct_2(B_249, A_248, A_248) | ~v1_funct_1(B_249))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.88/1.87  tff(c_1532, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_1'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_1402, c_1530])).
% 4.88/1.87  tff(c_1535, plain, (v3_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1405, c_1404, c_1403, c_1517, c_1532])).
% 4.88/1.87  tff(c_18, plain, (![C_17, B_16, A_15]: (v2_funct_2(C_17, B_16) | ~v3_funct_2(C_17, A_15, B_16) | ~v1_funct_1(C_17) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.88/1.87  tff(c_1602, plain, (v2_funct_2(k2_funct_1('#skF_1'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_1582, c_18])).
% 4.88/1.87  tff(c_1634, plain, (v2_funct_2(k2_funct_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1518, c_1535, c_1602])).
% 4.88/1.87  tff(c_8, plain, (![C_7, B_6, A_5]: (v5_relat_1(C_7, B_6) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_5, B_6))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.88/1.87  tff(c_1641, plain, (v5_relat_1(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_1582, c_8])).
% 4.88/1.87  tff(c_26, plain, (![B_19, A_18]: (k2_relat_1(B_19)=A_18 | ~v2_funct_2(B_19, A_18) | ~v5_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.88/1.87  tff(c_1654, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_1'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_1641, c_26])).
% 4.88/1.87  tff(c_1657, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1642, c_1654])).
% 4.88/1.87  tff(c_1699, plain, (k2_relat_1(k2_funct_1('#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1634, c_1657])).
% 4.88/1.87  tff(c_1700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1683, c_1699])).
% 4.88/1.87  tff(c_1701, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_1650])).
% 4.88/1.87  tff(c_970, plain, (![B_158, A_159]: (k2_relat_1(B_158)=A_159 | ~v2_funct_2(B_158, A_159) | ~v5_relat_1(B_158, A_159) | ~v1_relat_1(B_158))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.88/1.87  tff(c_976, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_99, c_970])).
% 4.88/1.87  tff(c_985, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_738, c_976])).
% 4.88/1.87  tff(c_989, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_985])).
% 4.88/1.87  tff(c_1079, plain, (![C_175, B_176, A_177]: (v2_funct_2(C_175, B_176) | ~v3_funct_2(C_175, A_177, B_176) | ~v1_funct_1(C_175) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_177, B_176))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.88/1.87  tff(c_1085, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1079])).
% 4.88/1.87  tff(c_1091, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_1085])).
% 4.88/1.87  tff(c_1093, plain, $false, inference(negUnitSimplification, [status(thm)], [c_989, c_1091])).
% 4.88/1.87  tff(c_1094, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_985])).
% 4.88/1.87  tff(c_81, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_72, c_2])).
% 4.88/1.87  tff(c_743, plain, (k2_relat_1('#skF_2')!='#skF_3' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_728, c_728, c_81])).
% 4.88/1.87  tff(c_744, plain, (k2_relat_1('#skF_2')!='#skF_3'), inference(splitLeft, [status(thm)], [c_743])).
% 4.88/1.87  tff(c_1102, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1094, c_744])).
% 4.88/1.87  tff(c_1187, plain, (![C_184, B_185, A_186]: (v2_funct_2(C_184, B_185) | ~v3_funct_2(C_184, A_186, B_185) | ~v1_funct_1(C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_186, B_185))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.88/1.87  tff(c_1193, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_1187])).
% 4.88/1.87  tff(c_1199, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_1193])).
% 4.88/1.87  tff(c_979, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_98, c_970])).
% 4.88/1.87  tff(c_988, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_979])).
% 4.88/1.87  tff(c_1205, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_988])).
% 4.88/1.87  tff(c_1206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1102, c_1205])).
% 4.88/1.87  tff(c_1207, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_743])).
% 4.88/1.87  tff(c_1212, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1207, c_44])).
% 4.88/1.87  tff(c_1392, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1387, c_1387, c_1212])).
% 4.88/1.87  tff(c_1519, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1517, c_1392])).
% 4.88/1.87  tff(c_1721, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1701, c_1519])).
% 4.88/1.87  tff(c_1739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1448, c_1721])).
% 4.88/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.88/1.87  
% 4.88/1.87  Inference rules
% 4.88/1.87  ----------------------
% 4.88/1.87  #Ref     : 0
% 4.88/1.87  #Sup     : 331
% 4.88/1.87  #Fact    : 0
% 4.88/1.87  #Define  : 0
% 4.88/1.87  #Split   : 20
% 4.88/1.87  #Chain   : 0
% 4.88/1.87  #Close   : 0
% 4.88/1.87  
% 4.88/1.87  Ordering : KBO
% 4.88/1.87  
% 4.88/1.87  Simplification rules
% 4.88/1.87  ----------------------
% 4.88/1.87  #Subsume      : 7
% 4.88/1.87  #Demod        : 565
% 4.88/1.87  #Tautology    : 181
% 4.88/1.87  #SimpNegUnit  : 12
% 4.88/1.87  #BackRed      : 129
% 4.88/1.87  
% 4.88/1.87  #Partial instantiations: 0
% 4.88/1.87  #Strategies tried      : 1
% 4.88/1.87  
% 4.88/1.87  Timing (in seconds)
% 4.88/1.87  ----------------------
% 4.88/1.87  Preprocessing        : 0.37
% 4.88/1.87  Parsing              : 0.20
% 4.88/1.87  CNF conversion       : 0.02
% 4.88/1.87  Main loop            : 0.69
% 4.88/1.87  Inferencing          : 0.25
% 4.88/1.87  Reduction            : 0.23
% 4.88/1.87  Demodulation         : 0.16
% 4.88/1.87  BG Simplification    : 0.03
% 4.88/1.87  Subsumption          : 0.10
% 4.88/1.87  Abstraction          : 0.03
% 4.88/1.87  MUC search           : 0.00
% 4.88/1.87  Cooper               : 0.00
% 4.88/1.87  Total                : 1.13
% 4.88/1.87  Index Insertion      : 0.00
% 4.88/1.87  Index Deletion       : 0.00
% 4.88/1.87  Index Matching       : 0.00
% 4.88/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
