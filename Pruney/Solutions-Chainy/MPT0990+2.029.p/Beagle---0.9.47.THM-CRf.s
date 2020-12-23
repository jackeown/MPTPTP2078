%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:59 EST 2020

% Result     : Theorem 7.54s
% Output     : CNFRefutation 7.54s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 414 expanded)
%              Number of leaves         :   39 ( 170 expanded)
%              Depth                    :   12
%              Number of atoms          :  294 (1934 expanded)
%              Number of equality atoms :  101 ( 691 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_169,negated_conjecture,(
    ~ ! [A,B,C] :
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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_99,axiom,(
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

tff(f_143,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_125,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_115,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_111,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_127,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ! [D] :
              ( ( v1_relat_1(D)
                & v1_funct_1(D) )
             => ( ( k2_relat_1(B) = A
                  & k5_relat_1(B,C) = k6_relat_1(k1_relat_1(D))
                  & k5_relat_1(C,D) = k6_relat_1(A) )
               => D = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l72_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(c_48,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_89,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_101,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_89])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_100,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_89])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_133,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_144,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_133])).

tff(c_204,plain,(
    ! [B_71,A_72,C_73] :
      ( k1_xboole_0 = B_71
      | k1_relset_1(A_72,B_71,C_73) = A_72
      | ~ v1_funct_2(C_73,A_72,B_71)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_72,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_210,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_204])).

tff(c_218,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_144,c_210])).

tff(c_219,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_218])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_786,plain,(
    ! [B_180,C_181,A_182] :
      ( k6_partfun1(B_180) = k5_relat_1(k2_funct_1(C_181),C_181)
      | k1_xboole_0 = B_180
      | ~ v2_funct_1(C_181)
      | k2_relset_1(A_182,B_180,C_181) != B_180
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_182,B_180)))
      | ~ v1_funct_2(C_181,A_182,B_180)
      | ~ v1_funct_1(C_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_792,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_786])).

tff(c_800,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_54,c_792])).

tff(c_801,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_800])).

tff(c_330,plain,(
    ! [B_98,E_99,C_102,F_101,D_97,A_100] :
      ( k1_partfun1(A_100,B_98,C_102,D_97,E_99,F_101) = k5_relat_1(E_99,F_101)
      | ~ m1_subset_1(F_101,k1_zfmisc_1(k2_zfmisc_1(C_102,D_97)))
      | ~ v1_funct_1(F_101)
      | ~ m1_subset_1(E_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_98)))
      | ~ v1_funct_1(E_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_334,plain,(
    ! [A_100,B_98,E_99] :
      ( k1_partfun1(A_100,B_98,'#skF_2','#skF_1',E_99,'#skF_4') = k5_relat_1(E_99,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_98)))
      | ~ v1_funct_1(E_99) ) ),
    inference(resolution,[status(thm)],[c_60,c_330])).

tff(c_344,plain,(
    ! [A_103,B_104,E_105] :
      ( k1_partfun1(A_103,B_104,'#skF_2','#skF_1',E_105,'#skF_4') = k5_relat_1(E_105,'#skF_4')
      | ~ m1_subset_1(E_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ v1_funct_1(E_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_334])).

tff(c_353,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_344])).

tff(c_360,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_353])).

tff(c_38,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_243,plain,(
    ! [D_75,C_76,A_77,B_78] :
      ( D_75 = C_76
      | ~ r2_relset_1(A_77,B_78,C_76,D_75)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_251,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_243])).

tff(c_266,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_251])).

tff(c_276,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_266])).

tff(c_367,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_276])).

tff(c_473,plain,(
    ! [E_127,B_126,D_130,C_125,F_128,A_129] :
      ( m1_subset_1(k1_partfun1(A_129,B_126,C_125,D_130,E_127,F_128),k1_zfmisc_1(k2_zfmisc_1(A_129,D_130)))
      | ~ m1_subset_1(F_128,k1_zfmisc_1(k2_zfmisc_1(C_125,D_130)))
      | ~ v1_funct_1(F_128)
      | ~ m1_subset_1(E_127,k1_zfmisc_1(k2_zfmisc_1(A_129,B_126)))
      | ~ v1_funct_1(E_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_530,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_473])).

tff(c_556,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_530])).

tff(c_558,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_367,c_556])).

tff(c_559,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_266])).

tff(c_617,plain,(
    ! [D_144,F_148,E_146,C_149,B_145,A_147] :
      ( k1_partfun1(A_147,B_145,C_149,D_144,E_146,F_148) = k5_relat_1(E_146,F_148)
      | ~ m1_subset_1(F_148,k1_zfmisc_1(k2_zfmisc_1(C_149,D_144)))
      | ~ v1_funct_1(F_148)
      | ~ m1_subset_1(E_146,k1_zfmisc_1(k2_zfmisc_1(A_147,B_145)))
      | ~ v1_funct_1(E_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_621,plain,(
    ! [A_147,B_145,E_146] :
      ( k1_partfun1(A_147,B_145,'#skF_2','#skF_1',E_146,'#skF_4') = k5_relat_1(E_146,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_146,k1_zfmisc_1(k2_zfmisc_1(A_147,B_145)))
      | ~ v1_funct_1(E_146) ) ),
    inference(resolution,[status(thm)],[c_60,c_617])).

tff(c_632,plain,(
    ! [A_151,B_152,E_153] :
      ( k1_partfun1(A_151,B_152,'#skF_2','#skF_1',E_153,'#skF_4') = k5_relat_1(E_153,'#skF_4')
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152)))
      | ~ v1_funct_1(E_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_621])).

tff(c_641,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_632])).

tff(c_648,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_559,c_641])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_funct_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_relat_1(k2_funct_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_145,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_133])).

tff(c_213,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_204])).

tff(c_222,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_145,c_213])).

tff(c_223,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_222])).

tff(c_42,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6,plain,(
    ! [D_9,B_3,C_7] :
      ( D_9 = B_3
      | k6_relat_1(k2_relat_1(B_3)) != k5_relat_1(C_7,D_9)
      | k6_relat_1(k1_relat_1(D_9)) != k5_relat_1(B_3,C_7)
      | ~ v1_funct_1(D_9)
      | ~ v1_relat_1(D_9)
      | ~ v1_funct_1(C_7)
      | ~ v1_relat_1(C_7)
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_71,plain,(
    ! [D_9,B_3,C_7] :
      ( D_9 = B_3
      | k6_partfun1(k2_relat_1(B_3)) != k5_relat_1(C_7,D_9)
      | k6_partfun1(k1_relat_1(D_9)) != k5_relat_1(B_3,C_7)
      | ~ v1_funct_1(D_9)
      | ~ v1_relat_1(D_9)
      | ~ v1_funct_1(C_7)
      | ~ v1_relat_1(C_7)
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_6])).

tff(c_804,plain,(
    ! [B_3] :
      ( B_3 = '#skF_3'
      | k6_partfun1(k2_relat_1(B_3)) != k6_partfun1('#skF_2')
      | k5_relat_1(B_3,k2_funct_1('#skF_3')) != k6_partfun1(k1_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_801,c_71])).

tff(c_808,plain,(
    ! [B_3] :
      ( B_3 = '#skF_3'
      | k6_partfun1(k2_relat_1(B_3)) != k6_partfun1('#skF_2')
      | k5_relat_1(B_3,k2_funct_1('#skF_3')) != k6_partfun1('#skF_1')
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_70,c_223,c_804])).

tff(c_819,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_808])).

tff(c_822,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_819])).

tff(c_826,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_70,c_822])).

tff(c_827,plain,(
    ! [B_3] :
      ( ~ v1_funct_1(k2_funct_1('#skF_3'))
      | B_3 = '#skF_3'
      | k6_partfun1(k2_relat_1(B_3)) != k6_partfun1('#skF_2')
      | k5_relat_1(B_3,k2_funct_1('#skF_3')) != k6_partfun1('#skF_1')
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3) ) ),
    inference(splitRight,[status(thm)],[c_808])).

tff(c_3947,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_827])).

tff(c_3950,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_3947])).

tff(c_3954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_70,c_3950])).

tff(c_3956,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_827])).

tff(c_828,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_808])).

tff(c_8,plain,(
    ! [A_10] :
      ( k2_relat_1(k2_funct_1(A_10)) = k1_relat_1(A_10)
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_671,plain,(
    ! [D_155,B_156,C_157] :
      ( D_155 = B_156
      | k6_partfun1(k2_relat_1(B_156)) != k5_relat_1(C_157,D_155)
      | k6_partfun1(k1_relat_1(D_155)) != k5_relat_1(B_156,C_157)
      | ~ v1_funct_1(D_155)
      | ~ v1_relat_1(D_155)
      | ~ v1_funct_1(C_157)
      | ~ v1_relat_1(C_157)
      | ~ v1_funct_1(B_156)
      | ~ v1_relat_1(B_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_6])).

tff(c_1896,plain,(
    ! [A_218,D_219,C_220] :
      ( k2_funct_1(A_218) = D_219
      | k6_partfun1(k1_relat_1(A_218)) != k5_relat_1(C_220,D_219)
      | k6_partfun1(k1_relat_1(D_219)) != k5_relat_1(k2_funct_1(A_218),C_220)
      | ~ v1_funct_1(D_219)
      | ~ v1_relat_1(D_219)
      | ~ v1_funct_1(C_220)
      | ~ v1_relat_1(C_220)
      | ~ v1_funct_1(k2_funct_1(A_218))
      | ~ v1_relat_1(k2_funct_1(A_218))
      | ~ v2_funct_1(A_218)
      | ~ v1_funct_1(A_218)
      | ~ v1_relat_1(A_218) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_671])).

tff(c_1902,plain,(
    ! [D_219,C_220] :
      ( k2_funct_1('#skF_3') = D_219
      | k5_relat_1(C_220,D_219) != k6_partfun1('#skF_1')
      | k6_partfun1(k1_relat_1(D_219)) != k5_relat_1(k2_funct_1('#skF_3'),C_220)
      | ~ v1_funct_1(D_219)
      | ~ v1_relat_1(D_219)
      | ~ v1_funct_1(C_220)
      | ~ v1_relat_1(C_220)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_1896])).

tff(c_1912,plain,(
    ! [D_219,C_220] :
      ( k2_funct_1('#skF_3') = D_219
      | k5_relat_1(C_220,D_219) != k6_partfun1('#skF_1')
      | k6_partfun1(k1_relat_1(D_219)) != k5_relat_1(k2_funct_1('#skF_3'),C_220)
      | ~ v1_funct_1(D_219)
      | ~ v1_relat_1(D_219)
      | ~ v1_funct_1(C_220)
      | ~ v1_relat_1(C_220)
      | ~ v1_funct_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_70,c_54,c_828,c_1902])).

tff(c_5016,plain,(
    ! [D_313,C_314] :
      ( k2_funct_1('#skF_3') = D_313
      | k5_relat_1(C_314,D_313) != k6_partfun1('#skF_1')
      | k6_partfun1(k1_relat_1(D_313)) != k5_relat_1(k2_funct_1('#skF_3'),C_314)
      | ~ v1_funct_1(D_313)
      | ~ v1_relat_1(D_313)
      | ~ v1_funct_1(C_314)
      | ~ v1_relat_1(C_314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3956,c_1912])).

tff(c_5026,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_648,c_5016])).

tff(c_5035,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_70,c_100,c_64,c_219,c_801,c_5026])).

tff(c_5037,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_5035])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:36:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.54/2.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.54/2.70  
% 7.54/2.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.54/2.70  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.54/2.70  
% 7.54/2.70  %Foreground sorts:
% 7.54/2.70  
% 7.54/2.70  
% 7.54/2.70  %Background operators:
% 7.54/2.70  
% 7.54/2.70  
% 7.54/2.70  %Foreground operators:
% 7.54/2.70  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.54/2.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.54/2.70  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.54/2.70  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.54/2.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.54/2.70  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.54/2.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.54/2.70  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.54/2.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.54/2.70  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.54/2.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.54/2.70  tff('#skF_2', type, '#skF_2': $i).
% 7.54/2.70  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.54/2.70  tff('#skF_3', type, '#skF_3': $i).
% 7.54/2.70  tff('#skF_1', type, '#skF_1': $i).
% 7.54/2.70  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.54/2.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.54/2.70  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.54/2.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.54/2.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.54/2.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.54/2.70  tff('#skF_4', type, '#skF_4': $i).
% 7.54/2.70  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.54/2.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.54/2.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.54/2.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.54/2.70  
% 7.54/2.72  tff(f_169, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 7.54/2.72  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.54/2.72  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.54/2.72  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.54/2.72  tff(f_143, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 7.54/2.72  tff(f_125, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.54/2.72  tff(f_115, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.54/2.72  tff(f_81, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.54/2.72  tff(f_111, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.54/2.72  tff(f_33, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.54/2.72  tff(f_127, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.54/2.72  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (![D]: ((v1_relat_1(D) & v1_funct_1(D)) => ((((k2_relat_1(B) = A) & (k5_relat_1(B, C) = k6_relat_1(k1_relat_1(D)))) & (k5_relat_1(C, D) = k6_relat_1(A))) => (D = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l72_funct_1)).
% 7.54/2.72  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 7.54/2.72  tff(c_48, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.54/2.72  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.54/2.72  tff(c_89, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.54/2.72  tff(c_101, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_89])).
% 7.54/2.72  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.54/2.72  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.54/2.72  tff(c_100, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_89])).
% 7.54/2.72  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.54/2.72  tff(c_52, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.54/2.72  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.54/2.72  tff(c_133, plain, (![A_58, B_59, C_60]: (k1_relset_1(A_58, B_59, C_60)=k1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.54/2.72  tff(c_144, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_133])).
% 7.54/2.72  tff(c_204, plain, (![B_71, A_72, C_73]: (k1_xboole_0=B_71 | k1_relset_1(A_72, B_71, C_73)=A_72 | ~v1_funct_2(C_73, A_72, B_71) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_72, B_71))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.54/2.72  tff(c_210, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_204])).
% 7.54/2.72  tff(c_218, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_144, c_210])).
% 7.54/2.72  tff(c_219, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_52, c_218])).
% 7.54/2.72  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.54/2.72  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.54/2.72  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.54/2.72  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.54/2.72  tff(c_786, plain, (![B_180, C_181, A_182]: (k6_partfun1(B_180)=k5_relat_1(k2_funct_1(C_181), C_181) | k1_xboole_0=B_180 | ~v2_funct_1(C_181) | k2_relset_1(A_182, B_180, C_181)!=B_180 | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_182, B_180))) | ~v1_funct_2(C_181, A_182, B_180) | ~v1_funct_1(C_181))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.54/2.72  tff(c_792, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_786])).
% 7.54/2.72  tff(c_800, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_54, c_792])).
% 7.54/2.72  tff(c_801, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_800])).
% 7.54/2.72  tff(c_330, plain, (![B_98, E_99, C_102, F_101, D_97, A_100]: (k1_partfun1(A_100, B_98, C_102, D_97, E_99, F_101)=k5_relat_1(E_99, F_101) | ~m1_subset_1(F_101, k1_zfmisc_1(k2_zfmisc_1(C_102, D_97))) | ~v1_funct_1(F_101) | ~m1_subset_1(E_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_98))) | ~v1_funct_1(E_99))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.54/2.72  tff(c_334, plain, (![A_100, B_98, E_99]: (k1_partfun1(A_100, B_98, '#skF_2', '#skF_1', E_99, '#skF_4')=k5_relat_1(E_99, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_98))) | ~v1_funct_1(E_99))), inference(resolution, [status(thm)], [c_60, c_330])).
% 7.54/2.72  tff(c_344, plain, (![A_103, B_104, E_105]: (k1_partfun1(A_103, B_104, '#skF_2', '#skF_1', E_105, '#skF_4')=k5_relat_1(E_105, '#skF_4') | ~m1_subset_1(E_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~v1_funct_1(E_105))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_334])).
% 7.54/2.72  tff(c_353, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_344])).
% 7.54/2.72  tff(c_360, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_353])).
% 7.54/2.72  tff(c_38, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.54/2.72  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_169])).
% 7.54/2.72  tff(c_243, plain, (![D_75, C_76, A_77, B_78]: (D_75=C_76 | ~r2_relset_1(A_77, B_78, C_76, D_75) | ~m1_subset_1(D_75, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.54/2.72  tff(c_251, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_243])).
% 7.54/2.72  tff(c_266, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_251])).
% 7.54/2.72  tff(c_276, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_266])).
% 7.54/2.72  tff(c_367, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_360, c_276])).
% 7.54/2.72  tff(c_473, plain, (![E_127, B_126, D_130, C_125, F_128, A_129]: (m1_subset_1(k1_partfun1(A_129, B_126, C_125, D_130, E_127, F_128), k1_zfmisc_1(k2_zfmisc_1(A_129, D_130))) | ~m1_subset_1(F_128, k1_zfmisc_1(k2_zfmisc_1(C_125, D_130))) | ~v1_funct_1(F_128) | ~m1_subset_1(E_127, k1_zfmisc_1(k2_zfmisc_1(A_129, B_126))) | ~v1_funct_1(E_127))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.54/2.72  tff(c_530, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_360, c_473])).
% 7.54/2.72  tff(c_556, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_530])).
% 7.54/2.72  tff(c_558, plain, $false, inference(negUnitSimplification, [status(thm)], [c_367, c_556])).
% 7.54/2.72  tff(c_559, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_266])).
% 7.54/2.72  tff(c_617, plain, (![D_144, F_148, E_146, C_149, B_145, A_147]: (k1_partfun1(A_147, B_145, C_149, D_144, E_146, F_148)=k5_relat_1(E_146, F_148) | ~m1_subset_1(F_148, k1_zfmisc_1(k2_zfmisc_1(C_149, D_144))) | ~v1_funct_1(F_148) | ~m1_subset_1(E_146, k1_zfmisc_1(k2_zfmisc_1(A_147, B_145))) | ~v1_funct_1(E_146))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.54/2.72  tff(c_621, plain, (![A_147, B_145, E_146]: (k1_partfun1(A_147, B_145, '#skF_2', '#skF_1', E_146, '#skF_4')=k5_relat_1(E_146, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_146, k1_zfmisc_1(k2_zfmisc_1(A_147, B_145))) | ~v1_funct_1(E_146))), inference(resolution, [status(thm)], [c_60, c_617])).
% 7.54/2.72  tff(c_632, plain, (![A_151, B_152, E_153]: (k1_partfun1(A_151, B_152, '#skF_2', '#skF_1', E_153, '#skF_4')=k5_relat_1(E_153, '#skF_4') | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))) | ~v1_funct_1(E_153))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_621])).
% 7.54/2.72  tff(c_641, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_632])).
% 7.54/2.72  tff(c_648, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_559, c_641])).
% 7.54/2.72  tff(c_2, plain, (![A_1]: (v1_funct_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.54/2.72  tff(c_4, plain, (![A_1]: (v1_relat_1(k2_funct_1(A_1)) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.54/2.72  tff(c_145, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_133])).
% 7.54/2.72  tff(c_213, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_204])).
% 7.54/2.72  tff(c_222, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_145, c_213])).
% 7.54/2.72  tff(c_223, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_50, c_222])).
% 7.54/2.72  tff(c_42, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.54/2.72  tff(c_6, plain, (![D_9, B_3, C_7]: (D_9=B_3 | k6_relat_1(k2_relat_1(B_3))!=k5_relat_1(C_7, D_9) | k6_relat_1(k1_relat_1(D_9))!=k5_relat_1(B_3, C_7) | ~v1_funct_1(D_9) | ~v1_relat_1(D_9) | ~v1_funct_1(C_7) | ~v1_relat_1(C_7) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.54/2.72  tff(c_71, plain, (![D_9, B_3, C_7]: (D_9=B_3 | k6_partfun1(k2_relat_1(B_3))!=k5_relat_1(C_7, D_9) | k6_partfun1(k1_relat_1(D_9))!=k5_relat_1(B_3, C_7) | ~v1_funct_1(D_9) | ~v1_relat_1(D_9) | ~v1_funct_1(C_7) | ~v1_relat_1(C_7) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_6])).
% 7.54/2.72  tff(c_804, plain, (![B_3]: (B_3='#skF_3' | k6_partfun1(k2_relat_1(B_3))!=k6_partfun1('#skF_2') | k5_relat_1(B_3, k2_funct_1('#skF_3'))!=k6_partfun1(k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3))), inference(superposition, [status(thm), theory('equality')], [c_801, c_71])).
% 7.54/2.72  tff(c_808, plain, (![B_3]: (B_3='#skF_3' | k6_partfun1(k2_relat_1(B_3))!=k6_partfun1('#skF_2') | k5_relat_1(B_3, k2_funct_1('#skF_3'))!=k6_partfun1('#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_70, c_223, c_804])).
% 7.54/2.72  tff(c_819, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_808])).
% 7.54/2.72  tff(c_822, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_819])).
% 7.54/2.72  tff(c_826, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_70, c_822])).
% 7.54/2.72  tff(c_827, plain, (![B_3]: (~v1_funct_1(k2_funct_1('#skF_3')) | B_3='#skF_3' | k6_partfun1(k2_relat_1(B_3))!=k6_partfun1('#skF_2') | k5_relat_1(B_3, k2_funct_1('#skF_3'))!=k6_partfun1('#skF_1') | ~v1_funct_1(B_3) | ~v1_relat_1(B_3))), inference(splitRight, [status(thm)], [c_808])).
% 7.54/2.72  tff(c_3947, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_827])).
% 7.54/2.72  tff(c_3950, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_3947])).
% 7.54/2.72  tff(c_3954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_70, c_3950])).
% 7.54/2.72  tff(c_3956, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_827])).
% 7.54/2.72  tff(c_828, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_808])).
% 7.54/2.72  tff(c_8, plain, (![A_10]: (k2_relat_1(k2_funct_1(A_10))=k1_relat_1(A_10) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.54/2.72  tff(c_671, plain, (![D_155, B_156, C_157]: (D_155=B_156 | k6_partfun1(k2_relat_1(B_156))!=k5_relat_1(C_157, D_155) | k6_partfun1(k1_relat_1(D_155))!=k5_relat_1(B_156, C_157) | ~v1_funct_1(D_155) | ~v1_relat_1(D_155) | ~v1_funct_1(C_157) | ~v1_relat_1(C_157) | ~v1_funct_1(B_156) | ~v1_relat_1(B_156))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_6])).
% 7.54/2.72  tff(c_1896, plain, (![A_218, D_219, C_220]: (k2_funct_1(A_218)=D_219 | k6_partfun1(k1_relat_1(A_218))!=k5_relat_1(C_220, D_219) | k6_partfun1(k1_relat_1(D_219))!=k5_relat_1(k2_funct_1(A_218), C_220) | ~v1_funct_1(D_219) | ~v1_relat_1(D_219) | ~v1_funct_1(C_220) | ~v1_relat_1(C_220) | ~v1_funct_1(k2_funct_1(A_218)) | ~v1_relat_1(k2_funct_1(A_218)) | ~v2_funct_1(A_218) | ~v1_funct_1(A_218) | ~v1_relat_1(A_218))), inference(superposition, [status(thm), theory('equality')], [c_8, c_671])).
% 7.54/2.72  tff(c_1902, plain, (![D_219, C_220]: (k2_funct_1('#skF_3')=D_219 | k5_relat_1(C_220, D_219)!=k6_partfun1('#skF_1') | k6_partfun1(k1_relat_1(D_219))!=k5_relat_1(k2_funct_1('#skF_3'), C_220) | ~v1_funct_1(D_219) | ~v1_relat_1(D_219) | ~v1_funct_1(C_220) | ~v1_relat_1(C_220) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_223, c_1896])).
% 7.54/2.72  tff(c_1912, plain, (![D_219, C_220]: (k2_funct_1('#skF_3')=D_219 | k5_relat_1(C_220, D_219)!=k6_partfun1('#skF_1') | k6_partfun1(k1_relat_1(D_219))!=k5_relat_1(k2_funct_1('#skF_3'), C_220) | ~v1_funct_1(D_219) | ~v1_relat_1(D_219) | ~v1_funct_1(C_220) | ~v1_relat_1(C_220) | ~v1_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_70, c_54, c_828, c_1902])).
% 7.54/2.72  tff(c_5016, plain, (![D_313, C_314]: (k2_funct_1('#skF_3')=D_313 | k5_relat_1(C_314, D_313)!=k6_partfun1('#skF_1') | k6_partfun1(k1_relat_1(D_313))!=k5_relat_1(k2_funct_1('#skF_3'), C_314) | ~v1_funct_1(D_313) | ~v1_relat_1(D_313) | ~v1_funct_1(C_314) | ~v1_relat_1(C_314))), inference(demodulation, [status(thm), theory('equality')], [c_3956, c_1912])).
% 7.54/2.72  tff(c_5026, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_648, c_5016])).
% 7.54/2.72  tff(c_5035, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_70, c_100, c_64, c_219, c_801, c_5026])).
% 7.54/2.72  tff(c_5037, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_5035])).
% 7.54/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.54/2.72  
% 7.54/2.72  Inference rules
% 7.54/2.72  ----------------------
% 7.54/2.72  #Ref     : 0
% 7.54/2.72  #Sup     : 995
% 7.54/2.72  #Fact    : 0
% 7.54/2.72  #Define  : 0
% 7.54/2.72  #Split   : 20
% 7.54/2.72  #Chain   : 0
% 7.54/2.72  #Close   : 0
% 7.54/2.72  
% 7.54/2.72  Ordering : KBO
% 7.54/2.72  
% 7.54/2.72  Simplification rules
% 7.54/2.72  ----------------------
% 7.54/2.72  #Subsume      : 48
% 7.54/2.72  #Demod        : 2012
% 7.54/2.72  #Tautology    : 199
% 7.54/2.72  #SimpNegUnit  : 213
% 7.54/2.72  #BackRed      : 20
% 7.54/2.72  
% 7.54/2.72  #Partial instantiations: 0
% 7.54/2.72  #Strategies tried      : 1
% 7.54/2.72  
% 7.54/2.72  Timing (in seconds)
% 7.54/2.72  ----------------------
% 7.54/2.73  Preprocessing        : 0.37
% 7.54/2.73  Parsing              : 0.20
% 7.54/2.73  CNF conversion       : 0.02
% 7.54/2.73  Main loop            : 1.55
% 7.54/2.73  Inferencing          : 0.47
% 7.54/2.73  Reduction            : 0.67
% 7.54/2.73  Demodulation         : 0.52
% 7.54/2.73  BG Simplification    : 0.05
% 7.54/2.73  Subsumption          : 0.27
% 7.54/2.73  Abstraction          : 0.07
% 7.54/2.73  MUC search           : 0.00
% 7.54/2.73  Cooper               : 0.00
% 7.54/2.73  Total                : 1.96
% 7.54/2.73  Index Insertion      : 0.00
% 7.54/2.73  Index Deletion       : 0.00
% 7.54/2.73  Index Matching       : 0.00
% 7.54/2.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
