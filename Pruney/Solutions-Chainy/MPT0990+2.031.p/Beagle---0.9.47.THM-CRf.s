%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:00 EST 2020

% Result     : Theorem 5.72s
% Output     : CNFRefutation 5.85s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 253 expanded)
%              Number of leaves         :   41 ( 108 expanded)
%              Depth                    :   11
%              Number of atoms          :  208 ( 965 expanded)
%              Number of equality atoms :   77 ( 334 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_189,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_119,axiom,(
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

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_147,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_131,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_135,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_145,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_163,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_64,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_138,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_150,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_138])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_149,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_138])).

tff(c_86,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_14,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_70,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_84,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_212,plain,(
    ! [A_66,B_67,C_68] :
      ( k1_relset_1(A_66,B_67,C_68) = k1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_224,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_212])).

tff(c_471,plain,(
    ! [B_88,A_89,C_90] :
      ( k1_xboole_0 = B_88
      | k1_relset_1(A_89,B_88,C_90) = A_89
      | ~ v1_funct_2(C_90,A_89,B_88)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_477,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_471])).

tff(c_485,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_224,c_477])).

tff(c_486,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_485])).

tff(c_166,plain,(
    ! [A_59] :
      ( k2_relat_1(k2_funct_1(A_59)) = k1_relat_1(A_59)
      | ~ v2_funct_1(A_59)
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_58,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_10,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k6_relat_1(k2_relat_1(A_10))) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_87,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k6_partfun1(k2_relat_1(A_10))) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_10])).

tff(c_1072,plain,(
    ! [A_107] :
      ( k5_relat_1(k2_funct_1(A_107),k6_partfun1(k1_relat_1(A_107))) = k2_funct_1(A_107)
      | ~ v1_relat_1(k2_funct_1(A_107))
      | ~ v2_funct_1(A_107)
      | ~ v1_funct_1(A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_87])).

tff(c_1090,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_1072])).

tff(c_1112,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_86,c_70,c_1090])).

tff(c_1927,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1112])).

tff(c_1930,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_1927])).

tff(c_1934,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_86,c_1930])).

tff(c_1935,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1112])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_78,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_225,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_212])).

tff(c_480,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_471])).

tff(c_489,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_225,c_480])).

tff(c_490,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_489])).

tff(c_8,plain,(
    ! [A_9] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_9)),A_9) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_88,plain,(
    ! [A_9] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_9)),A_9) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_8])).

tff(c_505,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_490,c_88])).

tff(c_509,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_505])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_1857,plain,(
    ! [E_143,F_142,A_144,D_147,C_145,B_146] :
      ( m1_subset_1(k1_partfun1(A_144,B_146,C_145,D_147,E_143,F_142),k1_zfmisc_1(k2_zfmisc_1(A_144,D_147)))
      | ~ m1_subset_1(F_142,k1_zfmisc_1(k2_zfmisc_1(C_145,D_147)))
      | ~ v1_funct_1(F_142)
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(A_144,B_146)))
      | ~ v1_funct_1(E_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_54,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_72,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_905,plain,(
    ! [D_101,C_102,A_103,B_104] :
      ( D_101 = C_102
      | ~ r2_relset_1(A_103,B_104,C_102,D_101)
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104)))
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_913,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_72,c_905])).

tff(c_928,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_913])).

tff(c_1115,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_928])).

tff(c_1872,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1857,c_1115])).

tff(c_1918,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_1872])).

tff(c_1919,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_928])).

tff(c_2215,plain,(
    ! [C_162,A_160,E_163,F_161,B_165,D_164] :
      ( k1_partfun1(A_160,B_165,C_162,D_164,E_163,F_161) = k5_relat_1(E_163,F_161)
      | ~ m1_subset_1(F_161,k1_zfmisc_1(k2_zfmisc_1(C_162,D_164)))
      | ~ v1_funct_1(F_161)
      | ~ m1_subset_1(E_163,k1_zfmisc_1(k2_zfmisc_1(A_160,B_165)))
      | ~ v1_funct_1(E_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2221,plain,(
    ! [A_160,B_165,E_163] :
      ( k1_partfun1(A_160,B_165,'#skF_2','#skF_1',E_163,'#skF_4') = k5_relat_1(E_163,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_163,k1_zfmisc_1(k2_zfmisc_1(A_160,B_165)))
      | ~ v1_funct_1(E_163) ) ),
    inference(resolution,[status(thm)],[c_76,c_2215])).

tff(c_2470,plain,(
    ! [A_173,B_174,E_175] :
      ( k1_partfun1(A_173,B_174,'#skF_2','#skF_1',E_175,'#skF_4') = k5_relat_1(E_175,'#skF_4')
      | ~ m1_subset_1(E_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174)))
      | ~ v1_funct_1(E_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2221])).

tff(c_2476,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_2470])).

tff(c_2483,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1919,c_2476])).

tff(c_1936,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1112])).

tff(c_74,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_2506,plain,(
    ! [B_176,C_177,A_178] :
      ( k6_partfun1(B_176) = k5_relat_1(k2_funct_1(C_177),C_177)
      | k1_xboole_0 = B_176
      | ~ v2_funct_1(C_177)
      | k2_relset_1(A_178,B_176,C_177) != B_176
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_178,B_176)))
      | ~ v1_funct_2(C_177,A_178,B_176)
      | ~ v1_funct_1(C_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2510,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_2506])).

tff(c_2516,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_70,c_2510])).

tff(c_2517,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2516])).

tff(c_2,plain,(
    ! [A_1,B_5,C_7] :
      ( k5_relat_1(k5_relat_1(A_1,B_5),C_7) = k5_relat_1(A_1,k5_relat_1(B_5,C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2534,plain,(
    ! [C_7] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_7)) = k5_relat_1(k6_partfun1('#skF_2'),C_7)
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2517,c_2])).

tff(c_3946,plain,(
    ! [C_203] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_203)) = k5_relat_1(k6_partfun1('#skF_2'),C_203)
      | ~ v1_relat_1(C_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1936,c_149,c_2534])).

tff(c_4006,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2483,c_3946])).

tff(c_4039,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_1935,c_509,c_4006])).

tff(c_4041,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_4039])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:48:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.72/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.72/2.10  
% 5.72/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.72/2.10  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.72/2.10  
% 5.72/2.10  %Foreground sorts:
% 5.72/2.10  
% 5.72/2.10  
% 5.72/2.10  %Background operators:
% 5.72/2.10  
% 5.72/2.10  
% 5.72/2.10  %Foreground operators:
% 5.72/2.10  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.72/2.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.72/2.10  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.72/2.10  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.72/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.72/2.10  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.72/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.72/2.10  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.72/2.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.72/2.10  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.72/2.10  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.72/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.72/2.10  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.72/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.72/2.10  tff('#skF_1', type, '#skF_1': $i).
% 5.72/2.10  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.72/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.72/2.10  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.72/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.72/2.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.72/2.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.72/2.10  tff('#skF_4', type, '#skF_4': $i).
% 5.72/2.10  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.72/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.72/2.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.72/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.72/2.10  
% 5.85/2.12  tff(f_189, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 5.85/2.12  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.85/2.12  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.85/2.12  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.85/2.12  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.85/2.12  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 5.85/2.12  tff(f_147, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.85/2.12  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 5.85/2.12  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 5.85/2.12  tff(f_131, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.85/2.12  tff(f_135, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.85/2.12  tff(f_101, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.85/2.12  tff(f_145, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.85/2.12  tff(f_163, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 5.85/2.12  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 5.85/2.12  tff(c_64, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_189])).
% 5.85/2.12  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_189])).
% 5.85/2.12  tff(c_138, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.85/2.12  tff(c_150, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_138])).
% 5.85/2.12  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_189])).
% 5.85/2.12  tff(c_149, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_138])).
% 5.85/2.12  tff(c_86, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 5.85/2.12  tff(c_14, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.85/2.12  tff(c_70, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_189])).
% 5.85/2.12  tff(c_66, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_189])).
% 5.85/2.12  tff(c_84, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_189])).
% 5.85/2.12  tff(c_212, plain, (![A_66, B_67, C_68]: (k1_relset_1(A_66, B_67, C_68)=k1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.85/2.12  tff(c_224, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_212])).
% 5.85/2.12  tff(c_471, plain, (![B_88, A_89, C_90]: (k1_xboole_0=B_88 | k1_relset_1(A_89, B_88, C_90)=A_89 | ~v1_funct_2(C_90, A_89, B_88) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.85/2.12  tff(c_477, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_82, c_471])).
% 5.85/2.12  tff(c_485, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_224, c_477])).
% 5.85/2.12  tff(c_486, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_66, c_485])).
% 5.85/2.12  tff(c_166, plain, (![A_59]: (k2_relat_1(k2_funct_1(A_59))=k1_relat_1(A_59) | ~v2_funct_1(A_59) | ~v1_funct_1(A_59) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.85/2.12  tff(c_58, plain, (![A_41]: (k6_relat_1(A_41)=k6_partfun1(A_41))), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.85/2.12  tff(c_10, plain, (![A_10]: (k5_relat_1(A_10, k6_relat_1(k2_relat_1(A_10)))=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.85/2.12  tff(c_87, plain, (![A_10]: (k5_relat_1(A_10, k6_partfun1(k2_relat_1(A_10)))=A_10 | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_10])).
% 5.85/2.12  tff(c_1072, plain, (![A_107]: (k5_relat_1(k2_funct_1(A_107), k6_partfun1(k1_relat_1(A_107)))=k2_funct_1(A_107) | ~v1_relat_1(k2_funct_1(A_107)) | ~v2_funct_1(A_107) | ~v1_funct_1(A_107) | ~v1_relat_1(A_107))), inference(superposition, [status(thm), theory('equality')], [c_166, c_87])).
% 5.85/2.12  tff(c_1090, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_486, c_1072])).
% 5.85/2.12  tff(c_1112, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_86, c_70, c_1090])).
% 5.85/2.12  tff(c_1927, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1112])).
% 5.85/2.12  tff(c_1930, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_1927])).
% 5.85/2.12  tff(c_1934, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149, c_86, c_1930])).
% 5.85/2.12  tff(c_1935, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_1112])).
% 5.85/2.12  tff(c_68, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_189])).
% 5.85/2.12  tff(c_78, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_189])).
% 5.85/2.12  tff(c_225, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_212])).
% 5.85/2.12  tff(c_480, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_76, c_471])).
% 5.85/2.12  tff(c_489, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_225, c_480])).
% 5.85/2.12  tff(c_490, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_68, c_489])).
% 5.85/2.12  tff(c_8, plain, (![A_9]: (k5_relat_1(k6_relat_1(k1_relat_1(A_9)), A_9)=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.85/2.12  tff(c_88, plain, (![A_9]: (k5_relat_1(k6_partfun1(k1_relat_1(A_9)), A_9)=A_9 | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_8])).
% 5.85/2.12  tff(c_505, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_490, c_88])).
% 5.85/2.12  tff(c_509, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_505])).
% 5.85/2.12  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_189])).
% 5.85/2.12  tff(c_1857, plain, (![E_143, F_142, A_144, D_147, C_145, B_146]: (m1_subset_1(k1_partfun1(A_144, B_146, C_145, D_147, E_143, F_142), k1_zfmisc_1(k2_zfmisc_1(A_144, D_147))) | ~m1_subset_1(F_142, k1_zfmisc_1(k2_zfmisc_1(C_145, D_147))) | ~v1_funct_1(F_142) | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(A_144, B_146))) | ~v1_funct_1(E_143))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.85/2.12  tff(c_54, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.85/2.12  tff(c_72, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_189])).
% 5.85/2.12  tff(c_905, plain, (![D_101, C_102, A_103, B_104]: (D_101=C_102 | ~r2_relset_1(A_103, B_104, C_102, D_101) | ~m1_subset_1(D_101, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.85/2.12  tff(c_913, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_72, c_905])).
% 5.85/2.12  tff(c_928, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_913])).
% 5.85/2.12  tff(c_1115, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_928])).
% 5.85/2.12  tff(c_1872, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1857, c_1115])).
% 5.85/2.12  tff(c_1918, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_1872])).
% 5.85/2.12  tff(c_1919, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_928])).
% 5.85/2.12  tff(c_2215, plain, (![C_162, A_160, E_163, F_161, B_165, D_164]: (k1_partfun1(A_160, B_165, C_162, D_164, E_163, F_161)=k5_relat_1(E_163, F_161) | ~m1_subset_1(F_161, k1_zfmisc_1(k2_zfmisc_1(C_162, D_164))) | ~v1_funct_1(F_161) | ~m1_subset_1(E_163, k1_zfmisc_1(k2_zfmisc_1(A_160, B_165))) | ~v1_funct_1(E_163))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.85/2.12  tff(c_2221, plain, (![A_160, B_165, E_163]: (k1_partfun1(A_160, B_165, '#skF_2', '#skF_1', E_163, '#skF_4')=k5_relat_1(E_163, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_163, k1_zfmisc_1(k2_zfmisc_1(A_160, B_165))) | ~v1_funct_1(E_163))), inference(resolution, [status(thm)], [c_76, c_2215])).
% 5.85/2.12  tff(c_2470, plain, (![A_173, B_174, E_175]: (k1_partfun1(A_173, B_174, '#skF_2', '#skF_1', E_175, '#skF_4')=k5_relat_1(E_175, '#skF_4') | ~m1_subset_1(E_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))) | ~v1_funct_1(E_175))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2221])).
% 5.85/2.12  tff(c_2476, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_2470])).
% 5.85/2.12  tff(c_2483, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1919, c_2476])).
% 5.85/2.12  tff(c_1936, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1112])).
% 5.85/2.12  tff(c_74, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_189])).
% 5.85/2.12  tff(c_2506, plain, (![B_176, C_177, A_178]: (k6_partfun1(B_176)=k5_relat_1(k2_funct_1(C_177), C_177) | k1_xboole_0=B_176 | ~v2_funct_1(C_177) | k2_relset_1(A_178, B_176, C_177)!=B_176 | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_178, B_176))) | ~v1_funct_2(C_177, A_178, B_176) | ~v1_funct_1(C_177))), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.85/2.12  tff(c_2510, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_2506])).
% 5.85/2.12  tff(c_2516, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_70, c_2510])).
% 5.85/2.12  tff(c_2517, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_66, c_2516])).
% 5.85/2.12  tff(c_2, plain, (![A_1, B_5, C_7]: (k5_relat_1(k5_relat_1(A_1, B_5), C_7)=k5_relat_1(A_1, k5_relat_1(B_5, C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1(B_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.85/2.12  tff(c_2534, plain, (![C_7]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_7))=k5_relat_1(k6_partfun1('#skF_2'), C_7) | ~v1_relat_1(C_7) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2517, c_2])).
% 5.85/2.12  tff(c_3946, plain, (![C_203]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_203))=k5_relat_1(k6_partfun1('#skF_2'), C_203) | ~v1_relat_1(C_203))), inference(demodulation, [status(thm), theory('equality')], [c_1936, c_149, c_2534])).
% 5.85/2.12  tff(c_4006, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2483, c_3946])).
% 5.85/2.12  tff(c_4039, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_1935, c_509, c_4006])).
% 5.85/2.12  tff(c_4041, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_4039])).
% 5.85/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.85/2.12  
% 5.85/2.12  Inference rules
% 5.85/2.12  ----------------------
% 5.85/2.12  #Ref     : 0
% 5.85/2.12  #Sup     : 844
% 5.85/2.12  #Fact    : 0
% 5.85/2.12  #Define  : 0
% 5.85/2.12  #Split   : 8
% 5.85/2.12  #Chain   : 0
% 5.85/2.12  #Close   : 0
% 5.85/2.12  
% 5.85/2.12  Ordering : KBO
% 5.85/2.12  
% 5.85/2.12  Simplification rules
% 5.85/2.12  ----------------------
% 5.85/2.12  #Subsume      : 23
% 5.85/2.12  #Demod        : 1323
% 5.85/2.12  #Tautology    : 447
% 5.85/2.12  #SimpNegUnit  : 27
% 5.85/2.12  #BackRed      : 17
% 5.85/2.12  
% 5.85/2.12  #Partial instantiations: 0
% 5.85/2.12  #Strategies tried      : 1
% 5.85/2.12  
% 5.85/2.12  Timing (in seconds)
% 5.85/2.12  ----------------------
% 5.85/2.12  Preprocessing        : 0.38
% 5.85/2.12  Parsing              : 0.19
% 5.85/2.12  CNF conversion       : 0.03
% 5.85/2.12  Main loop            : 0.96
% 5.85/2.12  Inferencing          : 0.33
% 5.85/2.12  Reduction            : 0.38
% 5.85/2.12  Demodulation         : 0.28
% 5.85/2.12  BG Simplification    : 0.05
% 5.85/2.12  Subsumption          : 0.15
% 5.85/2.12  Abstraction          : 0.05
% 5.85/2.12  MUC search           : 0.00
% 5.85/2.12  Cooper               : 0.00
% 5.85/2.12  Total                : 1.38
% 5.85/2.12  Index Insertion      : 0.00
% 5.85/2.12  Index Deletion       : 0.00
% 5.85/2.12  Index Matching       : 0.00
% 5.85/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
