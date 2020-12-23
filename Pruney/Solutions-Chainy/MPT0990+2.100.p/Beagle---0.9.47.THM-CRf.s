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
% DateTime   : Thu Dec  3 10:13:10 EST 2020

% Result     : Theorem 11.25s
% Output     : CNFRefutation 11.25s
% Verified   : 
% Statistics : Number of formulae       :  191 (5250 expanded)
%              Number of leaves         :   39 (1896 expanded)
%              Depth                    :   21
%              Number of atoms          :  514 (24565 expanded)
%              Number of equality atoms :  184 (9061 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_200,negated_conjecture,(
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

tff(f_115,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_174,axiom,(
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

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_113,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_91,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_132,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_158,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
              & k2_relset_1(A,B,D) = B )
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | ( v2_funct_1(D)
                & v2_funct_1(E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(c_48,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_32,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4,plain,(
    ! [A_1] : k2_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    ! [A_1] : k2_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_122,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_133,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_122])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_1505,plain,(
    ! [B_169,C_170,A_171] :
      ( k6_partfun1(B_169) = k5_relat_1(k2_funct_1(C_170),C_170)
      | k1_xboole_0 = B_169
      | ~ v2_funct_1(C_170)
      | k2_relset_1(A_171,B_169,C_170) != B_169
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_171,B_169)))
      | ~ v1_funct_2(C_170,A_171,B_169)
      | ~ v1_funct_1(C_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1509,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1505])).

tff(c_1515,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_54,c_1509])).

tff(c_1516,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1515])).

tff(c_12,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_relat_1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_74,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_partfun1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12])).

tff(c_1533,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1516,c_74])).

tff(c_1547,plain,(
    k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_70,c_54,c_1533])).

tff(c_1584,plain,(
    k2_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1547,c_76])).

tff(c_1601,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1584])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_315,plain,(
    ! [E_90,F_91,A_92,B_89,C_88,D_93] :
      ( k1_partfun1(A_92,B_89,C_88,D_93,E_90,F_91) = k5_relat_1(E_90,F_91)
      | ~ m1_subset_1(F_91,k1_zfmisc_1(k2_zfmisc_1(C_88,D_93)))
      | ~ v1_funct_1(F_91)
      | ~ m1_subset_1(E_90,k1_zfmisc_1(k2_zfmisc_1(A_92,B_89)))
      | ~ v1_funct_1(E_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_321,plain,(
    ! [A_92,B_89,E_90] :
      ( k1_partfun1(A_92,B_89,'#skF_2','#skF_1',E_90,'#skF_4') = k5_relat_1(E_90,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_90,k1_zfmisc_1(k2_zfmisc_1(A_92,B_89)))
      | ~ v1_funct_1(E_90) ) ),
    inference(resolution,[status(thm)],[c_60,c_315])).

tff(c_363,plain,(
    ! [A_99,B_100,E_101] :
      ( k1_partfun1(A_99,B_100,'#skF_2','#skF_1',E_101,'#skF_4') = k5_relat_1(E_101,'#skF_4')
      | ~ m1_subset_1(E_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ v1_funct_1(E_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_321])).

tff(c_369,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_363])).

tff(c_376,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_369])).

tff(c_24,plain,(
    ! [A_17] : m1_subset_1(k6_relat_1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_71,plain,(
    ! [A_17] : m1_subset_1(k6_partfun1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_24])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_216,plain,(
    ! [D_67,C_68,A_69,B_70] :
      ( D_67 = C_68
      | ~ r2_relset_1(A_69,B_70,C_68,D_67)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_224,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_216])).

tff(c_239,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_224])).

tff(c_240,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_381,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_240])).

tff(c_648,plain,(
    ! [A_108,D_112,C_109,E_110,B_113,F_111] :
      ( m1_subset_1(k1_partfun1(A_108,B_113,C_109,D_112,E_110,F_111),k1_zfmisc_1(k2_zfmisc_1(A_108,D_112)))
      | ~ m1_subset_1(F_111,k1_zfmisc_1(k2_zfmisc_1(C_109,D_112)))
      | ~ v1_funct_1(F_111)
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_113)))
      | ~ v1_funct_1(E_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_676,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_648])).

tff(c_694,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_676])).

tff(c_699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_694])).

tff(c_700,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_789,plain,(
    ! [B_133,C_132,F_135,D_137,E_134,A_136] :
      ( k1_partfun1(A_136,B_133,C_132,D_137,E_134,F_135) = k5_relat_1(E_134,F_135)
      | ~ m1_subset_1(F_135,k1_zfmisc_1(k2_zfmisc_1(C_132,D_137)))
      | ~ v1_funct_1(F_135)
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_136,B_133)))
      | ~ v1_funct_1(E_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_795,plain,(
    ! [A_136,B_133,E_134] :
      ( k1_partfun1(A_136,B_133,'#skF_2','#skF_1',E_134,'#skF_4') = k5_relat_1(E_134,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_136,B_133)))
      | ~ v1_funct_1(E_134) ) ),
    inference(resolution,[status(thm)],[c_60,c_789])).

tff(c_843,plain,(
    ! [A_142,B_143,E_144] :
      ( k1_partfun1(A_142,B_143,'#skF_2','#skF_1',E_144,'#skF_4') = k5_relat_1(E_144,'#skF_4')
      | ~ m1_subset_1(E_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143)))
      | ~ v1_funct_1(E_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_795])).

tff(c_849,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_843])).

tff(c_856,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_700,c_849])).

tff(c_134,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_122])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_860,plain,(
    ! [A_145,C_146,B_147] :
      ( k6_partfun1(A_145) = k5_relat_1(C_146,k2_funct_1(C_146))
      | k1_xboole_0 = B_147
      | ~ v2_funct_1(C_146)
      | k2_relset_1(A_145,B_147,C_146) != B_147
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_145,B_147)))
      | ~ v1_funct_2(C_146,A_145,B_147)
      | ~ v1_funct_1(C_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_866,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_860])).

tff(c_874,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_866])).

tff(c_875,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_874])).

tff(c_982,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_875])).

tff(c_147,plain,(
    ! [A_56,B_57,D_58] :
      ( r2_relset_1(A_56,B_57,D_58,D_58)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_154,plain,(
    ! [A_17] : r2_relset_1(A_17,A_17,k6_partfun1(A_17),k6_partfun1(A_17)) ),
    inference(resolution,[status(thm)],[c_71,c_147])).

tff(c_1421,plain,(
    ! [A_165,B_166,C_167,D_168] :
      ( k2_relset_1(A_165,B_166,C_167) = B_166
      | ~ r2_relset_1(B_166,B_166,k1_partfun1(B_166,A_165,A_165,B_166,D_168,C_167),k6_partfun1(B_166))
      | ~ m1_subset_1(D_168,k1_zfmisc_1(k2_zfmisc_1(B_166,A_165)))
      | ~ v1_funct_2(D_168,B_166,A_165)
      | ~ v1_funct_1(D_168)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166)))
      | ~ v1_funct_2(C_167,A_165,B_166)
      | ~ v1_funct_1(C_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1427,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_700,c_1421])).

tff(c_1431,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_154,c_1427])).

tff(c_1433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_982,c_1431])).

tff(c_1435,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_875])).

tff(c_1511,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1505])).

tff(c_1519,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1435,c_1511])).

tff(c_1520,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1519])).

tff(c_1604,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1520])).

tff(c_733,plain,(
    ! [B_122,E_119,F_120,A_117,D_121,C_118] :
      ( v1_funct_1(k1_partfun1(A_117,B_122,C_118,D_121,E_119,F_120))
      | ~ m1_subset_1(F_120,k1_zfmisc_1(k2_zfmisc_1(C_118,D_121)))
      | ~ v1_funct_1(F_120)
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_122)))
      | ~ v1_funct_1(E_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_739,plain,(
    ! [A_117,B_122,E_119] :
      ( v1_funct_1(k1_partfun1(A_117,B_122,'#skF_2','#skF_1',E_119,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_122)))
      | ~ v1_funct_1(E_119) ) ),
    inference(resolution,[status(thm)],[c_60,c_733])).

tff(c_764,plain,(
    ! [A_126,B_127,E_128] :
      ( v1_funct_1(k1_partfun1(A_126,B_127,'#skF_2','#skF_1',E_128,'#skF_4'))
      | ~ m1_subset_1(E_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ v1_funct_1(E_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_739])).

tff(c_770,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_764])).

tff(c_777,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_700,c_770])).

tff(c_864,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_860])).

tff(c_870,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_54,c_864])).

tff(c_871,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_870])).

tff(c_14,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_relat_1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_73,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_partfun1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_14])).

tff(c_899,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_871,c_73])).

tff(c_910,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_70,c_54,c_899])).

tff(c_132,plain,(
    ! [A_17] : v1_relat_1(k6_partfun1(A_17)) ),
    inference(resolution,[status(thm)],[c_71,c_122])).

tff(c_6,plain,(
    ! [A_2] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_2)),A_2) = A_2
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_75,plain,(
    ! [A_2] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_2)),A_2) = A_2
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6])).

tff(c_176,plain,(
    ! [B_62,A_63] :
      ( v2_funct_1(B_62)
      | k2_relat_1(B_62) != k1_relat_1(A_63)
      | ~ v2_funct_1(k5_relat_1(B_62,A_63))
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62)
      | ~ v1_funct_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_188,plain,(
    ! [A_2] :
      ( v2_funct_1(k6_partfun1(k1_relat_1(A_2)))
      | k2_relat_1(k6_partfun1(k1_relat_1(A_2))) != k1_relat_1(A_2)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(k6_partfun1(k1_relat_1(A_2)))
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_2)))
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_176])).

tff(c_192,plain,(
    ! [A_2] :
      ( v2_funct_1(k6_partfun1(k1_relat_1(A_2)))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(k6_partfun1(k1_relat_1(A_2)))
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_76,c_188])).

tff(c_931,plain,
    ( v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1(k6_partfun1(k1_relat_1('#skF_3')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_910,c_192])).

tff(c_971,plain,(
    v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_70,c_777,c_910,c_54,c_931])).

tff(c_1902,plain,(
    ! [A_191,B_194,C_195,D_193,E_192] :
      ( k1_xboole_0 = C_195
      | v2_funct_1(E_192)
      | k2_relset_1(A_191,B_194,D_193) != B_194
      | ~ v2_funct_1(k1_partfun1(A_191,B_194,B_194,C_195,D_193,E_192))
      | ~ m1_subset_1(E_192,k1_zfmisc_1(k2_zfmisc_1(B_194,C_195)))
      | ~ v1_funct_2(E_192,B_194,C_195)
      | ~ v1_funct_1(E_192)
      | ~ m1_subset_1(D_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_194)))
      | ~ v1_funct_2(D_193,A_191,B_194)
      | ~ v1_funct_1(D_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_1908,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_700,c_1902])).

tff(c_1916,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_971,c_58,c_1908])).

tff(c_1918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1604,c_52,c_1916])).

tff(c_1920,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1520])).

tff(c_1434,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_875])).

tff(c_2081,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1920,c_1434])).

tff(c_2091,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2081,c_73])).

tff(c_2102,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_64,c_1920,c_2091])).

tff(c_2146,plain,(
    k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2102,c_76])).

tff(c_2167,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2146])).

tff(c_1919,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1520])).

tff(c_1942,plain,
    ( k6_partfun1(k2_relat_1('#skF_4')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1919,c_74])).

tff(c_1956,plain,(
    k6_partfun1(k2_relat_1('#skF_4')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_64,c_1920,c_1942])).

tff(c_16,plain,(
    ! [A_7,B_9] :
      ( k2_funct_1(A_7) = B_9
      | k6_relat_1(k2_relat_1(A_7)) != k5_relat_1(B_9,A_7)
      | k2_relat_1(B_9) != k1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_72,plain,(
    ! [A_7,B_9] :
      ( k2_funct_1(A_7) = B_9
      | k6_partfun1(k2_relat_1(A_7)) != k5_relat_1(B_9,A_7)
      | k2_relat_1(B_9) != k1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_16])).

tff(c_1974,plain,(
    ! [B_9] :
      ( k2_funct_1('#skF_4') = B_9
      | k5_relat_1(B_9,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_9) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1956,c_72])).

tff(c_2009,plain,(
    ! [B_9] :
      ( k2_funct_1('#skF_4') = B_9
      | k5_relat_1(B_9,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_9) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_64,c_1920,c_1974])).

tff(c_14540,plain,(
    ! [B_667] :
      ( k2_funct_1('#skF_4') = B_667
      | k5_relat_1(B_667,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_667) != '#skF_2'
      | ~ v1_funct_1(B_667)
      | ~ v1_relat_1(B_667) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2167,c_2009])).

tff(c_14630,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_14540])).

tff(c_14716,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1601,c_856,c_14630])).

tff(c_954,plain,(
    k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_910,c_76])).

tff(c_979,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_954])).

tff(c_13438,plain,(
    ! [B_624] :
      ( k2_funct_1('#skF_4') = B_624
      | k5_relat_1(B_624,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_624) != '#skF_2'
      | ~ v1_funct_1(B_624)
      | ~ v1_relat_1(B_624) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2167,c_2009])).

tff(c_13528,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_13438])).

tff(c_13614,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1601,c_856,c_13528])).

tff(c_4136,plain,(
    ! [B_295] :
      ( k2_funct_1('#skF_4') = B_295
      | k5_relat_1(B_295,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_295) != '#skF_2'
      | ~ v1_funct_1(B_295)
      | ~ v1_relat_1(B_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2167,c_2009])).

tff(c_4223,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_4136])).

tff(c_4305,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1601,c_856,c_4223])).

tff(c_10,plain,(
    ! [B_5,A_3] :
      ( v2_funct_1(B_5)
      | k2_relat_1(B_5) != k1_relat_1(A_3)
      | ~ v2_funct_1(k5_relat_1(B_5,A_3))
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1939,plain,
    ( v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1919,c_10])).

tff(c_1954,plain,
    ( v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1(k2_funct_1('#skF_4')) != k1_relat_1('#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_64,c_971,c_1939])).

tff(c_2625,plain,
    ( v2_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1(k2_funct_1('#skF_4')) != '#skF_2'
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2167,c_1954])).

tff(c_2626,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2625])).

tff(c_4307,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4305,c_2626])).

tff(c_4312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_4307])).

tff(c_4314,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2625])).

tff(c_11726,plain,(
    ! [B_564] :
      ( k2_funct_1('#skF_4') = B_564
      | k5_relat_1(B_564,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_564) != '#skF_2'
      | ~ v1_funct_1(B_564)
      | ~ v1_relat_1(B_564) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2167,c_2009])).

tff(c_11816,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_11726])).

tff(c_11901,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1601,c_856,c_11816])).

tff(c_9994,plain,(
    ! [B_504] :
      ( k2_funct_1('#skF_4') = B_504
      | k5_relat_1(B_504,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_504) != '#skF_2'
      | ~ v1_funct_1(B_504)
      | ~ v1_relat_1(B_504) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2167,c_2009])).

tff(c_10084,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_9994])).

tff(c_10169,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1601,c_856,c_10084])).

tff(c_4313,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1(k2_funct_1('#skF_4')) != '#skF_2'
    | v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2625])).

tff(c_4315,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4313])).

tff(c_10177,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10169,c_4315])).

tff(c_10189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1601,c_10177])).

tff(c_10190,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_4'))
    | v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4313])).

tff(c_10200,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_10190])).

tff(c_11903,plain,(
    ~ v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11901,c_10200])).

tff(c_11910,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_11903])).

tff(c_11912,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_10190])).

tff(c_11911,plain,(
    v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_10190])).

tff(c_1994,plain,(
    k2_relat_1(k6_partfun1('#skF_1')) = k2_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1956,c_76])).

tff(c_2015,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1994])).

tff(c_10191,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4313])).

tff(c_709,plain,(
    ! [A_114,B_115] :
      ( k2_funct_1(A_114) = B_115
      | k6_partfun1(k2_relat_1(A_114)) != k5_relat_1(B_115,A_114)
      | k2_relat_1(B_115) != k1_relat_1(A_114)
      | ~ v2_funct_1(A_114)
      | ~ v1_funct_1(B_115)
      | ~ v1_relat_1(B_115)
      | ~ v1_funct_1(A_114)
      | ~ v1_relat_1(A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_16])).

tff(c_12749,plain,(
    ! [A_587] :
      ( k2_funct_1(k2_funct_1(A_587)) = A_587
      | k6_partfun1(k2_relat_1(k2_funct_1(A_587))) != k6_partfun1(k1_relat_1(A_587))
      | k1_relat_1(k2_funct_1(A_587)) != k2_relat_1(A_587)
      | ~ v2_funct_1(k2_funct_1(A_587))
      | ~ v1_funct_1(A_587)
      | ~ v1_relat_1(A_587)
      | ~ v1_funct_1(k2_funct_1(A_587))
      | ~ v1_relat_1(k2_funct_1(A_587))
      | ~ v2_funct_1(A_587)
      | ~ v1_funct_1(A_587)
      | ~ v1_relat_1(A_587) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_709])).

tff(c_12752,plain,
    ( k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4'
    | k6_partfun1(k1_relat_1('#skF_4')) != k6_partfun1('#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != k2_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10191,c_12749])).

tff(c_12757,plain,
    ( k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_64,c_1920,c_4314,c_11912,c_134,c_64,c_11911,c_2015,c_2167,c_12752])).

tff(c_12760,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_12757])).

tff(c_13616,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13614,c_12760])).

tff(c_13625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_13616])).

tff(c_13626,plain,(
    k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_12757])).

tff(c_14723,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14716,c_13626])).

tff(c_14733,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_14723])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.25/4.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.25/4.70  
% 11.25/4.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.25/4.70  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 11.25/4.70  
% 11.25/4.70  %Foreground sorts:
% 11.25/4.70  
% 11.25/4.70  
% 11.25/4.70  %Background operators:
% 11.25/4.70  
% 11.25/4.70  
% 11.25/4.70  %Foreground operators:
% 11.25/4.70  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.25/4.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.25/4.70  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.25/4.70  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.25/4.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.25/4.70  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 11.25/4.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.25/4.70  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 11.25/4.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.25/4.70  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.25/4.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.25/4.70  tff('#skF_2', type, '#skF_2': $i).
% 11.25/4.70  tff('#skF_3', type, '#skF_3': $i).
% 11.25/4.70  tff('#skF_1', type, '#skF_1': $i).
% 11.25/4.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.25/4.70  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 11.25/4.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.25/4.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.25/4.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.25/4.70  tff('#skF_4', type, '#skF_4': $i).
% 11.25/4.70  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.25/4.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.25/4.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.25/4.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.25/4.70  
% 11.25/4.73  tff(f_200, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 11.25/4.73  tff(f_115, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 11.25/4.73  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 11.25/4.73  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.25/4.73  tff(f_174, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 11.25/4.73  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 11.25/4.73  tff(f_113, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 11.25/4.73  tff(f_91, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 11.25/4.73  tff(f_89, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 11.25/4.73  tff(f_103, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 11.25/4.73  tff(f_132, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 11.25/4.73  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 11.25/4.73  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 11.25/4.73  tff(f_158, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 11.25/4.73  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 11.25/4.73  tff(c_48, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_200])).
% 11.25/4.73  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_200])).
% 11.25/4.73  tff(c_32, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.25/4.73  tff(c_4, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.25/4.73  tff(c_76, plain, (![A_1]: (k2_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4])).
% 11.25/4.73  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_200])).
% 11.25/4.73  tff(c_122, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.25/4.73  tff(c_133, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_122])).
% 11.25/4.73  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_200])).
% 11.25/4.73  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_200])).
% 11.25/4.73  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_200])).
% 11.25/4.73  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_200])).
% 11.25/4.73  tff(c_1505, plain, (![B_169, C_170, A_171]: (k6_partfun1(B_169)=k5_relat_1(k2_funct_1(C_170), C_170) | k1_xboole_0=B_169 | ~v2_funct_1(C_170) | k2_relset_1(A_171, B_169, C_170)!=B_169 | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_171, B_169))) | ~v1_funct_2(C_170, A_171, B_169) | ~v1_funct_1(C_170))), inference(cnfTransformation, [status(thm)], [f_174])).
% 11.25/4.73  tff(c_1509, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1505])).
% 11.25/4.73  tff(c_1515, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_54, c_1509])).
% 11.25/4.73  tff(c_1516, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_1515])).
% 11.25/4.73  tff(c_12, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_relat_1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.25/4.73  tff(c_74, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_partfun1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12])).
% 11.25/4.73  tff(c_1533, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1516, c_74])).
% 11.25/4.73  tff(c_1547, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_70, c_54, c_1533])).
% 11.25/4.73  tff(c_1584, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1547, c_76])).
% 11.25/4.73  tff(c_1601, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1584])).
% 11.25/4.73  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_200])).
% 11.25/4.73  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_200])).
% 11.25/4.73  tff(c_315, plain, (![E_90, F_91, A_92, B_89, C_88, D_93]: (k1_partfun1(A_92, B_89, C_88, D_93, E_90, F_91)=k5_relat_1(E_90, F_91) | ~m1_subset_1(F_91, k1_zfmisc_1(k2_zfmisc_1(C_88, D_93))) | ~v1_funct_1(F_91) | ~m1_subset_1(E_90, k1_zfmisc_1(k2_zfmisc_1(A_92, B_89))) | ~v1_funct_1(E_90))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.25/4.73  tff(c_321, plain, (![A_92, B_89, E_90]: (k1_partfun1(A_92, B_89, '#skF_2', '#skF_1', E_90, '#skF_4')=k5_relat_1(E_90, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_90, k1_zfmisc_1(k2_zfmisc_1(A_92, B_89))) | ~v1_funct_1(E_90))), inference(resolution, [status(thm)], [c_60, c_315])).
% 11.25/4.73  tff(c_363, plain, (![A_99, B_100, E_101]: (k1_partfun1(A_99, B_100, '#skF_2', '#skF_1', E_101, '#skF_4')=k5_relat_1(E_101, '#skF_4') | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~v1_funct_1(E_101))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_321])).
% 11.25/4.73  tff(c_369, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_363])).
% 11.25/4.73  tff(c_376, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_369])).
% 11.25/4.73  tff(c_24, plain, (![A_17]: (m1_subset_1(k6_relat_1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.25/4.73  tff(c_71, plain, (![A_17]: (m1_subset_1(k6_partfun1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_24])).
% 11.25/4.73  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_200])).
% 11.25/4.73  tff(c_216, plain, (![D_67, C_68, A_69, B_70]: (D_67=C_68 | ~r2_relset_1(A_69, B_70, C_68, D_67) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.25/4.73  tff(c_224, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_216])).
% 11.25/4.73  tff(c_239, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_224])).
% 11.25/4.73  tff(c_240, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_239])).
% 11.25/4.73  tff(c_381, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_376, c_240])).
% 11.25/4.73  tff(c_648, plain, (![A_108, D_112, C_109, E_110, B_113, F_111]: (m1_subset_1(k1_partfun1(A_108, B_113, C_109, D_112, E_110, F_111), k1_zfmisc_1(k2_zfmisc_1(A_108, D_112))) | ~m1_subset_1(F_111, k1_zfmisc_1(k2_zfmisc_1(C_109, D_112))) | ~v1_funct_1(F_111) | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_113))) | ~v1_funct_1(E_110))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.25/4.73  tff(c_676, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_376, c_648])).
% 11.25/4.73  tff(c_694, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_676])).
% 11.25/4.73  tff(c_699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_381, c_694])).
% 11.25/4.73  tff(c_700, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_239])).
% 11.25/4.73  tff(c_789, plain, (![B_133, C_132, F_135, D_137, E_134, A_136]: (k1_partfun1(A_136, B_133, C_132, D_137, E_134, F_135)=k5_relat_1(E_134, F_135) | ~m1_subset_1(F_135, k1_zfmisc_1(k2_zfmisc_1(C_132, D_137))) | ~v1_funct_1(F_135) | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_136, B_133))) | ~v1_funct_1(E_134))), inference(cnfTransformation, [status(thm)], [f_113])).
% 11.25/4.73  tff(c_795, plain, (![A_136, B_133, E_134]: (k1_partfun1(A_136, B_133, '#skF_2', '#skF_1', E_134, '#skF_4')=k5_relat_1(E_134, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_136, B_133))) | ~v1_funct_1(E_134))), inference(resolution, [status(thm)], [c_60, c_789])).
% 11.25/4.73  tff(c_843, plain, (![A_142, B_143, E_144]: (k1_partfun1(A_142, B_143, '#skF_2', '#skF_1', E_144, '#skF_4')=k5_relat_1(E_144, '#skF_4') | ~m1_subset_1(E_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))) | ~v1_funct_1(E_144))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_795])).
% 11.25/4.73  tff(c_849, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_843])).
% 11.25/4.73  tff(c_856, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_700, c_849])).
% 11.25/4.73  tff(c_134, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_122])).
% 11.25/4.73  tff(c_52, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_200])).
% 11.25/4.73  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_200])).
% 11.25/4.73  tff(c_860, plain, (![A_145, C_146, B_147]: (k6_partfun1(A_145)=k5_relat_1(C_146, k2_funct_1(C_146)) | k1_xboole_0=B_147 | ~v2_funct_1(C_146) | k2_relset_1(A_145, B_147, C_146)!=B_147 | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_145, B_147))) | ~v1_funct_2(C_146, A_145, B_147) | ~v1_funct_1(C_146))), inference(cnfTransformation, [status(thm)], [f_174])).
% 11.25/4.73  tff(c_866, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_860])).
% 11.25/4.73  tff(c_874, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_866])).
% 11.25/4.73  tff(c_875, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_52, c_874])).
% 11.25/4.73  tff(c_982, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_875])).
% 11.25/4.73  tff(c_147, plain, (![A_56, B_57, D_58]: (r2_relset_1(A_56, B_57, D_58, D_58) | ~m1_subset_1(D_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.25/4.73  tff(c_154, plain, (![A_17]: (r2_relset_1(A_17, A_17, k6_partfun1(A_17), k6_partfun1(A_17)))), inference(resolution, [status(thm)], [c_71, c_147])).
% 11.25/4.73  tff(c_1421, plain, (![A_165, B_166, C_167, D_168]: (k2_relset_1(A_165, B_166, C_167)=B_166 | ~r2_relset_1(B_166, B_166, k1_partfun1(B_166, A_165, A_165, B_166, D_168, C_167), k6_partfun1(B_166)) | ~m1_subset_1(D_168, k1_zfmisc_1(k2_zfmisc_1(B_166, A_165))) | ~v1_funct_2(D_168, B_166, A_165) | ~v1_funct_1(D_168) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))) | ~v1_funct_2(C_167, A_165, B_166) | ~v1_funct_1(C_167))), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.25/4.73  tff(c_1427, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_700, c_1421])).
% 11.25/4.73  tff(c_1431, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_154, c_1427])).
% 11.25/4.73  tff(c_1433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_982, c_1431])).
% 11.25/4.73  tff(c_1435, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_875])).
% 11.25/4.73  tff(c_1511, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_1505])).
% 11.25/4.73  tff(c_1519, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1435, c_1511])).
% 11.25/4.73  tff(c_1520, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_1519])).
% 11.25/4.73  tff(c_1604, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1520])).
% 11.25/4.73  tff(c_733, plain, (![B_122, E_119, F_120, A_117, D_121, C_118]: (v1_funct_1(k1_partfun1(A_117, B_122, C_118, D_121, E_119, F_120)) | ~m1_subset_1(F_120, k1_zfmisc_1(k2_zfmisc_1(C_118, D_121))) | ~v1_funct_1(F_120) | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_122))) | ~v1_funct_1(E_119))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.25/4.73  tff(c_739, plain, (![A_117, B_122, E_119]: (v1_funct_1(k1_partfun1(A_117, B_122, '#skF_2', '#skF_1', E_119, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_122))) | ~v1_funct_1(E_119))), inference(resolution, [status(thm)], [c_60, c_733])).
% 11.25/4.73  tff(c_764, plain, (![A_126, B_127, E_128]: (v1_funct_1(k1_partfun1(A_126, B_127, '#skF_2', '#skF_1', E_128, '#skF_4')) | ~m1_subset_1(E_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~v1_funct_1(E_128))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_739])).
% 11.25/4.73  tff(c_770, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_764])).
% 11.25/4.73  tff(c_777, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_700, c_770])).
% 11.25/4.73  tff(c_864, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_860])).
% 11.25/4.73  tff(c_870, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_54, c_864])).
% 11.25/4.73  tff(c_871, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_870])).
% 11.25/4.73  tff(c_14, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_relat_1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.25/4.73  tff(c_73, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_partfun1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_14])).
% 11.25/4.73  tff(c_899, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_871, c_73])).
% 11.25/4.73  tff(c_910, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_70, c_54, c_899])).
% 11.25/4.73  tff(c_132, plain, (![A_17]: (v1_relat_1(k6_partfun1(A_17)))), inference(resolution, [status(thm)], [c_71, c_122])).
% 11.25/4.73  tff(c_6, plain, (![A_2]: (k5_relat_1(k6_relat_1(k1_relat_1(A_2)), A_2)=A_2 | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.25/4.73  tff(c_75, plain, (![A_2]: (k5_relat_1(k6_partfun1(k1_relat_1(A_2)), A_2)=A_2 | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6])).
% 11.25/4.73  tff(c_176, plain, (![B_62, A_63]: (v2_funct_1(B_62) | k2_relat_1(B_62)!=k1_relat_1(A_63) | ~v2_funct_1(k5_relat_1(B_62, A_63)) | ~v1_funct_1(B_62) | ~v1_relat_1(B_62) | ~v1_funct_1(A_63) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.25/4.73  tff(c_188, plain, (![A_2]: (v2_funct_1(k6_partfun1(k1_relat_1(A_2))) | k2_relat_1(k6_partfun1(k1_relat_1(A_2)))!=k1_relat_1(A_2) | ~v2_funct_1(A_2) | ~v1_funct_1(k6_partfun1(k1_relat_1(A_2))) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_2))) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2) | ~v1_relat_1(A_2))), inference(superposition, [status(thm), theory('equality')], [c_75, c_176])).
% 11.25/4.73  tff(c_192, plain, (![A_2]: (v2_funct_1(k6_partfun1(k1_relat_1(A_2))) | ~v2_funct_1(A_2) | ~v1_funct_1(k6_partfun1(k1_relat_1(A_2))) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_76, c_188])).
% 11.25/4.73  tff(c_931, plain, (v2_funct_1(k6_partfun1('#skF_1')) | ~v2_funct_1('#skF_3') | ~v1_funct_1(k6_partfun1(k1_relat_1('#skF_3'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_910, c_192])).
% 11.25/4.73  tff(c_971, plain, (v2_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_70, c_777, c_910, c_54, c_931])).
% 11.25/4.73  tff(c_1902, plain, (![A_191, B_194, C_195, D_193, E_192]: (k1_xboole_0=C_195 | v2_funct_1(E_192) | k2_relset_1(A_191, B_194, D_193)!=B_194 | ~v2_funct_1(k1_partfun1(A_191, B_194, B_194, C_195, D_193, E_192)) | ~m1_subset_1(E_192, k1_zfmisc_1(k2_zfmisc_1(B_194, C_195))) | ~v1_funct_2(E_192, B_194, C_195) | ~v1_funct_1(E_192) | ~m1_subset_1(D_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_194))) | ~v1_funct_2(D_193, A_191, B_194) | ~v1_funct_1(D_193))), inference(cnfTransformation, [status(thm)], [f_158])).
% 11.25/4.73  tff(c_1908, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_700, c_1902])).
% 11.25/4.73  tff(c_1916, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_60, c_971, c_58, c_1908])).
% 11.25/4.73  tff(c_1918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1604, c_52, c_1916])).
% 11.25/4.73  tff(c_1920, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1520])).
% 11.25/4.73  tff(c_1434, plain, (~v2_funct_1('#skF_4') | k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_875])).
% 11.25/4.73  tff(c_2081, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1920, c_1434])).
% 11.25/4.73  tff(c_2091, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2081, c_73])).
% 11.25/4.73  tff(c_2102, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_64, c_1920, c_2091])).
% 11.25/4.73  tff(c_2146, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2102, c_76])).
% 11.25/4.73  tff(c_2167, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2146])).
% 11.25/4.73  tff(c_1919, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1520])).
% 11.25/4.73  tff(c_1942, plain, (k6_partfun1(k2_relat_1('#skF_4'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1919, c_74])).
% 11.25/4.73  tff(c_1956, plain, (k6_partfun1(k2_relat_1('#skF_4'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_64, c_1920, c_1942])).
% 11.25/4.73  tff(c_16, plain, (![A_7, B_9]: (k2_funct_1(A_7)=B_9 | k6_relat_1(k2_relat_1(A_7))!=k5_relat_1(B_9, A_7) | k2_relat_1(B_9)!=k1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_77])).
% 11.25/4.73  tff(c_72, plain, (![A_7, B_9]: (k2_funct_1(A_7)=B_9 | k6_partfun1(k2_relat_1(A_7))!=k5_relat_1(B_9, A_7) | k2_relat_1(B_9)!=k1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_16])).
% 11.25/4.73  tff(c_1974, plain, (![B_9]: (k2_funct_1('#skF_4')=B_9 | k5_relat_1(B_9, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_9)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1956, c_72])).
% 11.25/4.73  tff(c_2009, plain, (![B_9]: (k2_funct_1('#skF_4')=B_9 | k5_relat_1(B_9, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_9)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_64, c_1920, c_1974])).
% 11.25/4.73  tff(c_14540, plain, (![B_667]: (k2_funct_1('#skF_4')=B_667 | k5_relat_1(B_667, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_667)!='#skF_2' | ~v1_funct_1(B_667) | ~v1_relat_1(B_667))), inference(demodulation, [status(thm), theory('equality')], [c_2167, c_2009])).
% 11.25/4.73  tff(c_14630, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_133, c_14540])).
% 11.25/4.73  tff(c_14716, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1601, c_856, c_14630])).
% 11.25/4.73  tff(c_954, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_910, c_76])).
% 11.25/4.73  tff(c_979, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_954])).
% 11.25/4.73  tff(c_13438, plain, (![B_624]: (k2_funct_1('#skF_4')=B_624 | k5_relat_1(B_624, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_624)!='#skF_2' | ~v1_funct_1(B_624) | ~v1_relat_1(B_624))), inference(demodulation, [status(thm), theory('equality')], [c_2167, c_2009])).
% 11.25/4.73  tff(c_13528, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_133, c_13438])).
% 11.25/4.73  tff(c_13614, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1601, c_856, c_13528])).
% 11.25/4.73  tff(c_4136, plain, (![B_295]: (k2_funct_1('#skF_4')=B_295 | k5_relat_1(B_295, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_295)!='#skF_2' | ~v1_funct_1(B_295) | ~v1_relat_1(B_295))), inference(demodulation, [status(thm), theory('equality')], [c_2167, c_2009])).
% 11.25/4.73  tff(c_4223, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_133, c_4136])).
% 11.25/4.73  tff(c_4305, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1601, c_856, c_4223])).
% 11.25/4.73  tff(c_10, plain, (![B_5, A_3]: (v2_funct_1(B_5) | k2_relat_1(B_5)!=k1_relat_1(A_3) | ~v2_funct_1(k5_relat_1(B_5, A_3)) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.25/4.73  tff(c_1939, plain, (v2_funct_1(k2_funct_1('#skF_4')) | k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1919, c_10])).
% 11.25/4.73  tff(c_1954, plain, (v2_funct_1(k2_funct_1('#skF_4')) | k2_relat_1(k2_funct_1('#skF_4'))!=k1_relat_1('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_64, c_971, c_1939])).
% 11.25/4.73  tff(c_2625, plain, (v2_funct_1(k2_funct_1('#skF_4')) | k2_relat_1(k2_funct_1('#skF_4'))!='#skF_2' | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2167, c_1954])).
% 11.25/4.73  tff(c_2626, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_2625])).
% 11.25/4.73  tff(c_4307, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4305, c_2626])).
% 11.25/4.73  tff(c_4312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_4307])).
% 11.25/4.73  tff(c_4314, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2625])).
% 11.25/4.73  tff(c_11726, plain, (![B_564]: (k2_funct_1('#skF_4')=B_564 | k5_relat_1(B_564, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_564)!='#skF_2' | ~v1_funct_1(B_564) | ~v1_relat_1(B_564))), inference(demodulation, [status(thm), theory('equality')], [c_2167, c_2009])).
% 11.25/4.73  tff(c_11816, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_133, c_11726])).
% 11.25/4.73  tff(c_11901, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1601, c_856, c_11816])).
% 11.25/4.73  tff(c_9994, plain, (![B_504]: (k2_funct_1('#skF_4')=B_504 | k5_relat_1(B_504, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_504)!='#skF_2' | ~v1_funct_1(B_504) | ~v1_relat_1(B_504))), inference(demodulation, [status(thm), theory('equality')], [c_2167, c_2009])).
% 11.25/4.73  tff(c_10084, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_133, c_9994])).
% 11.25/4.73  tff(c_10169, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1601, c_856, c_10084])).
% 11.25/4.73  tff(c_4313, plain, (~v1_funct_1(k2_funct_1('#skF_4')) | k2_relat_1(k2_funct_1('#skF_4'))!='#skF_2' | v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2625])).
% 11.25/4.73  tff(c_4315, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_4313])).
% 11.25/4.73  tff(c_10177, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10169, c_4315])).
% 11.25/4.73  tff(c_10189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1601, c_10177])).
% 11.25/4.73  tff(c_10190, plain, (~v1_funct_1(k2_funct_1('#skF_4')) | v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4313])).
% 11.25/4.73  tff(c_10200, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_10190])).
% 11.25/4.73  tff(c_11903, plain, (~v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11901, c_10200])).
% 11.25/4.73  tff(c_11910, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_11903])).
% 11.25/4.73  tff(c_11912, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_10190])).
% 11.25/4.73  tff(c_11911, plain, (v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_10190])).
% 11.25/4.73  tff(c_1994, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k2_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1956, c_76])).
% 11.25/4.73  tff(c_2015, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1994])).
% 11.25/4.73  tff(c_10191, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(splitRight, [status(thm)], [c_4313])).
% 11.25/4.73  tff(c_709, plain, (![A_114, B_115]: (k2_funct_1(A_114)=B_115 | k6_partfun1(k2_relat_1(A_114))!=k5_relat_1(B_115, A_114) | k2_relat_1(B_115)!=k1_relat_1(A_114) | ~v2_funct_1(A_114) | ~v1_funct_1(B_115) | ~v1_relat_1(B_115) | ~v1_funct_1(A_114) | ~v1_relat_1(A_114))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_16])).
% 11.25/4.73  tff(c_12749, plain, (![A_587]: (k2_funct_1(k2_funct_1(A_587))=A_587 | k6_partfun1(k2_relat_1(k2_funct_1(A_587)))!=k6_partfun1(k1_relat_1(A_587)) | k1_relat_1(k2_funct_1(A_587))!=k2_relat_1(A_587) | ~v2_funct_1(k2_funct_1(A_587)) | ~v1_funct_1(A_587) | ~v1_relat_1(A_587) | ~v1_funct_1(k2_funct_1(A_587)) | ~v1_relat_1(k2_funct_1(A_587)) | ~v2_funct_1(A_587) | ~v1_funct_1(A_587) | ~v1_relat_1(A_587))), inference(superposition, [status(thm), theory('equality')], [c_73, c_709])).
% 11.25/4.73  tff(c_12752, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4' | k6_partfun1(k1_relat_1('#skF_4'))!=k6_partfun1('#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!=k2_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10191, c_12749])).
% 11.25/4.73  tff(c_12757, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_64, c_1920, c_4314, c_11912, c_134, c_64, c_11911, c_2015, c_2167, c_12752])).
% 11.25/4.73  tff(c_12760, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_12757])).
% 11.25/4.73  tff(c_13616, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13614, c_12760])).
% 11.25/4.73  tff(c_13625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_979, c_13616])).
% 11.25/4.73  tff(c_13626, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_12757])).
% 11.25/4.73  tff(c_14723, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14716, c_13626])).
% 11.25/4.73  tff(c_14733, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_14723])).
% 11.25/4.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.25/4.73  
% 11.25/4.73  Inference rules
% 11.25/4.73  ----------------------
% 11.25/4.73  #Ref     : 0
% 11.25/4.73  #Sup     : 2806
% 11.25/4.73  #Fact    : 0
% 11.25/4.73  #Define  : 0
% 11.25/4.73  #Split   : 78
% 11.25/4.73  #Chain   : 0
% 11.25/4.73  #Close   : 0
% 11.25/4.73  
% 11.25/4.73  Ordering : KBO
% 11.25/4.73  
% 11.25/4.73  Simplification rules
% 11.25/4.73  ----------------------
% 11.25/4.73  #Subsume      : 443
% 11.25/4.73  #Demod        : 8776
% 11.25/4.73  #Tautology    : 740
% 11.25/4.73  #SimpNegUnit  : 446
% 11.25/4.73  #BackRed      : 108
% 11.25/4.73  
% 11.25/4.73  #Partial instantiations: 0
% 11.25/4.73  #Strategies tried      : 1
% 11.25/4.73  
% 11.25/4.73  Timing (in seconds)
% 11.25/4.73  ----------------------
% 11.25/4.73  Preprocessing        : 0.37
% 11.25/4.73  Parsing              : 0.20
% 11.25/4.73  CNF conversion       : 0.03
% 11.25/4.73  Main loop            : 3.57
% 11.25/4.73  Inferencing          : 0.92
% 11.25/4.73  Reduction            : 1.81
% 11.25/4.73  Demodulation         : 1.47
% 11.25/4.73  BG Simplification    : 0.08
% 11.25/4.73  Subsumption          : 0.59
% 11.25/4.73  Abstraction          : 0.14
% 11.25/4.73  MUC search           : 0.00
% 11.25/4.73  Cooper               : 0.00
% 11.25/4.73  Total                : 4.00
% 11.25/4.73  Index Insertion      : 0.00
% 11.25/4.73  Index Deletion       : 0.00
% 11.25/4.73  Index Matching       : 0.00
% 11.25/4.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
