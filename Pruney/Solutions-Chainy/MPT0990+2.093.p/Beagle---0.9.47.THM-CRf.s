%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:09 EST 2020

% Result     : Theorem 5.70s
% Output     : CNFRefutation 6.08s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 365 expanded)
%              Number of leaves         :   40 ( 151 expanded)
%              Depth                    :   12
%              Number of atoms          :  322 (1669 expanded)
%              Number of equality atoms :  114 ( 574 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_208,negated_conjecture,(
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

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_182,axiom,(
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

tff(f_111,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_121,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_107,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_140,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_123,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_166,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
          & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

tff(c_54,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_118,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_131,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_118])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_647,plain,(
    ! [B_148,C_149,A_150] :
      ( k6_partfun1(B_148) = k5_relat_1(k2_funct_1(C_149),C_149)
      | k1_xboole_0 = B_148
      | ~ v2_funct_1(C_149)
      | k2_relset_1(A_150,B_148,C_149) != B_148
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_150,B_148)))
      | ~ v1_funct_2(C_149,A_150,B_148)
      | ~ v1_funct_1(C_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_653,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_647])).

tff(c_663,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_653])).

tff(c_664,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_663])).

tff(c_684,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_664])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_34,plain,(
    ! [A_24] : m1_subset_1(k6_partfun1(A_24),k1_zfmisc_1(k2_zfmisc_1(A_24,A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_132,plain,(
    ! [A_57,B_58,D_59] :
      ( r2_relset_1(A_57,B_58,D_59,D_59)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_139,plain,(
    ! [A_24] : r2_relset_1(A_24,A_24,k6_partfun1(A_24),k6_partfun1(A_24)) ),
    inference(resolution,[status(thm)],[c_34,c_132])).

tff(c_286,plain,(
    ! [D_91,A_92,B_95,E_96,F_94,C_93] :
      ( k1_partfun1(A_92,B_95,C_93,D_91,E_96,F_94) = k5_relat_1(E_96,F_94)
      | ~ m1_subset_1(F_94,k1_zfmisc_1(k2_zfmisc_1(C_93,D_91)))
      | ~ v1_funct_1(F_94)
      | ~ m1_subset_1(E_96,k1_zfmisc_1(k2_zfmisc_1(A_92,B_95)))
      | ~ v1_funct_1(E_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_292,plain,(
    ! [A_92,B_95,E_96] :
      ( k1_partfun1(A_92,B_95,'#skF_2','#skF_1',E_96,'#skF_4') = k5_relat_1(E_96,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_96,k1_zfmisc_1(k2_zfmisc_1(A_92,B_95)))
      | ~ v1_funct_1(E_96) ) ),
    inference(resolution,[status(thm)],[c_66,c_286])).

tff(c_369,plain,(
    ! [A_108,B_109,E_110] :
      ( k1_partfun1(A_108,B_109,'#skF_2','#skF_1',E_110,'#skF_4') = k5_relat_1(E_110,'#skF_4')
      | ~ m1_subset_1(E_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ v1_funct_1(E_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_292])).

tff(c_375,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_369])).

tff(c_382,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_375])).

tff(c_62,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_188,plain,(
    ! [D_67,C_68,A_69,B_70] :
      ( D_67 = C_68
      | ~ r2_relset_1(A_69,B_70,C_68,D_67)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_196,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_62,c_188])).

tff(c_211,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_196])).

tff(c_212,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_387,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_212])).

tff(c_477,plain,(
    ! [A_116,B_121,D_120,C_117,F_119,E_118] :
      ( m1_subset_1(k1_partfun1(A_116,B_121,C_117,D_120,E_118,F_119),k1_zfmisc_1(k2_zfmisc_1(A_116,D_120)))
      | ~ m1_subset_1(F_119,k1_zfmisc_1(k2_zfmisc_1(C_117,D_120)))
      | ~ v1_funct_1(F_119)
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_121)))
      | ~ v1_funct_1(E_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_510,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_477])).

tff(c_531,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_510])).

tff(c_533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_387,c_531])).

tff(c_534,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_1219,plain,(
    ! [A_178,B_179,C_180,D_181] :
      ( k2_relset_1(A_178,B_179,C_180) = B_179
      | ~ r2_relset_1(B_179,B_179,k1_partfun1(B_179,A_178,A_178,B_179,D_181,C_180),k6_partfun1(B_179))
      | ~ m1_subset_1(D_181,k1_zfmisc_1(k2_zfmisc_1(B_179,A_178)))
      | ~ v1_funct_2(D_181,B_179,A_178)
      | ~ v1_funct_1(D_181)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179)))
      | ~ v1_funct_2(C_180,A_178,B_179)
      | ~ v1_funct_1(C_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_1225,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_1219])).

tff(c_1229,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_76,c_74,c_72,c_139,c_1225])).

tff(c_1231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_684,c_1229])).

tff(c_1232,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_664])).

tff(c_1238,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1232])).

tff(c_38,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_8,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_79,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_8])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_1927,plain,(
    ! [E_216,A_213,D_215,C_217,B_214] :
      ( k1_xboole_0 = C_217
      | v2_funct_1(E_216)
      | k2_relset_1(A_213,B_214,D_215) != B_214
      | ~ v2_funct_1(k1_partfun1(A_213,B_214,B_214,C_217,D_215,E_216))
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1(B_214,C_217)))
      | ~ v1_funct_2(E_216,B_214,C_217)
      | ~ v1_funct_1(E_216)
      | ~ m1_subset_1(D_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214)))
      | ~ v1_funct_2(D_215,A_213,B_214)
      | ~ v1_funct_1(D_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1935,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_534,c_1927])).

tff(c_1946,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_66,c_79,c_64,c_1935])).

tff(c_1948,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1238,c_58,c_1946])).

tff(c_1950,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1232])).

tff(c_4,plain,(
    ! [A_1] : k2_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    ! [A_1] : k2_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4])).

tff(c_1233,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_664])).

tff(c_2005,plain,(
    ! [A_221,C_222,B_223] :
      ( k6_partfun1(A_221) = k5_relat_1(C_222,k2_funct_1(C_222))
      | k1_xboole_0 = B_223
      | ~ v2_funct_1(C_222)
      | k2_relset_1(A_221,B_223,C_222) != B_223
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_221,B_223)))
      | ~ v1_funct_2(C_222,A_221,B_223)
      | ~ v1_funct_1(C_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_2011,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_2005])).

tff(c_2021,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1233,c_1950,c_2011])).

tff(c_2022,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2021])).

tff(c_12,plain,(
    ! [A_6] :
      ( k2_relat_1(k5_relat_1(A_6,k2_funct_1(A_6))) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2065,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2022,c_12])).

tff(c_2077,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_70,c_1950,c_81,c_2065])).

tff(c_601,plain,(
    ! [D_137,A_138,E_142,B_141,F_140,C_139] :
      ( k1_partfun1(A_138,B_141,C_139,D_137,E_142,F_140) = k5_relat_1(E_142,F_140)
      | ~ m1_subset_1(F_140,k1_zfmisc_1(k2_zfmisc_1(C_139,D_137)))
      | ~ v1_funct_1(F_140)
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_138,B_141)))
      | ~ v1_funct_1(E_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_607,plain,(
    ! [A_138,B_141,E_142] :
      ( k1_partfun1(A_138,B_141,'#skF_2','#skF_1',E_142,'#skF_4') = k5_relat_1(E_142,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_138,B_141)))
      | ~ v1_funct_1(E_142) ) ),
    inference(resolution,[status(thm)],[c_66,c_601])).

tff(c_1969,plain,(
    ! [A_218,B_219,E_220] :
      ( k1_partfun1(A_218,B_219,'#skF_2','#skF_1',E_220,'#skF_4') = k5_relat_1(E_220,'#skF_4')
      | ~ m1_subset_1(E_220,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219)))
      | ~ v1_funct_1(E_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_607])).

tff(c_1975,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1969])).

tff(c_1982,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_534,c_1975])).

tff(c_130,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_118])).

tff(c_60,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_2,plain,(
    ! [A_1] : k1_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_82,plain,(
    ! [A_1] : k1_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_651,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_647])).

tff(c_659,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_64,c_60,c_651])).

tff(c_660,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_659])).

tff(c_18,plain,(
    ! [A_7] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(A_7),A_7)) = k2_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_668,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_18])).

tff(c_675,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_76,c_60,c_82,c_668])).

tff(c_2009,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_2005])).

tff(c_2017,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_64,c_60,c_2009])).

tff(c_2018,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2017])).

tff(c_2030,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2018,c_12])).

tff(c_2042,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_76,c_60,c_81,c_2030])).

tff(c_20,plain,(
    ! [A_8,B_10] :
      ( k2_funct_1(A_8) = B_10
      | k6_relat_1(k1_relat_1(A_8)) != k5_relat_1(A_8,B_10)
      | k2_relat_1(A_8) != k1_relat_1(B_10)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_77,plain,(
    ! [A_8,B_10] :
      ( k2_funct_1(A_8) = B_10
      | k6_partfun1(k1_relat_1(A_8)) != k5_relat_1(A_8,B_10)
      | k2_relat_1(A_8) != k1_relat_1(B_10)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_20])).

tff(c_2048,plain,(
    ! [B_10] :
      ( k2_funct_1('#skF_3') = B_10
      | k5_relat_1('#skF_3',B_10) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_10)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2042,c_77])).

tff(c_3057,plain,(
    ! [B_269] :
      ( k2_funct_1('#skF_3') = B_269
      | k5_relat_1('#skF_3',B_269) != k6_partfun1('#skF_1')
      | k1_relat_1(B_269) != '#skF_2'
      | ~ v1_funct_1(B_269)
      | ~ v1_relat_1(B_269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_76,c_60,c_675,c_2048])).

tff(c_3093,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_131,c_3057])).

tff(c_3135,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2077,c_1982,c_3093])).

tff(c_3137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.70/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.70/2.07  
% 5.70/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.70/2.07  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.70/2.07  
% 5.70/2.07  %Foreground sorts:
% 5.70/2.07  
% 5.70/2.07  
% 5.70/2.07  %Background operators:
% 5.70/2.07  
% 5.70/2.07  
% 5.70/2.07  %Foreground operators:
% 5.70/2.07  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.70/2.07  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.70/2.07  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.70/2.07  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.70/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.70/2.07  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.70/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.70/2.07  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.70/2.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.70/2.07  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.70/2.07  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.70/2.07  tff('#skF_2', type, '#skF_2': $i).
% 5.70/2.07  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.70/2.07  tff('#skF_3', type, '#skF_3': $i).
% 5.70/2.07  tff('#skF_1', type, '#skF_1': $i).
% 5.70/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.70/2.07  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.70/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.70/2.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.70/2.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.70/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.70/2.07  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.70/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.70/2.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.70/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.70/2.07  
% 6.08/2.09  tff(f_208, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 6.08/2.09  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.08/2.09  tff(f_182, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 6.08/2.09  tff(f_111, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.08/2.09  tff(f_95, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.08/2.09  tff(f_121, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.08/2.09  tff(f_107, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.08/2.09  tff(f_140, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 6.08/2.09  tff(f_123, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.08/2.09  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.08/2.09  tff(f_166, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 6.08/2.09  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 6.08/2.09  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 6.08/2.09  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 6.08/2.09  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 6.08/2.09  tff(c_54, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.08/2.09  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.08/2.09  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.08/2.09  tff(c_118, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.08/2.09  tff(c_131, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_118])).
% 6.08/2.09  tff(c_58, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.08/2.09  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.08/2.09  tff(c_647, plain, (![B_148, C_149, A_150]: (k6_partfun1(B_148)=k5_relat_1(k2_funct_1(C_149), C_149) | k1_xboole_0=B_148 | ~v2_funct_1(C_149) | k2_relset_1(A_150, B_148, C_149)!=B_148 | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_150, B_148))) | ~v1_funct_2(C_149, A_150, B_148) | ~v1_funct_1(C_149))), inference(cnfTransformation, [status(thm)], [f_182])).
% 6.08/2.09  tff(c_653, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_647])).
% 6.08/2.09  tff(c_663, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_653])).
% 6.08/2.09  tff(c_664, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_58, c_663])).
% 6.08/2.09  tff(c_684, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_664])).
% 6.08/2.09  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.08/2.09  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.08/2.09  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.08/2.09  tff(c_34, plain, (![A_24]: (m1_subset_1(k6_partfun1(A_24), k1_zfmisc_1(k2_zfmisc_1(A_24, A_24))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.08/2.09  tff(c_132, plain, (![A_57, B_58, D_59]: (r2_relset_1(A_57, B_58, D_59, D_59) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.08/2.09  tff(c_139, plain, (![A_24]: (r2_relset_1(A_24, A_24, k6_partfun1(A_24), k6_partfun1(A_24)))), inference(resolution, [status(thm)], [c_34, c_132])).
% 6.08/2.09  tff(c_286, plain, (![D_91, A_92, B_95, E_96, F_94, C_93]: (k1_partfun1(A_92, B_95, C_93, D_91, E_96, F_94)=k5_relat_1(E_96, F_94) | ~m1_subset_1(F_94, k1_zfmisc_1(k2_zfmisc_1(C_93, D_91))) | ~v1_funct_1(F_94) | ~m1_subset_1(E_96, k1_zfmisc_1(k2_zfmisc_1(A_92, B_95))) | ~v1_funct_1(E_96))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.08/2.09  tff(c_292, plain, (![A_92, B_95, E_96]: (k1_partfun1(A_92, B_95, '#skF_2', '#skF_1', E_96, '#skF_4')=k5_relat_1(E_96, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_96, k1_zfmisc_1(k2_zfmisc_1(A_92, B_95))) | ~v1_funct_1(E_96))), inference(resolution, [status(thm)], [c_66, c_286])).
% 6.08/2.09  tff(c_369, plain, (![A_108, B_109, E_110]: (k1_partfun1(A_108, B_109, '#skF_2', '#skF_1', E_110, '#skF_4')=k5_relat_1(E_110, '#skF_4') | ~m1_subset_1(E_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~v1_funct_1(E_110))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_292])).
% 6.08/2.09  tff(c_375, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_369])).
% 6.08/2.09  tff(c_382, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_375])).
% 6.08/2.09  tff(c_62, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.08/2.09  tff(c_188, plain, (![D_67, C_68, A_69, B_70]: (D_67=C_68 | ~r2_relset_1(A_69, B_70, C_68, D_67) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.08/2.09  tff(c_196, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_62, c_188])).
% 6.08/2.09  tff(c_211, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_196])).
% 6.08/2.09  tff(c_212, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_211])).
% 6.08/2.09  tff(c_387, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_382, c_212])).
% 6.08/2.09  tff(c_477, plain, (![A_116, B_121, D_120, C_117, F_119, E_118]: (m1_subset_1(k1_partfun1(A_116, B_121, C_117, D_120, E_118, F_119), k1_zfmisc_1(k2_zfmisc_1(A_116, D_120))) | ~m1_subset_1(F_119, k1_zfmisc_1(k2_zfmisc_1(C_117, D_120))) | ~v1_funct_1(F_119) | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_121))) | ~v1_funct_1(E_118))), inference(cnfTransformation, [status(thm)], [f_107])).
% 6.08/2.09  tff(c_510, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_382, c_477])).
% 6.08/2.09  tff(c_531, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_510])).
% 6.08/2.09  tff(c_533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_387, c_531])).
% 6.08/2.09  tff(c_534, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_211])).
% 6.08/2.09  tff(c_1219, plain, (![A_178, B_179, C_180, D_181]: (k2_relset_1(A_178, B_179, C_180)=B_179 | ~r2_relset_1(B_179, B_179, k1_partfun1(B_179, A_178, A_178, B_179, D_181, C_180), k6_partfun1(B_179)) | ~m1_subset_1(D_181, k1_zfmisc_1(k2_zfmisc_1(B_179, A_178))) | ~v1_funct_2(D_181, B_179, A_178) | ~v1_funct_1(D_181) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))) | ~v1_funct_2(C_180, A_178, B_179) | ~v1_funct_1(C_180))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.08/2.09  tff(c_1225, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_534, c_1219])).
% 6.08/2.09  tff(c_1229, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_76, c_74, c_72, c_139, c_1225])).
% 6.08/2.09  tff(c_1231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_684, c_1229])).
% 6.08/2.09  tff(c_1232, plain, (~v2_funct_1('#skF_4') | k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_664])).
% 6.08/2.09  tff(c_1238, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1232])).
% 6.08/2.09  tff(c_38, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.08/2.09  tff(c_8, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.08/2.09  tff(c_79, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_8])).
% 6.08/2.09  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.08/2.09  tff(c_1927, plain, (![E_216, A_213, D_215, C_217, B_214]: (k1_xboole_0=C_217 | v2_funct_1(E_216) | k2_relset_1(A_213, B_214, D_215)!=B_214 | ~v2_funct_1(k1_partfun1(A_213, B_214, B_214, C_217, D_215, E_216)) | ~m1_subset_1(E_216, k1_zfmisc_1(k2_zfmisc_1(B_214, C_217))) | ~v1_funct_2(E_216, B_214, C_217) | ~v1_funct_1(E_216) | ~m1_subset_1(D_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))) | ~v1_funct_2(D_215, A_213, B_214) | ~v1_funct_1(D_215))), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.08/2.09  tff(c_1935, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_534, c_1927])).
% 6.08/2.09  tff(c_1946, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_66, c_79, c_64, c_1935])).
% 6.08/2.09  tff(c_1948, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1238, c_58, c_1946])).
% 6.08/2.09  tff(c_1950, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1232])).
% 6.08/2.09  tff(c_4, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.08/2.09  tff(c_81, plain, (![A_1]: (k2_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4])).
% 6.08/2.09  tff(c_1233, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_664])).
% 6.08/2.09  tff(c_2005, plain, (![A_221, C_222, B_223]: (k6_partfun1(A_221)=k5_relat_1(C_222, k2_funct_1(C_222)) | k1_xboole_0=B_223 | ~v2_funct_1(C_222) | k2_relset_1(A_221, B_223, C_222)!=B_223 | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_221, B_223))) | ~v1_funct_2(C_222, A_221, B_223) | ~v1_funct_1(C_222))), inference(cnfTransformation, [status(thm)], [f_182])).
% 6.08/2.09  tff(c_2011, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_2005])).
% 6.08/2.09  tff(c_2021, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1233, c_1950, c_2011])).
% 6.08/2.09  tff(c_2022, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_58, c_2021])).
% 6.08/2.09  tff(c_12, plain, (![A_6]: (k2_relat_1(k5_relat_1(A_6, k2_funct_1(A_6)))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.08/2.09  tff(c_2065, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2022, c_12])).
% 6.08/2.09  tff(c_2077, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_70, c_1950, c_81, c_2065])).
% 6.08/2.09  tff(c_601, plain, (![D_137, A_138, E_142, B_141, F_140, C_139]: (k1_partfun1(A_138, B_141, C_139, D_137, E_142, F_140)=k5_relat_1(E_142, F_140) | ~m1_subset_1(F_140, k1_zfmisc_1(k2_zfmisc_1(C_139, D_137))) | ~v1_funct_1(F_140) | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_138, B_141))) | ~v1_funct_1(E_142))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.08/2.09  tff(c_607, plain, (![A_138, B_141, E_142]: (k1_partfun1(A_138, B_141, '#skF_2', '#skF_1', E_142, '#skF_4')=k5_relat_1(E_142, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_138, B_141))) | ~v1_funct_1(E_142))), inference(resolution, [status(thm)], [c_66, c_601])).
% 6.08/2.09  tff(c_1969, plain, (![A_218, B_219, E_220]: (k1_partfun1(A_218, B_219, '#skF_2', '#skF_1', E_220, '#skF_4')=k5_relat_1(E_220, '#skF_4') | ~m1_subset_1(E_220, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))) | ~v1_funct_1(E_220))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_607])).
% 6.08/2.09  tff(c_1975, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1969])).
% 6.08/2.09  tff(c_1982, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_534, c_1975])).
% 6.08/2.09  tff(c_130, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_118])).
% 6.08/2.09  tff(c_60, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.08/2.09  tff(c_2, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.08/2.09  tff(c_82, plain, (![A_1]: (k1_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2])).
% 6.08/2.09  tff(c_56, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_208])).
% 6.08/2.09  tff(c_651, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_647])).
% 6.08/2.09  tff(c_659, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_64, c_60, c_651])).
% 6.08/2.09  tff(c_660, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_659])).
% 6.08/2.09  tff(c_18, plain, (![A_7]: (k1_relat_1(k5_relat_1(k2_funct_1(A_7), A_7))=k2_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.08/2.09  tff(c_668, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_660, c_18])).
% 6.08/2.09  tff(c_675, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_76, c_60, c_82, c_668])).
% 6.08/2.09  tff(c_2009, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_2005])).
% 6.08/2.09  tff(c_2017, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_64, c_60, c_2009])).
% 6.08/2.09  tff(c_2018, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_56, c_2017])).
% 6.08/2.09  tff(c_2030, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2018, c_12])).
% 6.08/2.09  tff(c_2042, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_76, c_60, c_81, c_2030])).
% 6.08/2.09  tff(c_20, plain, (![A_8, B_10]: (k2_funct_1(A_8)=B_10 | k6_relat_1(k1_relat_1(A_8))!=k5_relat_1(A_8, B_10) | k2_relat_1(A_8)!=k1_relat_1(B_10) | ~v2_funct_1(A_8) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.08/2.09  tff(c_77, plain, (![A_8, B_10]: (k2_funct_1(A_8)=B_10 | k6_partfun1(k1_relat_1(A_8))!=k5_relat_1(A_8, B_10) | k2_relat_1(A_8)!=k1_relat_1(B_10) | ~v2_funct_1(A_8) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_20])).
% 6.08/2.09  tff(c_2048, plain, (![B_10]: (k2_funct_1('#skF_3')=B_10 | k5_relat_1('#skF_3', B_10)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_10) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2042, c_77])).
% 6.08/2.09  tff(c_3057, plain, (![B_269]: (k2_funct_1('#skF_3')=B_269 | k5_relat_1('#skF_3', B_269)!=k6_partfun1('#skF_1') | k1_relat_1(B_269)!='#skF_2' | ~v1_funct_1(B_269) | ~v1_relat_1(B_269))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_76, c_60, c_675, c_2048])).
% 6.08/2.09  tff(c_3093, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_131, c_3057])).
% 6.08/2.09  tff(c_3135, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2077, c_1982, c_3093])).
% 6.08/2.09  tff(c_3137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_3135])).
% 6.08/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.08/2.09  
% 6.08/2.09  Inference rules
% 6.08/2.09  ----------------------
% 6.08/2.09  #Ref     : 0
% 6.08/2.09  #Sup     : 637
% 6.08/2.09  #Fact    : 0
% 6.08/2.09  #Define  : 0
% 6.08/2.09  #Split   : 17
% 6.08/2.09  #Chain   : 0
% 6.08/2.09  #Close   : 0
% 6.08/2.09  
% 6.08/2.09  Ordering : KBO
% 6.08/2.09  
% 6.08/2.09  Simplification rules
% 6.08/2.09  ----------------------
% 6.08/2.09  #Subsume      : 24
% 6.08/2.09  #Demod        : 853
% 6.08/2.09  #Tautology    : 174
% 6.08/2.09  #SimpNegUnit  : 87
% 6.08/2.09  #BackRed      : 20
% 6.08/2.09  
% 6.08/2.09  #Partial instantiations: 0
% 6.08/2.09  #Strategies tried      : 1
% 6.08/2.09  
% 6.08/2.09  Timing (in seconds)
% 6.08/2.09  ----------------------
% 6.08/2.10  Preprocessing        : 0.38
% 6.08/2.10  Parsing              : 0.20
% 6.08/2.10  CNF conversion       : 0.03
% 6.08/2.10  Main loop            : 0.95
% 6.08/2.10  Inferencing          : 0.32
% 6.08/2.10  Reduction            : 0.36
% 6.08/2.10  Demodulation         : 0.26
% 6.08/2.10  BG Simplification    : 0.04
% 6.08/2.10  Subsumption          : 0.17
% 6.08/2.10  Abstraction          : 0.05
% 6.08/2.10  MUC search           : 0.00
% 6.08/2.10  Cooper               : 0.00
% 6.08/2.10  Total                : 1.37
% 6.08/2.10  Index Insertion      : 0.00
% 6.08/2.10  Index Deletion       : 0.00
% 6.08/2.10  Index Matching       : 0.00
% 6.08/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
