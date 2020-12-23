%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:10 EST 2020

% Result     : Theorem 6.19s
% Output     : CNFRefutation 6.36s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 397 expanded)
%              Number of leaves         :   38 ( 160 expanded)
%              Depth                    :   14
%              Number of atoms          :  327 (1707 expanded)
%              Number of equality atoms :  116 ( 603 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_196,negated_conjecture,(
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

tff(f_111,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_170,axiom,(
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

tff(f_87,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_99,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_128,axiom,(
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

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_154,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_73,axiom,(
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

tff(c_48,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_32,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2,plain,(
    ! [A_1] : k1_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_79,plain,(
    ! [A_1] : k1_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_114,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_127,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_114])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_645,plain,(
    ! [B_132,C_133,A_134] :
      ( k6_partfun1(B_132) = k5_relat_1(k2_funct_1(C_133),C_133)
      | k1_xboole_0 = B_132
      | ~ v2_funct_1(C_133)
      | k2_relset_1(A_134,B_132,C_133) != B_132
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_134,B_132)))
      | ~ v1_funct_2(C_133,A_134,B_132)
      | ~ v1_funct_1(C_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_651,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_645])).

tff(c_661,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_651])).

tff(c_662,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_661])).

tff(c_722,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_662])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_24,plain,(
    ! [A_17] : m1_subset_1(k6_relat_1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_71,plain,(
    ! [A_17] : m1_subset_1(k6_partfun1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_24])).

tff(c_128,plain,(
    ! [A_55,B_56,D_57] :
      ( r2_relset_1(A_55,B_56,D_57,D_57)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_135,plain,(
    ! [A_17] : r2_relset_1(A_17,A_17,k6_partfun1(A_17),k6_partfun1(A_17)) ),
    inference(resolution,[status(thm)],[c_71,c_128])).

tff(c_242,plain,(
    ! [D_85,C_80,B_81,E_82,A_84,F_83] :
      ( k1_partfun1(A_84,B_81,C_80,D_85,E_82,F_83) = k5_relat_1(E_82,F_83)
      | ~ m1_subset_1(F_83,k1_zfmisc_1(k2_zfmisc_1(C_80,D_85)))
      | ~ v1_funct_1(F_83)
      | ~ m1_subset_1(E_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_81)))
      | ~ v1_funct_1(E_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_248,plain,(
    ! [A_84,B_81,E_82] :
      ( k1_partfun1(A_84,B_81,'#skF_2','#skF_1',E_82,'#skF_4') = k5_relat_1(E_82,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_81)))
      | ~ v1_funct_1(E_82) ) ),
    inference(resolution,[status(thm)],[c_60,c_242])).

tff(c_275,plain,(
    ! [A_91,B_92,E_93] :
      ( k1_partfun1(A_91,B_92,'#skF_2','#skF_1',E_93,'#skF_4') = k5_relat_1(E_93,'#skF_4')
      | ~ m1_subset_1(E_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ v1_funct_1(E_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_248])).

tff(c_281,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_275])).

tff(c_288,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_281])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_167,plain,(
    ! [D_63,C_64,A_65,B_66] :
      ( D_63 = C_64
      | ~ r2_relset_1(A_65,B_66,C_64,D_63)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_175,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_167])).

tff(c_190,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_175])).

tff(c_191,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_293,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_191])).

tff(c_491,plain,(
    ! [D_104,C_101,B_105,A_100,F_103,E_102] :
      ( m1_subset_1(k1_partfun1(A_100,B_105,C_101,D_104,E_102,F_103),k1_zfmisc_1(k2_zfmisc_1(A_100,D_104)))
      | ~ m1_subset_1(F_103,k1_zfmisc_1(k2_zfmisc_1(C_101,D_104)))
      | ~ v1_funct_1(F_103)
      | ~ m1_subset_1(E_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_105)))
      | ~ v1_funct_1(E_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_516,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_491])).

tff(c_527,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_516])).

tff(c_529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_293,c_527])).

tff(c_530,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_1104,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( k2_relset_1(A_155,B_156,C_157) = B_156
      | ~ r2_relset_1(B_156,B_156,k1_partfun1(B_156,A_155,A_155,B_156,D_158,C_157),k6_partfun1(B_156))
      | ~ m1_subset_1(D_158,k1_zfmisc_1(k2_zfmisc_1(B_156,A_155)))
      | ~ v1_funct_2(D_158,B_156,A_155)
      | ~ v1_funct_1(D_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156)))
      | ~ v1_funct_2(C_157,A_155,B_156)
      | ~ v1_funct_1(C_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1110,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_530,c_1104])).

tff(c_1114,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_135,c_1110])).

tff(c_1116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_722,c_1114])).

tff(c_1117,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_662])).

tff(c_1125,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1117])).

tff(c_8,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_76,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_1677,plain,(
    ! [B_191,A_188,E_189,D_190,C_192] :
      ( k1_xboole_0 = C_192
      | v2_funct_1(E_189)
      | k2_relset_1(A_188,B_191,D_190) != B_191
      | ~ v2_funct_1(k1_partfun1(A_188,B_191,B_191,C_192,D_190,E_189))
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(B_191,C_192)))
      | ~ v1_funct_2(E_189,B_191,C_192)
      | ~ v1_funct_1(E_189)
      | ~ m1_subset_1(D_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_191)))
      | ~ v1_funct_2(D_190,A_188,B_191)
      | ~ v1_funct_1(D_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1683,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_530,c_1677])).

tff(c_1691,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_76,c_58,c_1683])).

tff(c_1693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1125,c_52,c_1691])).

tff(c_1695,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1117])).

tff(c_1118,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_662])).

tff(c_1782,plain,(
    ! [A_196,C_197,B_198] :
      ( k6_partfun1(A_196) = k5_relat_1(C_197,k2_funct_1(C_197))
      | k1_xboole_0 = B_198
      | ~ v2_funct_1(C_197)
      | k2_relset_1(A_196,B_198,C_197) != B_198
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_196,B_198)))
      | ~ v1_funct_2(C_197,A_196,B_198)
      | ~ v1_funct_1(C_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1788,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1782])).

tff(c_1798,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1118,c_1695,c_1788])).

tff(c_1799,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1798])).

tff(c_14,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_relat_1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_73,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_partfun1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_14])).

tff(c_1894,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1799,c_73])).

tff(c_1906,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_64,c_1695,c_1894])).

tff(c_1936,plain,(
    k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1906,c_79])).

tff(c_1955,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_1936])).

tff(c_599,plain,(
    ! [C_121,B_122,F_124,D_126,E_123,A_125] :
      ( k1_partfun1(A_125,B_122,C_121,D_126,E_123,F_124) = k5_relat_1(E_123,F_124)
      | ~ m1_subset_1(F_124,k1_zfmisc_1(k2_zfmisc_1(C_121,D_126)))
      | ~ v1_funct_1(F_124)
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_122)))
      | ~ v1_funct_1(E_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_605,plain,(
    ! [A_125,B_122,E_123] :
      ( k1_partfun1(A_125,B_122,'#skF_2','#skF_1',E_123,'#skF_4') = k5_relat_1(E_123,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_122)))
      | ~ v1_funct_1(E_123) ) ),
    inference(resolution,[status(thm)],[c_60,c_599])).

tff(c_1753,plain,(
    ! [A_193,B_194,E_195] :
      ( k1_partfun1(A_193,B_194,'#skF_2','#skF_1',E_195,'#skF_4') = k5_relat_1(E_195,'#skF_4')
      | ~ m1_subset_1(E_195,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194)))
      | ~ v1_funct_1(E_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_605])).

tff(c_1759,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1753])).

tff(c_1766,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_530,c_1759])).

tff(c_126,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_114])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_649,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_645])).

tff(c_657,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_54,c_649])).

tff(c_658,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_657])).

tff(c_12,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_relat_1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_74,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_partfun1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12])).

tff(c_666,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_658,c_74])).

tff(c_673,plain,(
    k6_partfun1(k2_relat_1('#skF_3')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_70,c_54,c_666])).

tff(c_697,plain,(
    k1_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_673,c_79])).

tff(c_712,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_697])).

tff(c_1786,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1782])).

tff(c_1794,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_54,c_1786])).

tff(c_1795,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1794])).

tff(c_1807,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1795,c_73])).

tff(c_1819,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_70,c_54,c_1807])).

tff(c_16,plain,(
    ! [A_7,B_9] :
      ( k2_funct_1(A_7) = B_9
      | k6_relat_1(k1_relat_1(A_7)) != k5_relat_1(A_7,B_9)
      | k2_relat_1(A_7) != k1_relat_1(B_9)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_72,plain,(
    ! [A_7,B_9] :
      ( k2_funct_1(A_7) = B_9
      | k6_partfun1(k1_relat_1(A_7)) != k5_relat_1(A_7,B_9)
      | k2_relat_1(A_7) != k1_relat_1(B_9)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_16])).

tff(c_1833,plain,(
    ! [B_9] :
      ( k2_funct_1('#skF_3') = B_9
      | k5_relat_1('#skF_3',B_9) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_9)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1819,c_72])).

tff(c_3274,plain,(
    ! [B_260] :
      ( k2_funct_1('#skF_3') = B_260
      | k5_relat_1('#skF_3',B_260) != k6_partfun1('#skF_1')
      | k1_relat_1(B_260) != '#skF_2'
      | ~ v1_funct_1(B_260)
      | ~ v1_relat_1(B_260) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_70,c_54,c_712,c_1833])).

tff(c_3310,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_127,c_3274])).

tff(c_3352,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1955,c_1766,c_3310])).

tff(c_3354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_3352])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.19/2.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.19/2.14  
% 6.19/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.19/2.15  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.19/2.15  
% 6.19/2.15  %Foreground sorts:
% 6.19/2.15  
% 6.19/2.15  
% 6.19/2.15  %Background operators:
% 6.19/2.15  
% 6.19/2.15  
% 6.19/2.15  %Foreground operators:
% 6.19/2.15  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.19/2.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.19/2.15  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.19/2.15  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.19/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.19/2.15  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.19/2.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.19/2.15  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.19/2.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.19/2.15  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.19/2.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.19/2.15  tff('#skF_2', type, '#skF_2': $i).
% 6.19/2.15  tff('#skF_3', type, '#skF_3': $i).
% 6.19/2.15  tff('#skF_1', type, '#skF_1': $i).
% 6.19/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.19/2.15  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.19/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.19/2.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.19/2.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.19/2.15  tff('#skF_4', type, '#skF_4': $i).
% 6.19/2.15  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.19/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.19/2.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.19/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.19/2.15  
% 6.36/2.17  tff(f_196, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 6.36/2.17  tff(f_111, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.36/2.17  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 6.36/2.17  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.36/2.17  tff(f_170, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 6.36/2.17  tff(f_87, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 6.36/2.17  tff(f_85, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.36/2.17  tff(f_109, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.36/2.17  tff(f_99, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.36/2.17  tff(f_128, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 6.36/2.17  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.36/2.17  tff(f_154, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 6.36/2.17  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 6.36/2.17  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 6.36/2.17  tff(c_48, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_196])).
% 6.36/2.17  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_196])).
% 6.36/2.17  tff(c_32, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.36/2.17  tff(c_2, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.36/2.17  tff(c_79, plain, (![A_1]: (k1_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2])).
% 6.36/2.17  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_196])).
% 6.36/2.17  tff(c_114, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.36/2.17  tff(c_127, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_114])).
% 6.36/2.17  tff(c_52, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_196])).
% 6.36/2.17  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_196])).
% 6.36/2.17  tff(c_645, plain, (![B_132, C_133, A_134]: (k6_partfun1(B_132)=k5_relat_1(k2_funct_1(C_133), C_133) | k1_xboole_0=B_132 | ~v2_funct_1(C_133) | k2_relset_1(A_134, B_132, C_133)!=B_132 | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_134, B_132))) | ~v1_funct_2(C_133, A_134, B_132) | ~v1_funct_1(C_133))), inference(cnfTransformation, [status(thm)], [f_170])).
% 6.36/2.17  tff(c_651, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_645])).
% 6.36/2.17  tff(c_661, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_651])).
% 6.36/2.17  tff(c_662, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_52, c_661])).
% 6.36/2.17  tff(c_722, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_662])).
% 6.36/2.17  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 6.36/2.17  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 6.36/2.17  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_196])).
% 6.36/2.17  tff(c_24, plain, (![A_17]: (m1_subset_1(k6_relat_1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.36/2.17  tff(c_71, plain, (![A_17]: (m1_subset_1(k6_partfun1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_24])).
% 6.36/2.17  tff(c_128, plain, (![A_55, B_56, D_57]: (r2_relset_1(A_55, B_56, D_57, D_57) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.36/2.17  tff(c_135, plain, (![A_17]: (r2_relset_1(A_17, A_17, k6_partfun1(A_17), k6_partfun1(A_17)))), inference(resolution, [status(thm)], [c_71, c_128])).
% 6.36/2.17  tff(c_242, plain, (![D_85, C_80, B_81, E_82, A_84, F_83]: (k1_partfun1(A_84, B_81, C_80, D_85, E_82, F_83)=k5_relat_1(E_82, F_83) | ~m1_subset_1(F_83, k1_zfmisc_1(k2_zfmisc_1(C_80, D_85))) | ~v1_funct_1(F_83) | ~m1_subset_1(E_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_81))) | ~v1_funct_1(E_82))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.36/2.17  tff(c_248, plain, (![A_84, B_81, E_82]: (k1_partfun1(A_84, B_81, '#skF_2', '#skF_1', E_82, '#skF_4')=k5_relat_1(E_82, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_81))) | ~v1_funct_1(E_82))), inference(resolution, [status(thm)], [c_60, c_242])).
% 6.36/2.17  tff(c_275, plain, (![A_91, B_92, E_93]: (k1_partfun1(A_91, B_92, '#skF_2', '#skF_1', E_93, '#skF_4')=k5_relat_1(E_93, '#skF_4') | ~m1_subset_1(E_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~v1_funct_1(E_93))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_248])).
% 6.36/2.17  tff(c_281, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_275])).
% 6.36/2.17  tff(c_288, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_281])).
% 6.36/2.17  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 6.36/2.17  tff(c_167, plain, (![D_63, C_64, A_65, B_66]: (D_63=C_64 | ~r2_relset_1(A_65, B_66, C_64, D_63) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.36/2.17  tff(c_175, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_167])).
% 6.36/2.17  tff(c_190, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_175])).
% 6.36/2.17  tff(c_191, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_190])).
% 6.36/2.17  tff(c_293, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_288, c_191])).
% 6.36/2.17  tff(c_491, plain, (![D_104, C_101, B_105, A_100, F_103, E_102]: (m1_subset_1(k1_partfun1(A_100, B_105, C_101, D_104, E_102, F_103), k1_zfmisc_1(k2_zfmisc_1(A_100, D_104))) | ~m1_subset_1(F_103, k1_zfmisc_1(k2_zfmisc_1(C_101, D_104))) | ~v1_funct_1(F_103) | ~m1_subset_1(E_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_105))) | ~v1_funct_1(E_102))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.36/2.17  tff(c_516, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_288, c_491])).
% 6.36/2.17  tff(c_527, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_516])).
% 6.36/2.17  tff(c_529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_293, c_527])).
% 6.36/2.17  tff(c_530, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_190])).
% 6.36/2.17  tff(c_1104, plain, (![A_155, B_156, C_157, D_158]: (k2_relset_1(A_155, B_156, C_157)=B_156 | ~r2_relset_1(B_156, B_156, k1_partfun1(B_156, A_155, A_155, B_156, D_158, C_157), k6_partfun1(B_156)) | ~m1_subset_1(D_158, k1_zfmisc_1(k2_zfmisc_1(B_156, A_155))) | ~v1_funct_2(D_158, B_156, A_155) | ~v1_funct_1(D_158) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))) | ~v1_funct_2(C_157, A_155, B_156) | ~v1_funct_1(C_157))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.36/2.17  tff(c_1110, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_530, c_1104])).
% 6.36/2.17  tff(c_1114, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_135, c_1110])).
% 6.36/2.17  tff(c_1116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_722, c_1114])).
% 6.36/2.17  tff(c_1117, plain, (~v2_funct_1('#skF_4') | k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_662])).
% 6.36/2.17  tff(c_1125, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1117])).
% 6.36/2.17  tff(c_8, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.36/2.17  tff(c_76, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8])).
% 6.36/2.17  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_196])).
% 6.36/2.17  tff(c_1677, plain, (![B_191, A_188, E_189, D_190, C_192]: (k1_xboole_0=C_192 | v2_funct_1(E_189) | k2_relset_1(A_188, B_191, D_190)!=B_191 | ~v2_funct_1(k1_partfun1(A_188, B_191, B_191, C_192, D_190, E_189)) | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(B_191, C_192))) | ~v1_funct_2(E_189, B_191, C_192) | ~v1_funct_1(E_189) | ~m1_subset_1(D_190, k1_zfmisc_1(k2_zfmisc_1(A_188, B_191))) | ~v1_funct_2(D_190, A_188, B_191) | ~v1_funct_1(D_190))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.36/2.17  tff(c_1683, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_530, c_1677])).
% 6.36/2.17  tff(c_1691, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_60, c_76, c_58, c_1683])).
% 6.36/2.17  tff(c_1693, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1125, c_52, c_1691])).
% 6.36/2.17  tff(c_1695, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1117])).
% 6.36/2.17  tff(c_1118, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_662])).
% 6.36/2.17  tff(c_1782, plain, (![A_196, C_197, B_198]: (k6_partfun1(A_196)=k5_relat_1(C_197, k2_funct_1(C_197)) | k1_xboole_0=B_198 | ~v2_funct_1(C_197) | k2_relset_1(A_196, B_198, C_197)!=B_198 | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_196, B_198))) | ~v1_funct_2(C_197, A_196, B_198) | ~v1_funct_1(C_197))), inference(cnfTransformation, [status(thm)], [f_170])).
% 6.36/2.17  tff(c_1788, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_1782])).
% 6.36/2.17  tff(c_1798, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1118, c_1695, c_1788])).
% 6.36/2.17  tff(c_1799, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_52, c_1798])).
% 6.36/2.17  tff(c_14, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_relat_1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.36/2.17  tff(c_73, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_partfun1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_14])).
% 6.36/2.17  tff(c_1894, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1799, c_73])).
% 6.36/2.17  tff(c_1906, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_64, c_1695, c_1894])).
% 6.36/2.17  tff(c_1936, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1906, c_79])).
% 6.36/2.17  tff(c_1955, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_1936])).
% 6.36/2.17  tff(c_599, plain, (![C_121, B_122, F_124, D_126, E_123, A_125]: (k1_partfun1(A_125, B_122, C_121, D_126, E_123, F_124)=k5_relat_1(E_123, F_124) | ~m1_subset_1(F_124, k1_zfmisc_1(k2_zfmisc_1(C_121, D_126))) | ~v1_funct_1(F_124) | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_125, B_122))) | ~v1_funct_1(E_123))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.36/2.17  tff(c_605, plain, (![A_125, B_122, E_123]: (k1_partfun1(A_125, B_122, '#skF_2', '#skF_1', E_123, '#skF_4')=k5_relat_1(E_123, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_123, k1_zfmisc_1(k2_zfmisc_1(A_125, B_122))) | ~v1_funct_1(E_123))), inference(resolution, [status(thm)], [c_60, c_599])).
% 6.36/2.17  tff(c_1753, plain, (![A_193, B_194, E_195]: (k1_partfun1(A_193, B_194, '#skF_2', '#skF_1', E_195, '#skF_4')=k5_relat_1(E_195, '#skF_4') | ~m1_subset_1(E_195, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))) | ~v1_funct_1(E_195))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_605])).
% 6.36/2.17  tff(c_1759, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1753])).
% 6.36/2.17  tff(c_1766, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_530, c_1759])).
% 6.36/2.17  tff(c_126, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_114])).
% 6.36/2.17  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 6.36/2.17  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_196])).
% 6.36/2.17  tff(c_649, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_645])).
% 6.36/2.17  tff(c_657, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_54, c_649])).
% 6.36/2.17  tff(c_658, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_657])).
% 6.36/2.17  tff(c_12, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_relat_1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.36/2.17  tff(c_74, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_partfun1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12])).
% 6.36/2.17  tff(c_666, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_658, c_74])).
% 6.36/2.17  tff(c_673, plain, (k6_partfun1(k2_relat_1('#skF_3'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_70, c_54, c_666])).
% 6.36/2.17  tff(c_697, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_673, c_79])).
% 6.36/2.17  tff(c_712, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_697])).
% 6.36/2.17  tff(c_1786, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1782])).
% 6.36/2.17  tff(c_1794, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_54, c_1786])).
% 6.36/2.17  tff(c_1795, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_1794])).
% 6.36/2.17  tff(c_1807, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1795, c_73])).
% 6.36/2.17  tff(c_1819, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_70, c_54, c_1807])).
% 6.36/2.17  tff(c_16, plain, (![A_7, B_9]: (k2_funct_1(A_7)=B_9 | k6_relat_1(k1_relat_1(A_7))!=k5_relat_1(A_7, B_9) | k2_relat_1(A_7)!=k1_relat_1(B_9) | ~v2_funct_1(A_7) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.36/2.17  tff(c_72, plain, (![A_7, B_9]: (k2_funct_1(A_7)=B_9 | k6_partfun1(k1_relat_1(A_7))!=k5_relat_1(A_7, B_9) | k2_relat_1(A_7)!=k1_relat_1(B_9) | ~v2_funct_1(A_7) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_16])).
% 6.36/2.17  tff(c_1833, plain, (![B_9]: (k2_funct_1('#skF_3')=B_9 | k5_relat_1('#skF_3', B_9)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_9) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1819, c_72])).
% 6.36/2.17  tff(c_3274, plain, (![B_260]: (k2_funct_1('#skF_3')=B_260 | k5_relat_1('#skF_3', B_260)!=k6_partfun1('#skF_1') | k1_relat_1(B_260)!='#skF_2' | ~v1_funct_1(B_260) | ~v1_relat_1(B_260))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_70, c_54, c_712, c_1833])).
% 6.36/2.17  tff(c_3310, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_127, c_3274])).
% 6.36/2.17  tff(c_3352, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1955, c_1766, c_3310])).
% 6.36/2.17  tff(c_3354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_3352])).
% 6.36/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.36/2.17  
% 6.36/2.17  Inference rules
% 6.36/2.17  ----------------------
% 6.36/2.17  #Ref     : 0
% 6.36/2.17  #Sup     : 693
% 6.36/2.17  #Fact    : 0
% 6.36/2.17  #Define  : 0
% 6.36/2.17  #Split   : 21
% 6.36/2.17  #Chain   : 0
% 6.36/2.17  #Close   : 0
% 6.36/2.17  
% 6.36/2.17  Ordering : KBO
% 6.36/2.17  
% 6.36/2.17  Simplification rules
% 6.36/2.17  ----------------------
% 6.36/2.17  #Subsume      : 25
% 6.36/2.17  #Demod        : 1170
% 6.36/2.17  #Tautology    : 272
% 6.36/2.17  #SimpNegUnit  : 71
% 6.36/2.17  #BackRed      : 18
% 6.36/2.17  
% 6.36/2.17  #Partial instantiations: 0
% 6.36/2.17  #Strategies tried      : 1
% 6.36/2.17  
% 6.36/2.17  Timing (in seconds)
% 6.36/2.17  ----------------------
% 6.36/2.17  Preprocessing        : 0.39
% 6.36/2.17  Parsing              : 0.21
% 6.36/2.17  CNF conversion       : 0.03
% 6.36/2.17  Main loop            : 0.98
% 6.36/2.17  Inferencing          : 0.30
% 6.36/2.17  Reduction            : 0.40
% 6.36/2.17  Demodulation         : 0.30
% 6.36/2.17  BG Simplification    : 0.04
% 6.36/2.17  Subsumption          : 0.17
% 6.36/2.17  Abstraction          : 0.05
% 6.36/2.17  MUC search           : 0.00
% 6.36/2.17  Cooper               : 0.00
% 6.36/2.17  Total                : 1.42
% 6.36/2.17  Index Insertion      : 0.00
% 6.36/2.17  Index Deletion       : 0.00
% 6.36/2.17  Index Matching       : 0.00
% 6.36/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
