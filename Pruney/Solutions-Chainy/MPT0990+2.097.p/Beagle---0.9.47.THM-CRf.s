%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:10 EST 2020

% Result     : Theorem 5.95s
% Output     : CNFRefutation 5.95s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 358 expanded)
%              Number of leaves         :   39 ( 146 expanded)
%              Depth                    :   12
%              Number of atoms          :  294 (1492 expanded)
%              Number of equality atoms :  100 ( 516 expanded)
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

tff(f_187,negated_conjecture,(
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

tff(f_102,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_161,axiom,(
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

tff(f_78,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_90,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_119,axiom,(
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

tff(f_145,axiom,(
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

tff(f_43,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_60,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_32,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2,plain,(
    ! [A_1] : k1_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    ! [A_1] : k1_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_113,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_126,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_113])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_138,plain,(
    ! [A_59,B_60,C_61] :
      ( k2_relset_1(A_59,B_60,C_61) = k2_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_152,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_138])).

tff(c_670,plain,(
    ! [A_139,C_140,B_141] :
      ( k6_partfun1(A_139) = k5_relat_1(C_140,k2_funct_1(C_140))
      | k1_xboole_0 = B_141
      | ~ v2_funct_1(C_140)
      | k2_relset_1(A_139,B_141,C_140) != B_141
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_139,B_141)))
      | ~ v1_funct_2(C_140,A_139,B_141)
      | ~ v1_funct_1(C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_676,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_670])).

tff(c_686,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_152,c_676])).

tff(c_687,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_686])).

tff(c_766,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_687])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_24,plain,(
    ! [A_17] : m1_subset_1(k6_relat_1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_71,plain,(
    ! [A_17] : m1_subset_1(k6_partfun1(A_17),k1_zfmisc_1(k2_zfmisc_1(A_17,A_17))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_24])).

tff(c_127,plain,(
    ! [A_55,B_56,D_57] :
      ( r2_relset_1(A_55,B_56,D_57,D_57)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_134,plain,(
    ! [A_17] : r2_relset_1(A_17,A_17,k6_partfun1(A_17),k6_partfun1(A_17)) ),
    inference(resolution,[status(thm)],[c_71,c_127])).

tff(c_282,plain,(
    ! [D_92,B_88,F_90,A_91,C_87,E_89] :
      ( k1_partfun1(A_91,B_88,C_87,D_92,E_89,F_90) = k5_relat_1(E_89,F_90)
      | ~ m1_subset_1(F_90,k1_zfmisc_1(k2_zfmisc_1(C_87,D_92)))
      | ~ v1_funct_1(F_90)
      | ~ m1_subset_1(E_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_88)))
      | ~ v1_funct_1(E_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_288,plain,(
    ! [A_91,B_88,E_89] :
      ( k1_partfun1(A_91,B_88,'#skF_2','#skF_1',E_89,'#skF_4') = k5_relat_1(E_89,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_88)))
      | ~ v1_funct_1(E_89) ) ),
    inference(resolution,[status(thm)],[c_60,c_282])).

tff(c_324,plain,(
    ! [A_97,B_98,E_99] :
      ( k1_partfun1(A_97,B_98,'#skF_2','#skF_1',E_99,'#skF_4') = k5_relat_1(E_99,'#skF_4')
      | ~ m1_subset_1(E_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ v1_funct_1(E_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_288])).

tff(c_330,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_324])).

tff(c_337,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_330])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_170,plain,(
    ! [D_63,C_64,A_65,B_66] :
      ( D_63 = C_64
      | ~ r2_relset_1(A_65,B_66,C_64,D_63)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_178,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_56,c_170])).

tff(c_193,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_178])).

tff(c_212,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_342,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_212])).

tff(c_497,plain,(
    ! [C_108,D_111,F_110,A_107,E_109,B_112] :
      ( m1_subset_1(k1_partfun1(A_107,B_112,C_108,D_111,E_109,F_110),k1_zfmisc_1(k2_zfmisc_1(A_107,D_111)))
      | ~ m1_subset_1(F_110,k1_zfmisc_1(k2_zfmisc_1(C_108,D_111)))
      | ~ v1_funct_1(F_110)
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_112)))
      | ~ v1_funct_1(E_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_531,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_497])).

tff(c_552,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_64,c_60,c_531])).

tff(c_554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_552])).

tff(c_555,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_1200,plain,(
    ! [A_167,B_168,C_169,D_170] :
      ( k2_relset_1(A_167,B_168,C_169) = B_168
      | ~ r2_relset_1(B_168,B_168,k1_partfun1(B_168,A_167,A_167,B_168,D_170,C_169),k6_partfun1(B_168))
      | ~ m1_subset_1(D_170,k1_zfmisc_1(k2_zfmisc_1(B_168,A_167)))
      | ~ v1_funct_2(D_170,B_168,A_167)
      | ~ v1_funct_1(D_170)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168)))
      | ~ v1_funct_2(C_169,A_167,B_168)
      | ~ v1_funct_1(C_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1206,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_555,c_1200])).

tff(c_1210,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_70,c_68,c_66,c_134,c_152,c_1206])).

tff(c_1212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_766,c_1210])).

tff(c_1213,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_687])).

tff(c_1225,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1213])).

tff(c_8,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_75,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8])).

tff(c_58,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_1764,plain,(
    ! [A_200,E_201,C_204,B_203,D_202] :
      ( k1_xboole_0 = C_204
      | v2_funct_1(E_201)
      | k2_relset_1(A_200,B_203,D_202) != B_203
      | ~ v2_funct_1(k1_partfun1(A_200,B_203,B_203,C_204,D_202,E_201))
      | ~ m1_subset_1(E_201,k1_zfmisc_1(k2_zfmisc_1(B_203,C_204)))
      | ~ v1_funct_2(E_201,B_203,C_204)
      | ~ v1_funct_1(E_201)
      | ~ m1_subset_1(D_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_203)))
      | ~ v1_funct_2(D_202,A_200,B_203)
      | ~ v1_funct_1(D_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1772,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_555,c_1764])).

tff(c_1783,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_62,c_60,c_75,c_58,c_1772])).

tff(c_1785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1225,c_52,c_1783])).

tff(c_1787,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1213])).

tff(c_1786,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1213])).

tff(c_12,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_relat_1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_73,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k2_funct_1(A_3)) = k6_partfun1(k1_relat_1(A_3))
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12])).

tff(c_1794,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1786,c_73])).

tff(c_1804,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_1787,c_1794])).

tff(c_1850,plain,(
    k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1804,c_78])).

tff(c_1867,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1850])).

tff(c_624,plain,(
    ! [C_128,B_129,A_132,E_130,D_133,F_131] :
      ( k1_partfun1(A_132,B_129,C_128,D_133,E_130,F_131) = k5_relat_1(E_130,F_131)
      | ~ m1_subset_1(F_131,k1_zfmisc_1(k2_zfmisc_1(C_128,D_133)))
      | ~ v1_funct_1(F_131)
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_132,B_129)))
      | ~ v1_funct_1(E_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_630,plain,(
    ! [A_132,B_129,E_130] :
      ( k1_partfun1(A_132,B_129,'#skF_2','#skF_1',E_130,'#skF_4') = k5_relat_1(E_130,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_132,B_129)))
      | ~ v1_funct_1(E_130) ) ),
    inference(resolution,[status(thm)],[c_60,c_624])).

tff(c_1808,plain,(
    ! [A_205,B_206,E_207] :
      ( k1_partfun1(A_205,B_206,'#skF_2','#skF_1',E_207,'#skF_4') = k5_relat_1(E_207,'#skF_4')
      | ~ m1_subset_1(E_207,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206)))
      | ~ v1_funct_1(E_207) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_630])).

tff(c_1814,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1808])).

tff(c_1821,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_555,c_1814])).

tff(c_125,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_113])).

tff(c_54,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_144,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_138])).

tff(c_151,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_144])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_187])).

tff(c_674,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_670])).

tff(c_682,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_54,c_674])).

tff(c_683,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_682])).

tff(c_693,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_683,c_73])).

tff(c_703,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_70,c_54,c_693])).

tff(c_14,plain,(
    ! [A_4,B_6] :
      ( k2_funct_1(A_4) = B_6
      | k6_relat_1(k1_relat_1(A_4)) != k5_relat_1(A_4,B_6)
      | k2_relat_1(A_4) != k1_relat_1(B_6)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_72,plain,(
    ! [A_4,B_6] :
      ( k2_funct_1(A_4) = B_6
      | k6_partfun1(k1_relat_1(A_4)) != k5_relat_1(A_4,B_6)
      | k2_relat_1(A_4) != k1_relat_1(B_6)
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_14])).

tff(c_717,plain,(
    ! [B_6] :
      ( k2_funct_1('#skF_3') = B_6
      | k5_relat_1('#skF_3',B_6) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_6)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_6)
      | ~ v1_relat_1(B_6)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_703,c_72])).

tff(c_3308,plain,(
    ! [B_275] :
      ( k2_funct_1('#skF_3') = B_275
      | k5_relat_1('#skF_3',B_275) != k6_partfun1('#skF_1')
      | k1_relat_1(B_275) != '#skF_2'
      | ~ v1_funct_1(B_275)
      | ~ v1_relat_1(B_275) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_70,c_54,c_151,c_717])).

tff(c_3344,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_126,c_3308])).

tff(c_3386,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1867,c_1821,c_3344])).

tff(c_3388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_3386])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:49:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.18/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.95/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.95/2.17  
% 5.95/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.95/2.17  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.95/2.17  
% 5.95/2.17  %Foreground sorts:
% 5.95/2.17  
% 5.95/2.17  
% 5.95/2.17  %Background operators:
% 5.95/2.17  
% 5.95/2.17  
% 5.95/2.17  %Foreground operators:
% 5.95/2.17  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.95/2.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.95/2.17  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.95/2.17  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.95/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.95/2.17  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.95/2.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.95/2.17  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.95/2.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.95/2.17  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.95/2.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.95/2.17  tff('#skF_2', type, '#skF_2': $i).
% 5.95/2.17  tff('#skF_3', type, '#skF_3': $i).
% 5.95/2.17  tff('#skF_1', type, '#skF_1': $i).
% 5.95/2.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.95/2.17  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.95/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.95/2.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.95/2.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.95/2.17  tff('#skF_4', type, '#skF_4': $i).
% 5.95/2.17  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.95/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.95/2.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.95/2.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.95/2.17  
% 5.95/2.19  tff(f_187, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 5.95/2.19  tff(f_102, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.95/2.19  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.95/2.19  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.95/2.19  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.95/2.19  tff(f_161, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 5.95/2.19  tff(f_78, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 5.95/2.19  tff(f_76, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.95/2.19  tff(f_100, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.95/2.19  tff(f_90, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.95/2.19  tff(f_119, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 5.95/2.19  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.95/2.19  tff(f_145, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 5.95/2.19  tff(f_43, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.95/2.19  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 5.95/2.19  tff(c_48, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.95/2.19  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.95/2.19  tff(c_32, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.95/2.19  tff(c_2, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.95/2.19  tff(c_78, plain, (![A_1]: (k1_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2])).
% 5.95/2.19  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.95/2.19  tff(c_113, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.95/2.19  tff(c_126, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_113])).
% 5.95/2.19  tff(c_52, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.95/2.19  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.95/2.19  tff(c_138, plain, (![A_59, B_60, C_61]: (k2_relset_1(A_59, B_60, C_61)=k2_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.95/2.19  tff(c_152, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_138])).
% 5.95/2.19  tff(c_670, plain, (![A_139, C_140, B_141]: (k6_partfun1(A_139)=k5_relat_1(C_140, k2_funct_1(C_140)) | k1_xboole_0=B_141 | ~v2_funct_1(C_140) | k2_relset_1(A_139, B_141, C_140)!=B_141 | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_139, B_141))) | ~v1_funct_2(C_140, A_139, B_141) | ~v1_funct_1(C_140))), inference(cnfTransformation, [status(thm)], [f_161])).
% 5.95/2.19  tff(c_676, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_670])).
% 5.95/2.19  tff(c_686, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_152, c_676])).
% 5.95/2.19  tff(c_687, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_52, c_686])).
% 5.95/2.19  tff(c_766, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_687])).
% 5.95/2.19  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.95/2.19  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.95/2.19  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.95/2.19  tff(c_24, plain, (![A_17]: (m1_subset_1(k6_relat_1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.95/2.19  tff(c_71, plain, (![A_17]: (m1_subset_1(k6_partfun1(A_17), k1_zfmisc_1(k2_zfmisc_1(A_17, A_17))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_24])).
% 5.95/2.19  tff(c_127, plain, (![A_55, B_56, D_57]: (r2_relset_1(A_55, B_56, D_57, D_57) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.95/2.19  tff(c_134, plain, (![A_17]: (r2_relset_1(A_17, A_17, k6_partfun1(A_17), k6_partfun1(A_17)))), inference(resolution, [status(thm)], [c_71, c_127])).
% 5.95/2.19  tff(c_282, plain, (![D_92, B_88, F_90, A_91, C_87, E_89]: (k1_partfun1(A_91, B_88, C_87, D_92, E_89, F_90)=k5_relat_1(E_89, F_90) | ~m1_subset_1(F_90, k1_zfmisc_1(k2_zfmisc_1(C_87, D_92))) | ~v1_funct_1(F_90) | ~m1_subset_1(E_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_88))) | ~v1_funct_1(E_89))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.95/2.19  tff(c_288, plain, (![A_91, B_88, E_89]: (k1_partfun1(A_91, B_88, '#skF_2', '#skF_1', E_89, '#skF_4')=k5_relat_1(E_89, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_88))) | ~v1_funct_1(E_89))), inference(resolution, [status(thm)], [c_60, c_282])).
% 5.95/2.19  tff(c_324, plain, (![A_97, B_98, E_99]: (k1_partfun1(A_97, B_98, '#skF_2', '#skF_1', E_99, '#skF_4')=k5_relat_1(E_99, '#skF_4') | ~m1_subset_1(E_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~v1_funct_1(E_99))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_288])).
% 5.95/2.19  tff(c_330, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_324])).
% 5.95/2.19  tff(c_337, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_330])).
% 5.95/2.19  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.95/2.19  tff(c_170, plain, (![D_63, C_64, A_65, B_66]: (D_63=C_64 | ~r2_relset_1(A_65, B_66, C_64, D_63) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.95/2.19  tff(c_178, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_56, c_170])).
% 5.95/2.19  tff(c_193, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_178])).
% 5.95/2.19  tff(c_212, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_193])).
% 5.95/2.19  tff(c_342, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_337, c_212])).
% 5.95/2.19  tff(c_497, plain, (![C_108, D_111, F_110, A_107, E_109, B_112]: (m1_subset_1(k1_partfun1(A_107, B_112, C_108, D_111, E_109, F_110), k1_zfmisc_1(k2_zfmisc_1(A_107, D_111))) | ~m1_subset_1(F_110, k1_zfmisc_1(k2_zfmisc_1(C_108, D_111))) | ~v1_funct_1(F_110) | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_112))) | ~v1_funct_1(E_109))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.95/2.19  tff(c_531, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_337, c_497])).
% 5.95/2.19  tff(c_552, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_64, c_60, c_531])).
% 5.95/2.19  tff(c_554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_342, c_552])).
% 5.95/2.19  tff(c_555, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_193])).
% 5.95/2.19  tff(c_1200, plain, (![A_167, B_168, C_169, D_170]: (k2_relset_1(A_167, B_168, C_169)=B_168 | ~r2_relset_1(B_168, B_168, k1_partfun1(B_168, A_167, A_167, B_168, D_170, C_169), k6_partfun1(B_168)) | ~m1_subset_1(D_170, k1_zfmisc_1(k2_zfmisc_1(B_168, A_167))) | ~v1_funct_2(D_170, B_168, A_167) | ~v1_funct_1(D_170) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))) | ~v1_funct_2(C_169, A_167, B_168) | ~v1_funct_1(C_169))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.95/2.19  tff(c_1206, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_555, c_1200])).
% 5.95/2.19  tff(c_1210, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_70, c_68, c_66, c_134, c_152, c_1206])).
% 5.95/2.19  tff(c_1212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_766, c_1210])).
% 5.95/2.19  tff(c_1213, plain, (~v2_funct_1('#skF_4') | k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_687])).
% 5.95/2.19  tff(c_1225, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1213])).
% 5.95/2.19  tff(c_8, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.95/2.19  tff(c_75, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8])).
% 5.95/2.19  tff(c_58, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.95/2.19  tff(c_1764, plain, (![A_200, E_201, C_204, B_203, D_202]: (k1_xboole_0=C_204 | v2_funct_1(E_201) | k2_relset_1(A_200, B_203, D_202)!=B_203 | ~v2_funct_1(k1_partfun1(A_200, B_203, B_203, C_204, D_202, E_201)) | ~m1_subset_1(E_201, k1_zfmisc_1(k2_zfmisc_1(B_203, C_204))) | ~v1_funct_2(E_201, B_203, C_204) | ~v1_funct_1(E_201) | ~m1_subset_1(D_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_203))) | ~v1_funct_2(D_202, A_200, B_203) | ~v1_funct_1(D_202))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.95/2.19  tff(c_1772, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_555, c_1764])).
% 5.95/2.19  tff(c_1783, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_62, c_60, c_75, c_58, c_1772])).
% 5.95/2.19  tff(c_1785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1225, c_52, c_1783])).
% 5.95/2.19  tff(c_1787, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1213])).
% 5.95/2.19  tff(c_1786, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1213])).
% 5.95/2.19  tff(c_12, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_relat_1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.95/2.19  tff(c_73, plain, (![A_3]: (k5_relat_1(A_3, k2_funct_1(A_3))=k6_partfun1(k1_relat_1(A_3)) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12])).
% 5.95/2.19  tff(c_1794, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1786, c_73])).
% 5.95/2.19  tff(c_1804, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_1787, c_1794])).
% 5.95/2.19  tff(c_1850, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1804, c_78])).
% 5.95/2.19  tff(c_1867, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1850])).
% 5.95/2.19  tff(c_624, plain, (![C_128, B_129, A_132, E_130, D_133, F_131]: (k1_partfun1(A_132, B_129, C_128, D_133, E_130, F_131)=k5_relat_1(E_130, F_131) | ~m1_subset_1(F_131, k1_zfmisc_1(k2_zfmisc_1(C_128, D_133))) | ~v1_funct_1(F_131) | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_132, B_129))) | ~v1_funct_1(E_130))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.95/2.19  tff(c_630, plain, (![A_132, B_129, E_130]: (k1_partfun1(A_132, B_129, '#skF_2', '#skF_1', E_130, '#skF_4')=k5_relat_1(E_130, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_132, B_129))) | ~v1_funct_1(E_130))), inference(resolution, [status(thm)], [c_60, c_624])).
% 5.95/2.19  tff(c_1808, plain, (![A_205, B_206, E_207]: (k1_partfun1(A_205, B_206, '#skF_2', '#skF_1', E_207, '#skF_4')=k5_relat_1(E_207, '#skF_4') | ~m1_subset_1(E_207, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))) | ~v1_funct_1(E_207))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_630])).
% 5.95/2.19  tff(c_1814, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1808])).
% 5.95/2.19  tff(c_1821, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_555, c_1814])).
% 5.95/2.19  tff(c_125, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_113])).
% 5.95/2.19  tff(c_54, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.95/2.19  tff(c_144, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_138])).
% 5.95/2.19  tff(c_151, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_144])).
% 5.95/2.19  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_187])).
% 5.95/2.19  tff(c_674, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_670])).
% 5.95/2.19  tff(c_682, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_54, c_674])).
% 5.95/2.19  tff(c_683, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_682])).
% 5.95/2.19  tff(c_693, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_683, c_73])).
% 5.95/2.19  tff(c_703, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_70, c_54, c_693])).
% 5.95/2.19  tff(c_14, plain, (![A_4, B_6]: (k2_funct_1(A_4)=B_6 | k6_relat_1(k1_relat_1(A_4))!=k5_relat_1(A_4, B_6) | k2_relat_1(A_4)!=k1_relat_1(B_6) | ~v2_funct_1(A_4) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.95/2.19  tff(c_72, plain, (![A_4, B_6]: (k2_funct_1(A_4)=B_6 | k6_partfun1(k1_relat_1(A_4))!=k5_relat_1(A_4, B_6) | k2_relat_1(A_4)!=k1_relat_1(B_6) | ~v2_funct_1(A_4) | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_14])).
% 5.95/2.19  tff(c_717, plain, (![B_6]: (k2_funct_1('#skF_3')=B_6 | k5_relat_1('#skF_3', B_6)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_6) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_6) | ~v1_relat_1(B_6) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_703, c_72])).
% 5.95/2.19  tff(c_3308, plain, (![B_275]: (k2_funct_1('#skF_3')=B_275 | k5_relat_1('#skF_3', B_275)!=k6_partfun1('#skF_1') | k1_relat_1(B_275)!='#skF_2' | ~v1_funct_1(B_275) | ~v1_relat_1(B_275))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_70, c_54, c_151, c_717])).
% 5.95/2.19  tff(c_3344, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_126, c_3308])).
% 5.95/2.19  tff(c_3386, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1867, c_1821, c_3344])).
% 5.95/2.19  tff(c_3388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_3386])).
% 5.95/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.95/2.19  
% 5.95/2.19  Inference rules
% 5.95/2.19  ----------------------
% 5.95/2.19  #Ref     : 0
% 5.95/2.19  #Sup     : 715
% 5.95/2.19  #Fact    : 0
% 5.95/2.19  #Define  : 0
% 5.95/2.19  #Split   : 18
% 5.95/2.19  #Chain   : 0
% 5.95/2.19  #Close   : 0
% 5.95/2.19  
% 5.95/2.19  Ordering : KBO
% 5.95/2.19  
% 5.95/2.19  Simplification rules
% 5.95/2.19  ----------------------
% 5.95/2.19  #Subsume      : 28
% 5.95/2.19  #Demod        : 1114
% 5.95/2.19  #Tautology    : 269
% 5.95/2.19  #SimpNegUnit  : 78
% 5.95/2.19  #BackRed      : 25
% 5.95/2.19  
% 5.95/2.19  #Partial instantiations: 0
% 5.95/2.19  #Strategies tried      : 1
% 5.95/2.19  
% 5.95/2.19  Timing (in seconds)
% 5.95/2.19  ----------------------
% 5.95/2.20  Preprocessing        : 0.38
% 5.95/2.20  Parsing              : 0.21
% 5.95/2.20  CNF conversion       : 0.02
% 5.95/2.20  Main loop            : 1.01
% 5.95/2.20  Inferencing          : 0.34
% 5.95/2.20  Reduction            : 0.39
% 5.95/2.20  Demodulation         : 0.29
% 5.95/2.20  BG Simplification    : 0.04
% 5.95/2.20  Subsumption          : 0.17
% 5.95/2.20  Abstraction          : 0.05
% 5.95/2.20  MUC search           : 0.00
% 5.95/2.20  Cooper               : 0.00
% 5.95/2.20  Total                : 1.44
% 5.95/2.20  Index Insertion      : 0.00
% 5.95/2.20  Index Deletion       : 0.00
% 5.95/2.20  Index Matching       : 0.00
% 5.95/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
