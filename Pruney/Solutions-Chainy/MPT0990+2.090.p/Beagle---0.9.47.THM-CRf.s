%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:09 EST 2020

% Result     : Theorem 5.91s
% Output     : CNFRefutation 6.00s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 382 expanded)
%              Number of leaves         :   40 ( 156 expanded)
%              Depth                    :   14
%              Number of atoms          :  311 (1676 expanded)
%              Number of equality atoms :  110 ( 583 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_202,negated_conjecture,(
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

tff(f_117,axiom,(
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

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_176,axiom,(
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

tff(f_105,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_115,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_101,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_134,axiom,(
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

tff(f_160,axiom,(
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

tff(c_52,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_36,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_4,plain,(
    ! [A_1] : k2_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    ! [A_1] : k2_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_118,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_131,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_118])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_142,plain,(
    ! [A_62,B_63,C_64] :
      ( k2_relset_1(A_62,B_63,C_64) = k2_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_156,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_142])).

tff(c_696,plain,(
    ! [B_143,C_144,A_145] :
      ( k6_partfun1(B_143) = k5_relat_1(k2_funct_1(C_144),C_144)
      | k1_xboole_0 = B_143
      | ~ v2_funct_1(C_144)
      | k2_relset_1(A_145,B_143,C_144) != B_143
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_145,B_143)))
      | ~ v1_funct_2(C_144,A_145,B_143)
      | ~ v1_funct_1(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_702,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_696])).

tff(c_712,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_156,c_702])).

tff(c_713,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_712])).

tff(c_728,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_713])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_32,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_132,plain,(
    ! [A_59,B_60,D_61] :
      ( r2_relset_1(A_59,B_60,D_61,D_61)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_139,plain,(
    ! [A_26] : r2_relset_1(A_26,A_26,k6_partfun1(A_26),k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_32,c_132])).

tff(c_296,plain,(
    ! [E_95,F_92,B_96,D_94,C_93,A_97] :
      ( k1_partfun1(A_97,B_96,C_93,D_94,E_95,F_92) = k5_relat_1(E_95,F_92)
      | ~ m1_subset_1(F_92,k1_zfmisc_1(k2_zfmisc_1(C_93,D_94)))
      | ~ v1_funct_1(F_92)
      | ~ m1_subset_1(E_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96)))
      | ~ v1_funct_1(E_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_302,plain,(
    ! [A_97,B_96,E_95] :
      ( k1_partfun1(A_97,B_96,'#skF_2','#skF_1',E_95,'#skF_4') = k5_relat_1(E_95,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96)))
      | ~ v1_funct_1(E_95) ) ),
    inference(resolution,[status(thm)],[c_64,c_296])).

tff(c_311,plain,(
    ! [A_99,B_100,E_101] :
      ( k1_partfun1(A_99,B_100,'#skF_2','#skF_1',E_101,'#skF_4') = k5_relat_1(E_101,'#skF_4')
      | ~ m1_subset_1(E_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ v1_funct_1(E_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_302])).

tff(c_317,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_311])).

tff(c_324,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_317])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_174,plain,(
    ! [D_66,C_67,A_68,B_69] :
      ( D_66 = C_67
      | ~ r2_relset_1(A_68,B_69,C_67,D_66)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_180,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_174])).

tff(c_191,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_180])).

tff(c_227,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_329,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_227])).

tff(c_519,plain,(
    ! [F_116,C_111,A_115,D_113,E_114,B_112] :
      ( m1_subset_1(k1_partfun1(A_115,B_112,C_111,D_113,E_114,F_116),k1_zfmisc_1(k2_zfmisc_1(A_115,D_113)))
      | ~ m1_subset_1(F_116,k1_zfmisc_1(k2_zfmisc_1(C_111,D_113)))
      | ~ v1_funct_1(F_116)
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_115,B_112)))
      | ~ v1_funct_1(E_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_559,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_519])).

tff(c_578,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_559])).

tff(c_580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_329,c_578])).

tff(c_581,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_1210,plain,(
    ! [A_166,B_167,C_168,D_169] :
      ( k2_relset_1(A_166,B_167,C_168) = B_167
      | ~ r2_relset_1(B_167,B_167,k1_partfun1(B_167,A_166,A_166,B_167,D_169,C_168),k6_partfun1(B_167))
      | ~ m1_subset_1(D_169,k1_zfmisc_1(k2_zfmisc_1(B_167,A_166)))
      | ~ v1_funct_2(D_169,B_167,A_166)
      | ~ v1_funct_1(D_169)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ v1_funct_2(C_168,A_166,B_167)
      | ~ v1_funct_1(C_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1216,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_581,c_1210])).

tff(c_1220,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_74,c_72,c_70,c_139,c_156,c_1216])).

tff(c_1222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_728,c_1220])).

tff(c_1223,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_713])).

tff(c_1234,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1223])).

tff(c_8,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_79,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_1716,plain,(
    ! [E_191,C_193,B_192,A_190,D_194] :
      ( k1_xboole_0 = C_193
      | v2_funct_1(E_191)
      | k2_relset_1(A_190,B_192,D_194) != B_192
      | ~ v2_funct_1(k1_partfun1(A_190,B_192,B_192,C_193,D_194,E_191))
      | ~ m1_subset_1(E_191,k1_zfmisc_1(k2_zfmisc_1(B_192,C_193)))
      | ~ v1_funct_2(E_191,B_192,C_193)
      | ~ v1_funct_1(E_191)
      | ~ m1_subset_1(D_194,k1_zfmisc_1(k2_zfmisc_1(A_190,B_192)))
      | ~ v1_funct_2(D_194,A_190,B_192)
      | ~ v1_funct_1(D_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1722,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_581,c_1716])).

tff(c_1730,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_64,c_79,c_62,c_1722])).

tff(c_1732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1234,c_56,c_1730])).

tff(c_1734,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1223])).

tff(c_1224,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_713])).

tff(c_1225,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1224,c_156])).

tff(c_1788,plain,(
    ! [A_199,C_200,B_201] :
      ( k6_partfun1(A_199) = k5_relat_1(C_200,k2_funct_1(C_200))
      | k1_xboole_0 = B_201
      | ~ v2_funct_1(C_200)
      | k2_relset_1(A_199,B_201,C_200) != B_201
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_199,B_201)))
      | ~ v1_funct_2(C_200,A_199,B_201)
      | ~ v1_funct_1(C_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1794,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_1788])).

tff(c_1804,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1225,c_1734,c_1794])).

tff(c_1805,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1804])).

tff(c_14,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_relat_1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_76,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_partfun1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_14])).

tff(c_1910,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1805,c_76])).

tff(c_1922,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_68,c_1734,c_1910])).

tff(c_1957,plain,(
    k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1922,c_81])).

tff(c_1980,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1957])).

tff(c_650,plain,(
    ! [C_133,B_136,D_134,A_137,F_132,E_135] :
      ( k1_partfun1(A_137,B_136,C_133,D_134,E_135,F_132) = k5_relat_1(E_135,F_132)
      | ~ m1_subset_1(F_132,k1_zfmisc_1(k2_zfmisc_1(C_133,D_134)))
      | ~ v1_funct_1(F_132)
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_137,B_136)))
      | ~ v1_funct_1(E_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_656,plain,(
    ! [A_137,B_136,E_135] :
      ( k1_partfun1(A_137,B_136,'#skF_2','#skF_1',E_135,'#skF_4') = k5_relat_1(E_135,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_137,B_136)))
      | ~ v1_funct_1(E_135) ) ),
    inference(resolution,[status(thm)],[c_64,c_650])).

tff(c_1758,plain,(
    ! [A_195,B_196,E_197] :
      ( k1_partfun1(A_195,B_196,'#skF_2','#skF_1',E_197,'#skF_4') = k5_relat_1(E_197,'#skF_4')
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196)))
      | ~ v1_funct_1(E_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_656])).

tff(c_1764,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1758])).

tff(c_1771,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_581,c_1764])).

tff(c_130,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_118])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_148,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_142])).

tff(c_155,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_148])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_1792,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1788])).

tff(c_1800,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_62,c_58,c_1792])).

tff(c_1801,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1800])).

tff(c_1813,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1801,c_76])).

tff(c_1825,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_74,c_58,c_1813])).

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

tff(c_75,plain,(
    ! [A_7,B_9] :
      ( k2_funct_1(A_7) = B_9
      | k6_partfun1(k1_relat_1(A_7)) != k5_relat_1(A_7,B_9)
      | k2_relat_1(A_7) != k1_relat_1(B_9)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_16])).

tff(c_1841,plain,(
    ! [B_9] :
      ( k2_funct_1('#skF_3') = B_9
      | k5_relat_1('#skF_3',B_9) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_9)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1825,c_75])).

tff(c_3282,plain,(
    ! [B_260] :
      ( k2_funct_1('#skF_3') = B_260
      | k5_relat_1('#skF_3',B_260) != k6_partfun1('#skF_1')
      | k1_relat_1(B_260) != '#skF_2'
      | ~ v1_funct_1(B_260)
      | ~ v1_relat_1(B_260) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_74,c_58,c_155,c_1841])).

tff(c_3318,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_131,c_3282])).

tff(c_3360,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1980,c_1771,c_3318])).

tff(c_3362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3360])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:39:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.91/2.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.00/2.15  
% 6.00/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.00/2.15  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.00/2.15  
% 6.00/2.15  %Foreground sorts:
% 6.00/2.15  
% 6.00/2.15  
% 6.00/2.15  %Background operators:
% 6.00/2.15  
% 6.00/2.15  
% 6.00/2.15  %Foreground operators:
% 6.00/2.15  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.00/2.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.00/2.15  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.00/2.15  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.00/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.00/2.15  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.00/2.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.00/2.15  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.00/2.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.00/2.15  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.00/2.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.00/2.15  tff('#skF_2', type, '#skF_2': $i).
% 6.00/2.15  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.00/2.15  tff('#skF_3', type, '#skF_3': $i).
% 6.00/2.15  tff('#skF_1', type, '#skF_1': $i).
% 6.00/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.00/2.15  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.00/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.00/2.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.00/2.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.00/2.15  tff('#skF_4', type, '#skF_4': $i).
% 6.00/2.15  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.00/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.00/2.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.00/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.00/2.15  
% 6.00/2.17  tff(f_202, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 6.00/2.17  tff(f_117, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.00/2.17  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 6.00/2.17  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.00/2.17  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.00/2.17  tff(f_176, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 6.00/2.17  tff(f_105, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.00/2.17  tff(f_89, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.00/2.17  tff(f_115, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.00/2.17  tff(f_101, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.00/2.17  tff(f_134, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 6.00/2.17  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.00/2.17  tff(f_160, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 6.00/2.17  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 6.00/2.17  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 6.00/2.17  tff(c_52, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.00/2.17  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.00/2.17  tff(c_36, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.00/2.17  tff(c_4, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.00/2.17  tff(c_81, plain, (![A_1]: (k2_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4])).
% 6.00/2.17  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.00/2.17  tff(c_118, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.00/2.17  tff(c_131, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_118])).
% 6.00/2.17  tff(c_56, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.00/2.17  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.00/2.17  tff(c_142, plain, (![A_62, B_63, C_64]: (k2_relset_1(A_62, B_63, C_64)=k2_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.00/2.17  tff(c_156, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_142])).
% 6.00/2.17  tff(c_696, plain, (![B_143, C_144, A_145]: (k6_partfun1(B_143)=k5_relat_1(k2_funct_1(C_144), C_144) | k1_xboole_0=B_143 | ~v2_funct_1(C_144) | k2_relset_1(A_145, B_143, C_144)!=B_143 | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_145, B_143))) | ~v1_funct_2(C_144, A_145, B_143) | ~v1_funct_1(C_144))), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.00/2.17  tff(c_702, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_696])).
% 6.00/2.17  tff(c_712, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_156, c_702])).
% 6.00/2.17  tff(c_713, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_56, c_712])).
% 6.00/2.17  tff(c_728, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_713])).
% 6.00/2.17  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.00/2.17  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.00/2.17  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.00/2.17  tff(c_32, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.00/2.17  tff(c_132, plain, (![A_59, B_60, D_61]: (r2_relset_1(A_59, B_60, D_61, D_61) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.00/2.17  tff(c_139, plain, (![A_26]: (r2_relset_1(A_26, A_26, k6_partfun1(A_26), k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_32, c_132])).
% 6.00/2.17  tff(c_296, plain, (![E_95, F_92, B_96, D_94, C_93, A_97]: (k1_partfun1(A_97, B_96, C_93, D_94, E_95, F_92)=k5_relat_1(E_95, F_92) | ~m1_subset_1(F_92, k1_zfmisc_1(k2_zfmisc_1(C_93, D_94))) | ~v1_funct_1(F_92) | ~m1_subset_1(E_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))) | ~v1_funct_1(E_95))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.00/2.17  tff(c_302, plain, (![A_97, B_96, E_95]: (k1_partfun1(A_97, B_96, '#skF_2', '#skF_1', E_95, '#skF_4')=k5_relat_1(E_95, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))) | ~v1_funct_1(E_95))), inference(resolution, [status(thm)], [c_64, c_296])).
% 6.00/2.17  tff(c_311, plain, (![A_99, B_100, E_101]: (k1_partfun1(A_99, B_100, '#skF_2', '#skF_1', E_101, '#skF_4')=k5_relat_1(E_101, '#skF_4') | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~v1_funct_1(E_101))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_302])).
% 6.00/2.17  tff(c_317, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_311])).
% 6.00/2.17  tff(c_324, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_317])).
% 6.00/2.17  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.00/2.17  tff(c_174, plain, (![D_66, C_67, A_68, B_69]: (D_66=C_67 | ~r2_relset_1(A_68, B_69, C_67, D_66) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.00/2.17  tff(c_180, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_174])).
% 6.00/2.17  tff(c_191, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_180])).
% 6.00/2.17  tff(c_227, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_191])).
% 6.00/2.17  tff(c_329, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_227])).
% 6.00/2.17  tff(c_519, plain, (![F_116, C_111, A_115, D_113, E_114, B_112]: (m1_subset_1(k1_partfun1(A_115, B_112, C_111, D_113, E_114, F_116), k1_zfmisc_1(k2_zfmisc_1(A_115, D_113))) | ~m1_subset_1(F_116, k1_zfmisc_1(k2_zfmisc_1(C_111, D_113))) | ~v1_funct_1(F_116) | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_115, B_112))) | ~v1_funct_1(E_114))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.00/2.17  tff(c_559, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_324, c_519])).
% 6.00/2.17  tff(c_578, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_559])).
% 6.00/2.17  tff(c_580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_329, c_578])).
% 6.00/2.17  tff(c_581, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_191])).
% 6.00/2.17  tff(c_1210, plain, (![A_166, B_167, C_168, D_169]: (k2_relset_1(A_166, B_167, C_168)=B_167 | ~r2_relset_1(B_167, B_167, k1_partfun1(B_167, A_166, A_166, B_167, D_169, C_168), k6_partfun1(B_167)) | ~m1_subset_1(D_169, k1_zfmisc_1(k2_zfmisc_1(B_167, A_166))) | ~v1_funct_2(D_169, B_167, A_166) | ~v1_funct_1(D_169) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~v1_funct_2(C_168, A_166, B_167) | ~v1_funct_1(C_168))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.00/2.17  tff(c_1216, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_581, c_1210])).
% 6.00/2.17  tff(c_1220, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_74, c_72, c_70, c_139, c_156, c_1216])).
% 6.00/2.17  tff(c_1222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_728, c_1220])).
% 6.00/2.17  tff(c_1223, plain, (~v2_funct_1('#skF_4') | k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_713])).
% 6.00/2.17  tff(c_1234, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1223])).
% 6.00/2.17  tff(c_8, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.00/2.17  tff(c_79, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8])).
% 6.00/2.17  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.00/2.17  tff(c_1716, plain, (![E_191, C_193, B_192, A_190, D_194]: (k1_xboole_0=C_193 | v2_funct_1(E_191) | k2_relset_1(A_190, B_192, D_194)!=B_192 | ~v2_funct_1(k1_partfun1(A_190, B_192, B_192, C_193, D_194, E_191)) | ~m1_subset_1(E_191, k1_zfmisc_1(k2_zfmisc_1(B_192, C_193))) | ~v1_funct_2(E_191, B_192, C_193) | ~v1_funct_1(E_191) | ~m1_subset_1(D_194, k1_zfmisc_1(k2_zfmisc_1(A_190, B_192))) | ~v1_funct_2(D_194, A_190, B_192) | ~v1_funct_1(D_194))), inference(cnfTransformation, [status(thm)], [f_160])).
% 6.00/2.17  tff(c_1722, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_581, c_1716])).
% 6.00/2.17  tff(c_1730, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_66, c_64, c_79, c_62, c_1722])).
% 6.00/2.17  tff(c_1732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1234, c_56, c_1730])).
% 6.00/2.17  tff(c_1734, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1223])).
% 6.00/2.17  tff(c_1224, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_713])).
% 6.00/2.17  tff(c_1225, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1224, c_156])).
% 6.00/2.17  tff(c_1788, plain, (![A_199, C_200, B_201]: (k6_partfun1(A_199)=k5_relat_1(C_200, k2_funct_1(C_200)) | k1_xboole_0=B_201 | ~v2_funct_1(C_200) | k2_relset_1(A_199, B_201, C_200)!=B_201 | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_199, B_201))) | ~v1_funct_2(C_200, A_199, B_201) | ~v1_funct_1(C_200))), inference(cnfTransformation, [status(thm)], [f_176])).
% 6.00/2.17  tff(c_1794, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_1788])).
% 6.00/2.17  tff(c_1804, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1225, c_1734, c_1794])).
% 6.00/2.17  tff(c_1805, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_1804])).
% 6.00/2.17  tff(c_14, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_relat_1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.00/2.17  tff(c_76, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_partfun1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_14])).
% 6.00/2.17  tff(c_1910, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1805, c_76])).
% 6.00/2.17  tff(c_1922, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_68, c_1734, c_1910])).
% 6.00/2.17  tff(c_1957, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1922, c_81])).
% 6.00/2.17  tff(c_1980, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1957])).
% 6.00/2.17  tff(c_650, plain, (![C_133, B_136, D_134, A_137, F_132, E_135]: (k1_partfun1(A_137, B_136, C_133, D_134, E_135, F_132)=k5_relat_1(E_135, F_132) | ~m1_subset_1(F_132, k1_zfmisc_1(k2_zfmisc_1(C_133, D_134))) | ~v1_funct_1(F_132) | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_137, B_136))) | ~v1_funct_1(E_135))), inference(cnfTransformation, [status(thm)], [f_115])).
% 6.00/2.17  tff(c_656, plain, (![A_137, B_136, E_135]: (k1_partfun1(A_137, B_136, '#skF_2', '#skF_1', E_135, '#skF_4')=k5_relat_1(E_135, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_137, B_136))) | ~v1_funct_1(E_135))), inference(resolution, [status(thm)], [c_64, c_650])).
% 6.00/2.17  tff(c_1758, plain, (![A_195, B_196, E_197]: (k1_partfun1(A_195, B_196, '#skF_2', '#skF_1', E_197, '#skF_4')=k5_relat_1(E_197, '#skF_4') | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))) | ~v1_funct_1(E_197))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_656])).
% 6.00/2.17  tff(c_1764, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_1758])).
% 6.00/2.17  tff(c_1771, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_581, c_1764])).
% 6.00/2.17  tff(c_130, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_118])).
% 6.00/2.17  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.00/2.17  tff(c_148, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_142])).
% 6.00/2.17  tff(c_155, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_148])).
% 6.00/2.17  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.00/2.17  tff(c_1792, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_1788])).
% 6.00/2.17  tff(c_1800, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_62, c_58, c_1792])).
% 6.00/2.17  tff(c_1801, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_1800])).
% 6.00/2.17  tff(c_1813, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1801, c_76])).
% 6.00/2.17  tff(c_1825, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_74, c_58, c_1813])).
% 6.00/2.17  tff(c_16, plain, (![A_7, B_9]: (k2_funct_1(A_7)=B_9 | k6_relat_1(k1_relat_1(A_7))!=k5_relat_1(A_7, B_9) | k2_relat_1(A_7)!=k1_relat_1(B_9) | ~v2_funct_1(A_7) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.00/2.17  tff(c_75, plain, (![A_7, B_9]: (k2_funct_1(A_7)=B_9 | k6_partfun1(k1_relat_1(A_7))!=k5_relat_1(A_7, B_9) | k2_relat_1(A_7)!=k1_relat_1(B_9) | ~v2_funct_1(A_7) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_16])).
% 6.00/2.17  tff(c_1841, plain, (![B_9]: (k2_funct_1('#skF_3')=B_9 | k5_relat_1('#skF_3', B_9)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_9) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1825, c_75])).
% 6.00/2.17  tff(c_3282, plain, (![B_260]: (k2_funct_1('#skF_3')=B_260 | k5_relat_1('#skF_3', B_260)!=k6_partfun1('#skF_1') | k1_relat_1(B_260)!='#skF_2' | ~v1_funct_1(B_260) | ~v1_relat_1(B_260))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_74, c_58, c_155, c_1841])).
% 6.00/2.17  tff(c_3318, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_131, c_3282])).
% 6.00/2.17  tff(c_3360, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1980, c_1771, c_3318])).
% 6.00/2.17  tff(c_3362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_3360])).
% 6.00/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.00/2.17  
% 6.00/2.17  Inference rules
% 6.00/2.17  ----------------------
% 6.00/2.17  #Ref     : 0
% 6.00/2.17  #Sup     : 724
% 6.00/2.17  #Fact    : 0
% 6.00/2.17  #Define  : 0
% 6.00/2.17  #Split   : 17
% 6.00/2.17  #Chain   : 0
% 6.00/2.17  #Close   : 0
% 6.00/2.17  
% 6.00/2.17  Ordering : KBO
% 6.00/2.17  
% 6.00/2.17  Simplification rules
% 6.00/2.17  ----------------------
% 6.00/2.17  #Subsume      : 20
% 6.00/2.17  #Demod        : 1093
% 6.00/2.17  #Tautology    : 285
% 6.00/2.17  #SimpNegUnit  : 68
% 6.00/2.17  #BackRed      : 19
% 6.00/2.17  
% 6.00/2.17  #Partial instantiations: 0
% 6.00/2.17  #Strategies tried      : 1
% 6.00/2.17  
% 6.00/2.17  Timing (in seconds)
% 6.00/2.17  ----------------------
% 6.00/2.18  Preprocessing        : 0.36
% 6.00/2.18  Parsing              : 0.19
% 6.00/2.18  CNF conversion       : 0.02
% 6.00/2.18  Main loop            : 0.96
% 6.00/2.18  Inferencing          : 0.30
% 6.00/2.18  Reduction            : 0.39
% 6.00/2.18  Demodulation         : 0.29
% 6.00/2.18  BG Simplification    : 0.04
% 6.00/2.18  Subsumption          : 0.16
% 6.00/2.18  Abstraction          : 0.04
% 6.00/2.18  MUC search           : 0.00
% 6.00/2.18  Cooper               : 0.00
% 6.00/2.18  Total                : 1.36
% 6.00/2.18  Index Insertion      : 0.00
% 6.00/2.18  Index Deletion       : 0.00
% 6.00/2.18  Index Matching       : 0.00
% 6.00/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
