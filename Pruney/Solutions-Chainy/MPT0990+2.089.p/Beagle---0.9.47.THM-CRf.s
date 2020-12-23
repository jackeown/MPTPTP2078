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
% DateTime   : Thu Dec  3 10:13:09 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.61s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 336 expanded)
%              Number of leaves         :   40 ( 140 expanded)
%              Depth                    :   11
%              Number of atoms          :  288 (1468 expanded)
%              Number of equality atoms :   97 ( 498 expanded)
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

tff(f_117,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

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

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_116,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_129,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_116])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_140,plain,(
    ! [A_62,B_63,C_64] :
      ( k2_relset_1(A_62,B_63,C_64) = k2_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_154,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_140])).

tff(c_630,plain,(
    ! [A_146,C_147,B_148] :
      ( k6_partfun1(A_146) = k5_relat_1(C_147,k2_funct_1(C_147))
      | k1_xboole_0 = B_148
      | ~ v2_funct_1(C_147)
      | k2_relset_1(A_146,B_148,C_147) != B_148
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_146,B_148)))
      | ~ v1_funct_2(C_147,A_146,B_148)
      | ~ v1_funct_1(C_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_636,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_630])).

tff(c_646,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_154,c_636])).

tff(c_647,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_646])).

tff(c_684,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_647])).

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

tff(c_130,plain,(
    ! [A_59,B_60,D_61] :
      ( r2_relset_1(A_59,B_60,D_61,D_61)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_137,plain,(
    ! [A_26] : r2_relset_1(A_26,A_26,k6_partfun1(A_26),k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_32,c_130])).

tff(c_281,plain,(
    ! [E_95,F_92,B_96,D_94,C_93,A_97] :
      ( k1_partfun1(A_97,B_96,C_93,D_94,E_95,F_92) = k5_relat_1(E_95,F_92)
      | ~ m1_subset_1(F_92,k1_zfmisc_1(k2_zfmisc_1(C_93,D_94)))
      | ~ v1_funct_1(F_92)
      | ~ m1_subset_1(E_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96)))
      | ~ v1_funct_1(E_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_287,plain,(
    ! [A_97,B_96,E_95] :
      ( k1_partfun1(A_97,B_96,'#skF_2','#skF_1',E_95,'#skF_4') = k5_relat_1(E_95,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_96)))
      | ~ v1_funct_1(E_95) ) ),
    inference(resolution,[status(thm)],[c_64,c_281])).

tff(c_296,plain,(
    ! [A_99,B_100,E_101] :
      ( k1_partfun1(A_99,B_100,'#skF_2','#skF_1',E_101,'#skF_4') = k5_relat_1(E_101,'#skF_4')
      | ~ m1_subset_1(E_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ v1_funct_1(E_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_287])).

tff(c_302,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_296])).

tff(c_309,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_302])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_198,plain,(
    ! [D_71,C_72,A_73,B_74] :
      ( D_71 = C_72
      | ~ r2_relset_1(A_73,B_74,C_72,D_71)
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74)))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_206,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_198])).

tff(c_221,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_206])).

tff(c_222,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_314,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_222])).

tff(c_457,plain,(
    ! [B_115,D_116,C_114,E_117,A_118,F_119] :
      ( m1_subset_1(k1_partfun1(A_118,B_115,C_114,D_116,E_117,F_119),k1_zfmisc_1(k2_zfmisc_1(A_118,D_116)))
      | ~ m1_subset_1(F_119,k1_zfmisc_1(k2_zfmisc_1(C_114,D_116)))
      | ~ v1_funct_1(F_119)
      | ~ m1_subset_1(E_117,k1_zfmisc_1(k2_zfmisc_1(A_118,B_115)))
      | ~ v1_funct_1(E_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_497,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_457])).

tff(c_516,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_497])).

tff(c_518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_516])).

tff(c_519,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_1119,plain,(
    ! [A_171,B_172,C_173,D_174] :
      ( k2_relset_1(A_171,B_172,C_173) = B_172
      | ~ r2_relset_1(B_172,B_172,k1_partfun1(B_172,A_171,A_171,B_172,D_174,C_173),k6_partfun1(B_172))
      | ~ m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(B_172,A_171)))
      | ~ v1_funct_2(D_174,B_172,A_171)
      | ~ v1_funct_1(D_174)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172)))
      | ~ v1_funct_2(C_173,A_171,B_172)
      | ~ v1_funct_1(C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1125,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_1119])).

tff(c_1129,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_74,c_72,c_70,c_137,c_154,c_1125])).

tff(c_1131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_684,c_1129])).

tff(c_1132,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_647])).

tff(c_1143,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1132])).

tff(c_36,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_8,plain,(
    ! [A_2] : v2_funct_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_77,plain,(
    ! [A_2] : v2_funct_1(k6_partfun1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_1777,plain,(
    ! [B_208,C_209,A_206,D_210,E_207] :
      ( k1_xboole_0 = C_209
      | v2_funct_1(E_207)
      | k2_relset_1(A_206,B_208,D_210) != B_208
      | ~ v2_funct_1(k1_partfun1(A_206,B_208,B_208,C_209,D_210,E_207))
      | ~ m1_subset_1(E_207,k1_zfmisc_1(k2_zfmisc_1(B_208,C_209)))
      | ~ v1_funct_2(E_207,B_208,C_209)
      | ~ v1_funct_1(E_207)
      | ~ m1_subset_1(D_210,k1_zfmisc_1(k2_zfmisc_1(A_206,B_208)))
      | ~ v1_funct_2(D_210,A_206,B_208)
      | ~ v1_funct_1(D_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1783,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_519,c_1777])).

tff(c_1791,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_64,c_77,c_62,c_1783])).

tff(c_1793,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1143,c_56,c_1791])).

tff(c_1795,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1132])).

tff(c_4,plain,(
    ! [A_1] : k2_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_79,plain,(
    ! [A_1] : k2_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4])).

tff(c_1794,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1132])).

tff(c_12,plain,(
    ! [A_6] :
      ( k2_relat_1(k5_relat_1(A_6,k2_funct_1(A_6))) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1803,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1794,c_12])).

tff(c_1815,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_68,c_1795,c_79,c_1803])).

tff(c_584,plain,(
    ! [E_138,F_135,C_136,D_137,B_139,A_140] :
      ( k1_partfun1(A_140,B_139,C_136,D_137,E_138,F_135) = k5_relat_1(E_138,F_135)
      | ~ m1_subset_1(F_135,k1_zfmisc_1(k2_zfmisc_1(C_136,D_137)))
      | ~ v1_funct_1(F_135)
      | ~ m1_subset_1(E_138,k1_zfmisc_1(k2_zfmisc_1(A_140,B_139)))
      | ~ v1_funct_1(E_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_590,plain,(
    ! [A_140,B_139,E_138] :
      ( k1_partfun1(A_140,B_139,'#skF_2','#skF_1',E_138,'#skF_4') = k5_relat_1(E_138,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_138,k1_zfmisc_1(k2_zfmisc_1(A_140,B_139)))
      | ~ v1_funct_1(E_138) ) ),
    inference(resolution,[status(thm)],[c_64,c_584])).

tff(c_1831,plain,(
    ! [A_211,B_212,E_213] :
      ( k1_partfun1(A_211,B_212,'#skF_2','#skF_1',E_213,'#skF_4') = k5_relat_1(E_213,'#skF_4')
      | ~ m1_subset_1(E_213,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212)))
      | ~ v1_funct_1(E_213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_590])).

tff(c_1837,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1831])).

tff(c_1844,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_519,c_1837])).

tff(c_128,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_116])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_146,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_140])).

tff(c_153,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_146])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_634,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_630])).

tff(c_642,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_62,c_58,c_634])).

tff(c_643,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_642])).

tff(c_655,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_643,c_12])).

tff(c_667,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_74,c_58,c_79,c_655])).

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

tff(c_673,plain,(
    ! [B_9] :
      ( k2_funct_1('#skF_3') = B_9
      | k5_relat_1('#skF_3',B_9) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_9)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_667,c_75])).

tff(c_1906,plain,(
    ! [B_218] :
      ( k2_funct_1('#skF_3') = B_218
      | k5_relat_1('#skF_3',B_218) != k6_partfun1('#skF_1')
      | k1_relat_1(B_218) != '#skF_2'
      | ~ v1_funct_1(B_218)
      | ~ v1_relat_1(B_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_74,c_58,c_153,c_673])).

tff(c_1909,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_129,c_1906])).

tff(c_1918,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1815,c_1844,c_1909])).

tff(c_1920,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1918])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:42:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.84  
% 4.61/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.84  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.61/1.84  
% 4.61/1.84  %Foreground sorts:
% 4.61/1.84  
% 4.61/1.84  
% 4.61/1.84  %Background operators:
% 4.61/1.84  
% 4.61/1.84  
% 4.61/1.84  %Foreground operators:
% 4.61/1.84  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.61/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.61/1.84  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.61/1.84  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.61/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.61/1.84  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.61/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.61/1.84  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.61/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.61/1.84  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.61/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.61/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.61/1.84  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.61/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.61/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.61/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.61/1.84  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.61/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.61/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.61/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.61/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.61/1.84  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.61/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.61/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.61/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.61/1.84  
% 4.61/1.86  tff(f_202, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.61/1.86  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.61/1.86  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.61/1.86  tff(f_176, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 4.61/1.86  tff(f_105, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.61/1.86  tff(f_89, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.61/1.86  tff(f_115, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.61/1.86  tff(f_101, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.61/1.86  tff(f_134, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.61/1.86  tff(f_117, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.61/1.86  tff(f_33, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.61/1.86  tff(f_160, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 4.61/1.86  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.61/1.86  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 4.61/1.86  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 4.61/1.86  tff(c_52, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_202])).
% 4.61/1.86  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_202])).
% 4.61/1.86  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_202])).
% 4.61/1.86  tff(c_116, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.61/1.86  tff(c_129, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_116])).
% 4.61/1.86  tff(c_56, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_202])).
% 4.61/1.86  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_202])).
% 4.61/1.86  tff(c_140, plain, (![A_62, B_63, C_64]: (k2_relset_1(A_62, B_63, C_64)=k2_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.61/1.86  tff(c_154, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_140])).
% 4.61/1.86  tff(c_630, plain, (![A_146, C_147, B_148]: (k6_partfun1(A_146)=k5_relat_1(C_147, k2_funct_1(C_147)) | k1_xboole_0=B_148 | ~v2_funct_1(C_147) | k2_relset_1(A_146, B_148, C_147)!=B_148 | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_146, B_148))) | ~v1_funct_2(C_147, A_146, B_148) | ~v1_funct_1(C_147))), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.61/1.86  tff(c_636, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_630])).
% 4.61/1.86  tff(c_646, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_154, c_636])).
% 4.61/1.86  tff(c_647, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_56, c_646])).
% 4.61/1.86  tff(c_684, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_647])).
% 4.61/1.86  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 4.61/1.86  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_202])).
% 4.61/1.86  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_202])).
% 4.61/1.86  tff(c_32, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.61/1.86  tff(c_130, plain, (![A_59, B_60, D_61]: (r2_relset_1(A_59, B_60, D_61, D_61) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.61/1.86  tff(c_137, plain, (![A_26]: (r2_relset_1(A_26, A_26, k6_partfun1(A_26), k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_32, c_130])).
% 4.61/1.86  tff(c_281, plain, (![E_95, F_92, B_96, D_94, C_93, A_97]: (k1_partfun1(A_97, B_96, C_93, D_94, E_95, F_92)=k5_relat_1(E_95, F_92) | ~m1_subset_1(F_92, k1_zfmisc_1(k2_zfmisc_1(C_93, D_94))) | ~v1_funct_1(F_92) | ~m1_subset_1(E_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))) | ~v1_funct_1(E_95))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.61/1.86  tff(c_287, plain, (![A_97, B_96, E_95]: (k1_partfun1(A_97, B_96, '#skF_2', '#skF_1', E_95, '#skF_4')=k5_relat_1(E_95, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_96))) | ~v1_funct_1(E_95))), inference(resolution, [status(thm)], [c_64, c_281])).
% 4.61/1.86  tff(c_296, plain, (![A_99, B_100, E_101]: (k1_partfun1(A_99, B_100, '#skF_2', '#skF_1', E_101, '#skF_4')=k5_relat_1(E_101, '#skF_4') | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~v1_funct_1(E_101))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_287])).
% 4.61/1.86  tff(c_302, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_296])).
% 4.61/1.86  tff(c_309, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_302])).
% 4.61/1.86  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_202])).
% 4.61/1.86  tff(c_198, plain, (![D_71, C_72, A_73, B_74]: (D_71=C_72 | ~r2_relset_1(A_73, B_74, C_72, D_71) | ~m1_subset_1(D_71, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.61/1.86  tff(c_206, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_198])).
% 4.61/1.86  tff(c_221, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_206])).
% 4.61/1.86  tff(c_222, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_221])).
% 4.61/1.86  tff(c_314, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_222])).
% 4.61/1.86  tff(c_457, plain, (![B_115, D_116, C_114, E_117, A_118, F_119]: (m1_subset_1(k1_partfun1(A_118, B_115, C_114, D_116, E_117, F_119), k1_zfmisc_1(k2_zfmisc_1(A_118, D_116))) | ~m1_subset_1(F_119, k1_zfmisc_1(k2_zfmisc_1(C_114, D_116))) | ~v1_funct_1(F_119) | ~m1_subset_1(E_117, k1_zfmisc_1(k2_zfmisc_1(A_118, B_115))) | ~v1_funct_1(E_117))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.61/1.86  tff(c_497, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_309, c_457])).
% 4.61/1.86  tff(c_516, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_497])).
% 4.61/1.86  tff(c_518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_314, c_516])).
% 4.61/1.86  tff(c_519, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_221])).
% 4.61/1.86  tff(c_1119, plain, (![A_171, B_172, C_173, D_174]: (k2_relset_1(A_171, B_172, C_173)=B_172 | ~r2_relset_1(B_172, B_172, k1_partfun1(B_172, A_171, A_171, B_172, D_174, C_173), k6_partfun1(B_172)) | ~m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(B_172, A_171))) | ~v1_funct_2(D_174, B_172, A_171) | ~v1_funct_1(D_174) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))) | ~v1_funct_2(C_173, A_171, B_172) | ~v1_funct_1(C_173))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.61/1.86  tff(c_1125, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_519, c_1119])).
% 4.61/1.86  tff(c_1129, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_74, c_72, c_70, c_137, c_154, c_1125])).
% 4.61/1.86  tff(c_1131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_684, c_1129])).
% 4.61/1.86  tff(c_1132, plain, (~v2_funct_1('#skF_4') | k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_647])).
% 4.61/1.86  tff(c_1143, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1132])).
% 4.61/1.86  tff(c_36, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.61/1.86  tff(c_8, plain, (![A_2]: (v2_funct_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.61/1.86  tff(c_77, plain, (![A_2]: (v2_funct_1(k6_partfun1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8])).
% 4.61/1.86  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_202])).
% 4.61/1.86  tff(c_1777, plain, (![B_208, C_209, A_206, D_210, E_207]: (k1_xboole_0=C_209 | v2_funct_1(E_207) | k2_relset_1(A_206, B_208, D_210)!=B_208 | ~v2_funct_1(k1_partfun1(A_206, B_208, B_208, C_209, D_210, E_207)) | ~m1_subset_1(E_207, k1_zfmisc_1(k2_zfmisc_1(B_208, C_209))) | ~v1_funct_2(E_207, B_208, C_209) | ~v1_funct_1(E_207) | ~m1_subset_1(D_210, k1_zfmisc_1(k2_zfmisc_1(A_206, B_208))) | ~v1_funct_2(D_210, A_206, B_208) | ~v1_funct_1(D_210))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.61/1.86  tff(c_1783, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_519, c_1777])).
% 4.61/1.86  tff(c_1791, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_66, c_64, c_77, c_62, c_1783])).
% 4.61/1.86  tff(c_1793, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1143, c_56, c_1791])).
% 4.61/1.86  tff(c_1795, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1132])).
% 4.61/1.86  tff(c_4, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.61/1.86  tff(c_79, plain, (![A_1]: (k2_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4])).
% 4.61/1.86  tff(c_1794, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1132])).
% 4.61/1.86  tff(c_12, plain, (![A_6]: (k2_relat_1(k5_relat_1(A_6, k2_funct_1(A_6)))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.61/1.86  tff(c_1803, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1794, c_12])).
% 4.61/1.86  tff(c_1815, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_68, c_1795, c_79, c_1803])).
% 4.61/1.86  tff(c_584, plain, (![E_138, F_135, C_136, D_137, B_139, A_140]: (k1_partfun1(A_140, B_139, C_136, D_137, E_138, F_135)=k5_relat_1(E_138, F_135) | ~m1_subset_1(F_135, k1_zfmisc_1(k2_zfmisc_1(C_136, D_137))) | ~v1_funct_1(F_135) | ~m1_subset_1(E_138, k1_zfmisc_1(k2_zfmisc_1(A_140, B_139))) | ~v1_funct_1(E_138))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.61/1.86  tff(c_590, plain, (![A_140, B_139, E_138]: (k1_partfun1(A_140, B_139, '#skF_2', '#skF_1', E_138, '#skF_4')=k5_relat_1(E_138, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_138, k1_zfmisc_1(k2_zfmisc_1(A_140, B_139))) | ~v1_funct_1(E_138))), inference(resolution, [status(thm)], [c_64, c_584])).
% 4.61/1.86  tff(c_1831, plain, (![A_211, B_212, E_213]: (k1_partfun1(A_211, B_212, '#skF_2', '#skF_1', E_213, '#skF_4')=k5_relat_1(E_213, '#skF_4') | ~m1_subset_1(E_213, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))) | ~v1_funct_1(E_213))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_590])).
% 4.61/1.86  tff(c_1837, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_1831])).
% 4.61/1.86  tff(c_1844, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_519, c_1837])).
% 4.61/1.86  tff(c_128, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_116])).
% 4.61/1.86  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 4.61/1.86  tff(c_146, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_140])).
% 4.61/1.86  tff(c_153, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_146])).
% 4.61/1.86  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_202])).
% 4.61/1.86  tff(c_634, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_630])).
% 4.61/1.86  tff(c_642, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_62, c_58, c_634])).
% 4.61/1.86  tff(c_643, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_642])).
% 4.61/1.86  tff(c_655, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_643, c_12])).
% 4.61/1.86  tff(c_667, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_74, c_58, c_79, c_655])).
% 4.61/1.86  tff(c_16, plain, (![A_7, B_9]: (k2_funct_1(A_7)=B_9 | k6_relat_1(k1_relat_1(A_7))!=k5_relat_1(A_7, B_9) | k2_relat_1(A_7)!=k1_relat_1(B_9) | ~v2_funct_1(A_7) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.61/1.86  tff(c_75, plain, (![A_7, B_9]: (k2_funct_1(A_7)=B_9 | k6_partfun1(k1_relat_1(A_7))!=k5_relat_1(A_7, B_9) | k2_relat_1(A_7)!=k1_relat_1(B_9) | ~v2_funct_1(A_7) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_16])).
% 4.61/1.86  tff(c_673, plain, (![B_9]: (k2_funct_1('#skF_3')=B_9 | k5_relat_1('#skF_3', B_9)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_9) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_667, c_75])).
% 4.61/1.86  tff(c_1906, plain, (![B_218]: (k2_funct_1('#skF_3')=B_218 | k5_relat_1('#skF_3', B_218)!=k6_partfun1('#skF_1') | k1_relat_1(B_218)!='#skF_2' | ~v1_funct_1(B_218) | ~v1_relat_1(B_218))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_74, c_58, c_153, c_673])).
% 4.61/1.86  tff(c_1909, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_129, c_1906])).
% 4.61/1.86  tff(c_1918, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1815, c_1844, c_1909])).
% 4.61/1.86  tff(c_1920, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1918])).
% 4.61/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.86  
% 4.61/1.86  Inference rules
% 4.61/1.86  ----------------------
% 4.61/1.86  #Ref     : 0
% 4.61/1.86  #Sup     : 404
% 4.61/1.86  #Fact    : 0
% 4.61/1.86  #Define  : 0
% 4.61/1.86  #Split   : 14
% 4.61/1.86  #Chain   : 0
% 4.61/1.86  #Close   : 0
% 4.61/1.86  
% 4.61/1.86  Ordering : KBO
% 4.61/1.86  
% 4.61/1.86  Simplification rules
% 4.61/1.86  ----------------------
% 4.61/1.86  #Subsume      : 8
% 4.61/1.86  #Demod        : 460
% 4.61/1.86  #Tautology    : 133
% 4.61/1.86  #SimpNegUnit  : 44
% 4.61/1.86  #BackRed      : 14
% 4.61/1.86  
% 4.61/1.86  #Partial instantiations: 0
% 4.61/1.86  #Strategies tried      : 1
% 4.61/1.86  
% 4.61/1.86  Timing (in seconds)
% 4.61/1.86  ----------------------
% 4.61/1.86  Preprocessing        : 0.39
% 4.61/1.86  Parsing              : 0.20
% 4.61/1.86  CNF conversion       : 0.03
% 4.61/1.86  Main loop            : 0.70
% 4.61/1.86  Inferencing          : 0.23
% 4.61/1.86  Reduction            : 0.25
% 4.61/1.87  Demodulation         : 0.18
% 4.61/1.87  BG Simplification    : 0.04
% 4.61/1.87  Subsumption          : 0.13
% 4.61/1.87  Abstraction          : 0.04
% 4.61/1.87  MUC search           : 0.00
% 4.61/1.87  Cooper               : 0.00
% 4.61/1.87  Total                : 1.13
% 4.61/1.87  Index Insertion      : 0.00
% 4.61/1.87  Index Deletion       : 0.00
% 4.61/1.87  Index Matching       : 0.00
% 4.61/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
