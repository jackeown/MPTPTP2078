%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:05 EST 2020

% Result     : Theorem 6.94s
% Output     : CNFRefutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 422 expanded)
%              Number of leaves         :   45 ( 171 expanded)
%              Depth                    :   12
%              Number of atoms          :  318 (1779 expanded)
%              Number of equality atoms :  106 ( 576 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_212,negated_conjecture,(
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

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_127,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_49,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_186,axiom,(
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
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_115,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_125,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_111,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_144,axiom,(
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

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_170,axiom,(
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

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_45,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_149,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_161,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_149])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_162,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_149])).

tff(c_86,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_70,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_189,plain,(
    ! [A_70] :
      ( k4_relat_1(A_70) = k2_funct_1(A_70)
      | ~ v2_funct_1(A_70)
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_195,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_189])).

tff(c_201,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_86,c_195])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_211,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_2])).

tff(c_219,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_211])).

tff(c_48,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_10,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_92,plain,(
    ! [A_10] : k1_relat_1(k6_partfun1(A_10)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_84,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_74,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_1933,plain,(
    ! [A_162,C_163,B_164] :
      ( k6_partfun1(A_162) = k5_relat_1(C_163,k2_funct_1(C_163))
      | k1_xboole_0 = B_164
      | ~ v2_funct_1(C_163)
      | k2_relset_1(A_162,B_164,C_163) != B_164
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_162,B_164)))
      | ~ v1_funct_2(C_163,A_162,B_164)
      | ~ v1_funct_1(C_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_1939,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_1933])).

tff(c_1949,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_70,c_1939])).

tff(c_1950,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1949])).

tff(c_30,plain,(
    ! [A_16] :
      ( k1_relat_1(k5_relat_1(A_16,k2_funct_1(A_16))) = k1_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1960,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1950,c_30])).

tff(c_1971,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_86,c_70,c_92,c_1960])).

tff(c_4,plain,(
    ! [A_2] :
      ( k2_relat_1(k4_relat_1(A_2)) = k1_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k6_relat_1(k2_relat_1(A_12))) = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_234,plain,(
    ! [A_71] :
      ( k5_relat_1(A_71,k6_partfun1(k2_relat_1(A_71))) = A_71
      | ~ v1_relat_1(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_16])).

tff(c_246,plain,(
    ! [A_2] :
      ( k5_relat_1(k4_relat_1(A_2),k6_partfun1(k1_relat_1(A_2))) = k4_relat_1(A_2)
      | ~ v1_relat_1(k4_relat_1(A_2))
      | ~ v1_relat_1(A_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_234])).

tff(c_1988,plain,
    ( k5_relat_1(k4_relat_1('#skF_3'),k6_partfun1('#skF_1')) = k4_relat_1('#skF_3')
    | ~ v1_relat_1(k4_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1971,c_246])).

tff(c_1999,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_219,c_201,c_201,c_201,c_1988])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_78,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_1937,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_1933])).

tff(c_1945,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_1937])).

tff(c_1946,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1945])).

tff(c_2004,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1946])).

tff(c_44,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_256,plain,(
    ! [A_72,B_73,D_74] :
      ( r2_relset_1(A_72,B_73,D_74,D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_263,plain,(
    ! [A_30] : r2_relset_1(A_30,A_30,k6_partfun1(A_30),k6_partfun1(A_30)) ),
    inference(resolution,[status(thm)],[c_44,c_256])).

tff(c_1065,plain,(
    ! [A_112,F_113,D_109,C_114,E_111,B_110] :
      ( k1_partfun1(A_112,B_110,C_114,D_109,E_111,F_113) = k5_relat_1(E_111,F_113)
      | ~ m1_subset_1(F_113,k1_zfmisc_1(k2_zfmisc_1(C_114,D_109)))
      | ~ v1_funct_1(F_113)
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1(A_112,B_110)))
      | ~ v1_funct_1(E_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1069,plain,(
    ! [A_112,B_110,E_111] :
      ( k1_partfun1(A_112,B_110,'#skF_2','#skF_1',E_111,'#skF_4') = k5_relat_1(E_111,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_111,k1_zfmisc_1(k2_zfmisc_1(A_112,B_110)))
      | ~ v1_funct_1(E_111) ) ),
    inference(resolution,[status(thm)],[c_76,c_1065])).

tff(c_1096,plain,(
    ! [A_118,B_119,E_120] :
      ( k1_partfun1(A_118,B_119,'#skF_2','#skF_1',E_120,'#skF_4') = k5_relat_1(E_120,'#skF_4')
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ v1_funct_1(E_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1069])).

tff(c_1105,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_1096])).

tff(c_1112,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1105])).

tff(c_72,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_629,plain,(
    ! [D_90,C_91,A_92,B_93] :
      ( D_90 = C_91
      | ~ r2_relset_1(A_92,B_93,C_91,D_90)
      | ~ m1_subset_1(D_90,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_637,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_72,c_629])).

tff(c_652,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_637])).

tff(c_762,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_652])).

tff(c_1119,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1112,c_762])).

tff(c_1415,plain,(
    ! [B_133,C_132,F_135,D_137,E_134,A_136] :
      ( m1_subset_1(k1_partfun1(A_136,B_133,C_132,D_137,E_134,F_135),k1_zfmisc_1(k2_zfmisc_1(A_136,D_137)))
      | ~ m1_subset_1(F_135,k1_zfmisc_1(k2_zfmisc_1(C_132,D_137)))
      | ~ v1_funct_1(F_135)
      | ~ m1_subset_1(E_134,k1_zfmisc_1(k2_zfmisc_1(A_136,B_133)))
      | ~ v1_funct_1(E_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1443,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1112,c_1415])).

tff(c_1458,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_1443])).

tff(c_1460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1119,c_1458])).

tff(c_1461,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_652])).

tff(c_2913,plain,(
    ! [A_202,B_203,C_204,D_205] :
      ( k2_relset_1(A_202,B_203,C_204) = B_203
      | ~ r2_relset_1(B_203,B_203,k1_partfun1(B_203,A_202,A_202,B_203,D_205,C_204),k6_partfun1(B_203))
      | ~ m1_subset_1(D_205,k1_zfmisc_1(k2_zfmisc_1(B_203,A_202)))
      | ~ v1_funct_2(D_205,B_203,A_202)
      | ~ v1_funct_1(D_205)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203)))
      | ~ v1_funct_2(C_204,A_202,B_203)
      | ~ v1_funct_1(C_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2919,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1461,c_2913])).

tff(c_2923,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_86,c_84,c_82,c_263,c_2919])).

tff(c_2925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2004,c_2923])).

tff(c_2926,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1946])).

tff(c_2970,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2926])).

tff(c_26,plain,(
    ! [A_15] : v2_funct_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_87,plain,(
    ! [A_15] : v2_funct_1(k6_partfun1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_26])).

tff(c_4021,plain,(
    ! [B_250,D_248,C_247,E_246,A_249] :
      ( k1_xboole_0 = C_247
      | v2_funct_1(E_246)
      | k2_relset_1(A_249,B_250,D_248) != B_250
      | ~ v2_funct_1(k1_partfun1(A_249,B_250,B_250,C_247,D_248,E_246))
      | ~ m1_subset_1(E_246,k1_zfmisc_1(k2_zfmisc_1(B_250,C_247)))
      | ~ v1_funct_2(E_246,B_250,C_247)
      | ~ v1_funct_1(E_246)
      | ~ m1_subset_1(D_248,k1_zfmisc_1(k2_zfmisc_1(A_249,B_250)))
      | ~ v1_funct_2(D_248,A_249,B_250)
      | ~ v1_funct_1(D_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_4025,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1461,c_4021])).

tff(c_4030,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_78,c_76,c_87,c_74,c_4025])).

tff(c_4032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2970,c_68,c_4030])).

tff(c_4034,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2926])).

tff(c_4033,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2926])).

tff(c_4153,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4033,c_30])).

tff(c_4164,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_80,c_4034,c_92,c_4153])).

tff(c_14,plain,(
    ! [A_11] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_11)),A_11) = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_90,plain,(
    ! [A_11] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_11)),A_11) = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_14])).

tff(c_4181,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4164,c_90])).

tff(c_4191,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_4181])).

tff(c_1855,plain,(
    ! [B_152,A_154,D_151,F_155,C_156,E_153] :
      ( k1_partfun1(A_154,B_152,C_156,D_151,E_153,F_155) = k5_relat_1(E_153,F_155)
      | ~ m1_subset_1(F_155,k1_zfmisc_1(k2_zfmisc_1(C_156,D_151)))
      | ~ v1_funct_1(F_155)
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_154,B_152)))
      | ~ v1_funct_1(E_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1859,plain,(
    ! [A_154,B_152,E_153] :
      ( k1_partfun1(A_154,B_152,'#skF_2','#skF_1',E_153,'#skF_4') = k5_relat_1(E_153,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_154,B_152)))
      | ~ v1_funct_1(E_153) ) ),
    inference(resolution,[status(thm)],[c_76,c_1855])).

tff(c_4070,plain,(
    ! [A_251,B_252,E_253] :
      ( k1_partfun1(A_251,B_252,'#skF_2','#skF_1',E_253,'#skF_4') = k5_relat_1(E_253,'#skF_4')
      | ~ m1_subset_1(E_253,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252)))
      | ~ v1_funct_1(E_253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1859])).

tff(c_4079,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_4070])).

tff(c_4086,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1461,c_4079])).

tff(c_4193,plain,(
    ! [B_254,C_255,A_256] :
      ( k6_partfun1(B_254) = k5_relat_1(k2_funct_1(C_255),C_255)
      | k1_xboole_0 = B_254
      | ~ v2_funct_1(C_255)
      | k2_relset_1(A_256,B_254,C_255) != B_254
      | ~ m1_subset_1(C_255,k1_zfmisc_1(k2_zfmisc_1(A_256,B_254)))
      | ~ v1_funct_2(C_255,A_256,B_254)
      | ~ v1_funct_1(C_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_4199,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_4193])).

tff(c_4209,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_70,c_4199])).

tff(c_4210,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_4209])).

tff(c_8,plain,(
    ! [A_3,B_7,C_9] :
      ( k5_relat_1(k5_relat_1(A_3,B_7),C_9) = k5_relat_1(A_3,k5_relat_1(B_7,C_9))
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4274,plain,(
    ! [C_9] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_9)) = k5_relat_1(k6_partfun1('#skF_2'),C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4210,c_8])).

tff(c_5790,plain,(
    ! [C_301] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_301)) = k5_relat_1(k6_partfun1('#skF_2'),C_301)
      | ~ v1_relat_1(C_301) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_162,c_4274])).

tff(c_5856,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4086,c_5790])).

tff(c_5892,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_1999,c_4191,c_5856])).

tff(c_5894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5892])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:04:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.94/2.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.94/2.49  
% 6.94/2.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.49  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.31/2.49  
% 7.31/2.49  %Foreground sorts:
% 7.31/2.49  
% 7.31/2.49  
% 7.31/2.49  %Background operators:
% 7.31/2.49  
% 7.31/2.49  
% 7.31/2.49  %Foreground operators:
% 7.31/2.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.31/2.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.31/2.49  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.31/2.49  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.31/2.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.31/2.49  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.31/2.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.31/2.49  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.31/2.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.31/2.49  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.31/2.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.31/2.49  tff('#skF_2', type, '#skF_2': $i).
% 7.31/2.49  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.31/2.49  tff('#skF_3', type, '#skF_3': $i).
% 7.31/2.49  tff('#skF_1', type, '#skF_1': $i).
% 7.31/2.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.31/2.49  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.31/2.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.31/2.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.31/2.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.31/2.49  tff('#skF_4', type, '#skF_4': $i).
% 7.31/2.49  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.31/2.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.31/2.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.31/2.49  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 7.31/2.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.31/2.49  
% 7.31/2.52  tff(f_212, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 7.31/2.52  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.31/2.52  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 7.31/2.52  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 7.31/2.52  tff(f_127, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.31/2.52  tff(f_49, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.31/2.52  tff(f_186, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 7.31/2.52  tff(f_87, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 7.31/2.52  tff(f_35, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 7.31/2.52  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 7.31/2.52  tff(f_115, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.31/2.52  tff(f_99, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.31/2.52  tff(f_125, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.31/2.52  tff(f_111, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.31/2.52  tff(f_144, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.31/2.52  tff(f_77, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.31/2.52  tff(f_170, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 7.31/2.52  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 7.31/2.52  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 7.31/2.52  tff(c_64, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_212])).
% 7.31/2.52  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_212])).
% 7.31/2.52  tff(c_149, plain, (![C_65, A_66, B_67]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.31/2.52  tff(c_161, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_149])).
% 7.31/2.52  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_212])).
% 7.31/2.52  tff(c_162, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_149])).
% 7.31/2.52  tff(c_86, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 7.31/2.52  tff(c_70, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 7.31/2.52  tff(c_189, plain, (![A_70]: (k4_relat_1(A_70)=k2_funct_1(A_70) | ~v2_funct_1(A_70) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.31/2.52  tff(c_195, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_189])).
% 7.31/2.52  tff(c_201, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_86, c_195])).
% 7.31/2.52  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.31/2.52  tff(c_211, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_201, c_2])).
% 7.31/2.52  tff(c_219, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_211])).
% 7.31/2.52  tff(c_48, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.31/2.52  tff(c_10, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.31/2.52  tff(c_92, plain, (![A_10]: (k1_relat_1(k6_partfun1(A_10))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_10])).
% 7.31/2.52  tff(c_66, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_212])).
% 7.31/2.52  tff(c_84, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 7.31/2.52  tff(c_74, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_212])).
% 7.31/2.52  tff(c_1933, plain, (![A_162, C_163, B_164]: (k6_partfun1(A_162)=k5_relat_1(C_163, k2_funct_1(C_163)) | k1_xboole_0=B_164 | ~v2_funct_1(C_163) | k2_relset_1(A_162, B_164, C_163)!=B_164 | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_162, B_164))) | ~v1_funct_2(C_163, A_162, B_164) | ~v1_funct_1(C_163))), inference(cnfTransformation, [status(thm)], [f_186])).
% 7.31/2.52  tff(c_1939, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_1933])).
% 7.31/2.52  tff(c_1949, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_70, c_1939])).
% 7.31/2.52  tff(c_1950, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_1949])).
% 7.31/2.52  tff(c_30, plain, (![A_16]: (k1_relat_1(k5_relat_1(A_16, k2_funct_1(A_16)))=k1_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.31/2.52  tff(c_1960, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1950, c_30])).
% 7.31/2.52  tff(c_1971, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_86, c_70, c_92, c_1960])).
% 7.31/2.52  tff(c_4, plain, (![A_2]: (k2_relat_1(k4_relat_1(A_2))=k1_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.31/2.52  tff(c_16, plain, (![A_12]: (k5_relat_1(A_12, k6_relat_1(k2_relat_1(A_12)))=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.31/2.52  tff(c_234, plain, (![A_71]: (k5_relat_1(A_71, k6_partfun1(k2_relat_1(A_71)))=A_71 | ~v1_relat_1(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_16])).
% 7.31/2.52  tff(c_246, plain, (![A_2]: (k5_relat_1(k4_relat_1(A_2), k6_partfun1(k1_relat_1(A_2)))=k4_relat_1(A_2) | ~v1_relat_1(k4_relat_1(A_2)) | ~v1_relat_1(A_2))), inference(superposition, [status(thm), theory('equality')], [c_4, c_234])).
% 7.31/2.52  tff(c_1988, plain, (k5_relat_1(k4_relat_1('#skF_3'), k6_partfun1('#skF_1'))=k4_relat_1('#skF_3') | ~v1_relat_1(k4_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1971, c_246])).
% 7.31/2.52  tff(c_1999, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_219, c_201, c_201, c_201, c_1988])).
% 7.31/2.52  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_212])).
% 7.31/2.52  tff(c_68, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_212])).
% 7.31/2.52  tff(c_78, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_212])).
% 7.31/2.52  tff(c_1937, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_1933])).
% 7.31/2.52  tff(c_1945, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_1937])).
% 7.31/2.52  tff(c_1946, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_68, c_1945])).
% 7.31/2.52  tff(c_2004, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1946])).
% 7.31/2.52  tff(c_44, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.31/2.52  tff(c_256, plain, (![A_72, B_73, D_74]: (r2_relset_1(A_72, B_73, D_74, D_74) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.31/2.52  tff(c_263, plain, (![A_30]: (r2_relset_1(A_30, A_30, k6_partfun1(A_30), k6_partfun1(A_30)))), inference(resolution, [status(thm)], [c_44, c_256])).
% 7.31/2.52  tff(c_1065, plain, (![A_112, F_113, D_109, C_114, E_111, B_110]: (k1_partfun1(A_112, B_110, C_114, D_109, E_111, F_113)=k5_relat_1(E_111, F_113) | ~m1_subset_1(F_113, k1_zfmisc_1(k2_zfmisc_1(C_114, D_109))) | ~v1_funct_1(F_113) | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1(A_112, B_110))) | ~v1_funct_1(E_111))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.31/2.52  tff(c_1069, plain, (![A_112, B_110, E_111]: (k1_partfun1(A_112, B_110, '#skF_2', '#skF_1', E_111, '#skF_4')=k5_relat_1(E_111, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_111, k1_zfmisc_1(k2_zfmisc_1(A_112, B_110))) | ~v1_funct_1(E_111))), inference(resolution, [status(thm)], [c_76, c_1065])).
% 7.31/2.52  tff(c_1096, plain, (![A_118, B_119, E_120]: (k1_partfun1(A_118, B_119, '#skF_2', '#skF_1', E_120, '#skF_4')=k5_relat_1(E_120, '#skF_4') | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))) | ~v1_funct_1(E_120))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1069])).
% 7.31/2.52  tff(c_1105, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_1096])).
% 7.31/2.52  tff(c_1112, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1105])).
% 7.31/2.52  tff(c_72, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_212])).
% 7.31/2.52  tff(c_629, plain, (![D_90, C_91, A_92, B_93]: (D_90=C_91 | ~r2_relset_1(A_92, B_93, C_91, D_90) | ~m1_subset_1(D_90, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.31/2.52  tff(c_637, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_72, c_629])).
% 7.31/2.52  tff(c_652, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_637])).
% 7.31/2.52  tff(c_762, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_652])).
% 7.31/2.52  tff(c_1119, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1112, c_762])).
% 7.31/2.52  tff(c_1415, plain, (![B_133, C_132, F_135, D_137, E_134, A_136]: (m1_subset_1(k1_partfun1(A_136, B_133, C_132, D_137, E_134, F_135), k1_zfmisc_1(k2_zfmisc_1(A_136, D_137))) | ~m1_subset_1(F_135, k1_zfmisc_1(k2_zfmisc_1(C_132, D_137))) | ~v1_funct_1(F_135) | ~m1_subset_1(E_134, k1_zfmisc_1(k2_zfmisc_1(A_136, B_133))) | ~v1_funct_1(E_134))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.31/2.52  tff(c_1443, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1112, c_1415])).
% 7.31/2.52  tff(c_1458, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_1443])).
% 7.31/2.52  tff(c_1460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1119, c_1458])).
% 7.31/2.52  tff(c_1461, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_652])).
% 7.31/2.52  tff(c_2913, plain, (![A_202, B_203, C_204, D_205]: (k2_relset_1(A_202, B_203, C_204)=B_203 | ~r2_relset_1(B_203, B_203, k1_partfun1(B_203, A_202, A_202, B_203, D_205, C_204), k6_partfun1(B_203)) | ~m1_subset_1(D_205, k1_zfmisc_1(k2_zfmisc_1(B_203, A_202))) | ~v1_funct_2(D_205, B_203, A_202) | ~v1_funct_1(D_205) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))) | ~v1_funct_2(C_204, A_202, B_203) | ~v1_funct_1(C_204))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.31/2.52  tff(c_2919, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1461, c_2913])).
% 7.31/2.52  tff(c_2923, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_86, c_84, c_82, c_263, c_2919])).
% 7.31/2.52  tff(c_2925, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2004, c_2923])).
% 7.31/2.52  tff(c_2926, plain, (~v2_funct_1('#skF_4') | k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1946])).
% 7.31/2.52  tff(c_2970, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2926])).
% 7.31/2.52  tff(c_26, plain, (![A_15]: (v2_funct_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.31/2.52  tff(c_87, plain, (![A_15]: (v2_funct_1(k6_partfun1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_26])).
% 7.31/2.52  tff(c_4021, plain, (![B_250, D_248, C_247, E_246, A_249]: (k1_xboole_0=C_247 | v2_funct_1(E_246) | k2_relset_1(A_249, B_250, D_248)!=B_250 | ~v2_funct_1(k1_partfun1(A_249, B_250, B_250, C_247, D_248, E_246)) | ~m1_subset_1(E_246, k1_zfmisc_1(k2_zfmisc_1(B_250, C_247))) | ~v1_funct_2(E_246, B_250, C_247) | ~v1_funct_1(E_246) | ~m1_subset_1(D_248, k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))) | ~v1_funct_2(D_248, A_249, B_250) | ~v1_funct_1(D_248))), inference(cnfTransformation, [status(thm)], [f_170])).
% 7.31/2.52  tff(c_4025, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1461, c_4021])).
% 7.31/2.52  tff(c_4030, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_80, c_78, c_76, c_87, c_74, c_4025])).
% 7.31/2.52  tff(c_4032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2970, c_68, c_4030])).
% 7.31/2.52  tff(c_4034, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2926])).
% 7.31/2.52  tff(c_4033, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2926])).
% 7.31/2.52  tff(c_4153, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4033, c_30])).
% 7.31/2.52  tff(c_4164, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_161, c_80, c_4034, c_92, c_4153])).
% 7.31/2.52  tff(c_14, plain, (![A_11]: (k5_relat_1(k6_relat_1(k1_relat_1(A_11)), A_11)=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.31/2.52  tff(c_90, plain, (![A_11]: (k5_relat_1(k6_partfun1(k1_relat_1(A_11)), A_11)=A_11 | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_14])).
% 7.31/2.52  tff(c_4181, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4164, c_90])).
% 7.31/2.52  tff(c_4191, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_161, c_4181])).
% 7.31/2.52  tff(c_1855, plain, (![B_152, A_154, D_151, F_155, C_156, E_153]: (k1_partfun1(A_154, B_152, C_156, D_151, E_153, F_155)=k5_relat_1(E_153, F_155) | ~m1_subset_1(F_155, k1_zfmisc_1(k2_zfmisc_1(C_156, D_151))) | ~v1_funct_1(F_155) | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_154, B_152))) | ~v1_funct_1(E_153))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.31/2.52  tff(c_1859, plain, (![A_154, B_152, E_153]: (k1_partfun1(A_154, B_152, '#skF_2', '#skF_1', E_153, '#skF_4')=k5_relat_1(E_153, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_154, B_152))) | ~v1_funct_1(E_153))), inference(resolution, [status(thm)], [c_76, c_1855])).
% 7.31/2.52  tff(c_4070, plain, (![A_251, B_252, E_253]: (k1_partfun1(A_251, B_252, '#skF_2', '#skF_1', E_253, '#skF_4')=k5_relat_1(E_253, '#skF_4') | ~m1_subset_1(E_253, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))) | ~v1_funct_1(E_253))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1859])).
% 7.31/2.52  tff(c_4079, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_4070])).
% 7.31/2.52  tff(c_4086, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1461, c_4079])).
% 7.31/2.52  tff(c_4193, plain, (![B_254, C_255, A_256]: (k6_partfun1(B_254)=k5_relat_1(k2_funct_1(C_255), C_255) | k1_xboole_0=B_254 | ~v2_funct_1(C_255) | k2_relset_1(A_256, B_254, C_255)!=B_254 | ~m1_subset_1(C_255, k1_zfmisc_1(k2_zfmisc_1(A_256, B_254))) | ~v1_funct_2(C_255, A_256, B_254) | ~v1_funct_1(C_255))), inference(cnfTransformation, [status(thm)], [f_186])).
% 7.31/2.52  tff(c_4199, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_4193])).
% 7.31/2.52  tff(c_4209, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_70, c_4199])).
% 7.31/2.52  tff(c_4210, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_66, c_4209])).
% 7.31/2.52  tff(c_8, plain, (![A_3, B_7, C_9]: (k5_relat_1(k5_relat_1(A_3, B_7), C_9)=k5_relat_1(A_3, k5_relat_1(B_7, C_9)) | ~v1_relat_1(C_9) | ~v1_relat_1(B_7) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.31/2.52  tff(c_4274, plain, (![C_9]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_9))=k5_relat_1(k6_partfun1('#skF_2'), C_9) | ~v1_relat_1(C_9) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4210, c_8])).
% 7.31/2.52  tff(c_5790, plain, (![C_301]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_301))=k5_relat_1(k6_partfun1('#skF_2'), C_301) | ~v1_relat_1(C_301))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_162, c_4274])).
% 7.31/2.52  tff(c_5856, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4086, c_5790])).
% 7.31/2.52  tff(c_5892, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_161, c_1999, c_4191, c_5856])).
% 7.31/2.52  tff(c_5894, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_5892])).
% 7.31/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.52  
% 7.31/2.52  Inference rules
% 7.31/2.52  ----------------------
% 7.31/2.52  #Ref     : 0
% 7.31/2.52  #Sup     : 1263
% 7.31/2.52  #Fact    : 0
% 7.31/2.52  #Define  : 0
% 7.31/2.52  #Split   : 12
% 7.31/2.52  #Chain   : 0
% 7.31/2.52  #Close   : 0
% 7.31/2.52  
% 7.31/2.52  Ordering : KBO
% 7.31/2.52  
% 7.31/2.52  Simplification rules
% 7.31/2.52  ----------------------
% 7.31/2.52  #Subsume      : 29
% 7.31/2.52  #Demod        : 2084
% 7.31/2.52  #Tautology    : 677
% 7.31/2.52  #SimpNegUnit  : 45
% 7.31/2.52  #BackRed      : 30
% 7.31/2.52  
% 7.31/2.52  #Partial instantiations: 0
% 7.31/2.52  #Strategies tried      : 1
% 7.31/2.52  
% 7.31/2.52  Timing (in seconds)
% 7.31/2.52  ----------------------
% 7.31/2.52  Preprocessing        : 0.41
% 7.31/2.52  Parsing              : 0.22
% 7.31/2.52  CNF conversion       : 0.03
% 7.31/2.52  Main loop            : 1.27
% 7.31/2.52  Inferencing          : 0.42
% 7.31/2.52  Reduction            : 0.51
% 7.31/2.52  Demodulation         : 0.39
% 7.31/2.52  BG Simplification    : 0.05
% 7.31/2.52  Subsumption          : 0.20
% 7.31/2.52  Abstraction          : 0.06
% 7.31/2.52  MUC search           : 0.00
% 7.31/2.52  Cooper               : 0.00
% 7.31/2.52  Total                : 1.73
% 7.31/2.52  Index Insertion      : 0.00
% 7.31/2.52  Index Deletion       : 0.00
% 7.31/2.52  Index Matching       : 0.00
% 7.31/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
