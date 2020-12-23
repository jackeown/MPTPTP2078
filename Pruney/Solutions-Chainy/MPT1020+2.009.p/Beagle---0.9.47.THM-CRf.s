%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:51 EST 2020

% Result     : Theorem 21.45s
% Output     : CNFRefutation 21.45s
% Verified   : 
% Statistics : Number of formulae       :  184 (2002 expanded)
%              Number of leaves         :   44 ( 786 expanded)
%              Depth                    :   16
%              Number of atoms          :  437 (8841 expanded)
%              Number of equality atoms :  100 ( 497 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_185,negated_conjecture,(
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

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_163,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_71,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_161,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_137,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_121,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_141,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_151,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_156,plain,(
    ! [A_65,B_66,D_67] :
      ( r2_relset_1(A_65,B_66,D_67,D_67)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_165,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_156])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_92,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_104,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_92])).

tff(c_141,plain,(
    ! [C_60,B_61,A_62] :
      ( v5_relat_1(C_60,B_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_62,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_153,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_141])).

tff(c_179,plain,(
    ! [B_70,A_71] :
      ( k2_relat_1(B_70) = A_71
      | ~ v2_funct_2(B_70,A_71)
      | ~ v5_relat_1(B_70,A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_185,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_153,c_179])).

tff(c_194,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_185])).

tff(c_198,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_64,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_318,plain,(
    ! [C_89,B_90,A_91] :
      ( v2_funct_2(C_89,B_90)
      | ~ v3_funct_2(C_89,A_91,B_90)
      | ~ v1_funct_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_327,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_318])).

tff(c_334,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_327])).

tff(c_336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_334])).

tff(c_337,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_70,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_103,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_92])).

tff(c_76,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_72,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_452,plain,(
    ! [C_107,A_108,B_109] :
      ( v2_funct_1(C_107)
      | ~ v3_funct_2(C_107,A_108,B_109)
      | ~ v1_funct_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_458,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_452])).

tff(c_465,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_458])).

tff(c_152,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_141])).

tff(c_188,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_152,c_179])).

tff(c_197,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_188])).

tff(c_349,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_396,plain,(
    ! [C_100,B_101,A_102] :
      ( v2_funct_2(C_100,B_101)
      | ~ v3_funct_2(C_100,A_102,B_101)
      | ~ v1_funct_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_102,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_402,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_396])).

tff(c_409,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_402])).

tff(c_411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_349,c_409])).

tff(c_412,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_56,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_14,plain,(
    ! [A_8,B_10] :
      ( k2_funct_1(A_8) = B_10
      | k6_relat_1(k2_relat_1(A_8)) != k5_relat_1(B_10,A_8)
      | k2_relat_1(B_10) != k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1098,plain,(
    ! [A_171,B_172] :
      ( k2_funct_1(A_171) = B_172
      | k6_partfun1(k2_relat_1(A_171)) != k5_relat_1(B_172,A_171)
      | k2_relat_1(B_172) != k1_relat_1(A_171)
      | ~ v2_funct_1(A_171)
      | ~ v1_funct_1(B_172)
      | ~ v1_relat_1(B_172)
      | ~ v1_funct_1(A_171)
      | ~ v1_relat_1(A_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_14])).

tff(c_1104,plain,(
    ! [B_172] :
      ( k2_funct_1('#skF_2') = B_172
      | k5_relat_1(B_172,'#skF_2') != k6_partfun1('#skF_1')
      | k2_relat_1(B_172) != k1_relat_1('#skF_2')
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1(B_172)
      | ~ v1_relat_1(B_172)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_1098])).

tff(c_1115,plain,(
    ! [B_173] :
      ( k2_funct_1('#skF_2') = B_173
      | k5_relat_1(B_173,'#skF_2') != k6_partfun1('#skF_1')
      | k2_relat_1(B_173) != k1_relat_1('#skF_2')
      | ~ v1_funct_1(B_173)
      | ~ v1_relat_1(B_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_76,c_465,c_1104])).

tff(c_1121,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_2') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_104,c_1115])).

tff(c_1131,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_2') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_337,c_1121])).

tff(c_1252,plain,(
    k1_relat_1('#skF_2') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1131])).

tff(c_74,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_529,plain,(
    ! [A_121,B_122] :
      ( k2_funct_2(A_121,B_122) = k2_funct_1(B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(k2_zfmisc_1(A_121,A_121)))
      | ~ v3_funct_2(B_122,A_121,A_121)
      | ~ v1_funct_2(B_122,A_121,A_121)
      | ~ v1_funct_1(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_535,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_529])).

tff(c_542,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_535])).

tff(c_512,plain,(
    ! [A_119,B_120] :
      ( v1_funct_1(k2_funct_2(A_119,B_120))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k2_zfmisc_1(A_119,A_119)))
      | ~ v3_funct_2(B_120,A_119,A_119)
      | ~ v1_funct_2(B_120,A_119,A_119)
      | ~ v1_funct_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_518,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_2'))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_512])).

tff(c_525,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_518])).

tff(c_551,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_525])).

tff(c_559,plain,(
    ! [A_125,B_126] :
      ( v3_funct_2(k2_funct_2(A_125,B_126),A_125,A_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(k2_zfmisc_1(A_125,A_125)))
      | ~ v3_funct_2(B_126,A_125,A_125)
      | ~ v1_funct_2(B_126,A_125,A_125)
      | ~ v1_funct_1(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_563,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_2'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_559])).

tff(c_569,plain,(
    v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_542,c_563])).

tff(c_1136,plain,(
    ! [A_174,B_175] :
      ( m1_subset_1(k2_funct_2(A_174,B_175),k1_zfmisc_1(k2_zfmisc_1(A_174,A_174)))
      | ~ m1_subset_1(B_175,k1_zfmisc_1(k2_zfmisc_1(A_174,A_174)))
      | ~ v3_funct_2(B_175,A_174,A_174)
      | ~ v1_funct_2(B_175,A_174,A_174)
      | ~ v1_funct_1(B_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1169,plain,
    ( m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_1136])).

tff(c_1187,plain,(
    m1_subset_1(k2_funct_1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_1169])).

tff(c_26,plain,(
    ! [C_23,B_22,A_21] :
      ( v2_funct_2(C_23,B_22)
      | ~ v3_funct_2(C_23,A_21,B_22)
      | ~ v1_funct_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1202,plain,
    ( v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_2'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1187,c_26])).

tff(c_1234,plain,(
    v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_569,c_1202])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1216,plain,
    ( v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1187,c_2])).

tff(c_1243,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1216])).

tff(c_18,plain,(
    ! [C_16,B_15,A_14] :
      ( v5_relat_1(C_16,B_15)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1239,plain,(
    v5_relat_1(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1187,c_18])).

tff(c_34,plain,(
    ! [B_25,A_24] :
      ( k2_relat_1(B_25) = A_24
      | ~ v2_funct_2(B_25,A_24)
      | ~ v5_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1256,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1239,c_34])).

tff(c_1259,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1243,c_1256])).

tff(c_1626,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_1259])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_relat_1(k2_funct_1(A_6)) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1635,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1626,c_6])).

tff(c_1649,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_76,c_465,c_1635])).

tff(c_1651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1252,c_1649])).

tff(c_1652,plain,
    ( k5_relat_1('#skF_3','#skF_2') != k6_partfun1('#skF_1')
    | k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1131])).

tff(c_2334,plain,(
    k5_relat_1('#skF_3','#skF_2') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1652])).

tff(c_1009,plain,(
    ! [A_163,E_166,C_165,D_161,B_162,F_164] :
      ( m1_subset_1(k1_partfun1(A_163,B_162,C_165,D_161,E_166,F_164),k1_zfmisc_1(k2_zfmisc_1(A_163,D_161)))
      | ~ m1_subset_1(F_164,k1_zfmisc_1(k2_zfmisc_1(C_165,D_161)))
      | ~ v1_funct_1(F_164)
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(A_163,B_162)))
      | ~ v1_funct_1(E_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_50,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_488,plain,(
    ! [D_115,C_116,A_117,B_118] :
      ( D_115 = C_116
      | ~ r2_relset_1(A_117,B_118,C_116,D_115)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_496,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_488])).

tff(c_511,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_496])).

tff(c_574,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_511])).

tff(c_1028,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1009,c_574])).

tff(c_1069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70,c_68,c_62,c_1028])).

tff(c_1070,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_511])).

tff(c_1782,plain,(
    ! [D_216,F_213,B_217,C_214,A_212,E_215] :
      ( k1_partfun1(A_212,B_217,C_214,D_216,E_215,F_213) = k5_relat_1(E_215,F_213)
      | ~ m1_subset_1(F_213,k1_zfmisc_1(k2_zfmisc_1(C_214,D_216)))
      | ~ v1_funct_1(F_213)
      | ~ m1_subset_1(E_215,k1_zfmisc_1(k2_zfmisc_1(A_212,B_217)))
      | ~ v1_funct_1(E_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1794,plain,(
    ! [A_212,B_217,E_215] :
      ( k1_partfun1(A_212,B_217,'#skF_1','#skF_1',E_215,'#skF_3') = k5_relat_1(E_215,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_215,k1_zfmisc_1(k2_zfmisc_1(A_212,B_217)))
      | ~ v1_funct_1(E_215) ) ),
    inference(resolution,[status(thm)],[c_62,c_1782])).

tff(c_2061,plain,(
    ! [A_227,B_228,E_229] :
      ( k1_partfun1(A_227,B_228,'#skF_1','#skF_1',E_229,'#skF_3') = k5_relat_1(E_229,'#skF_3')
      | ~ m1_subset_1(E_229,k1_zfmisc_1(k2_zfmisc_1(A_227,B_228)))
      | ~ v1_funct_1(E_229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1794])).

tff(c_2082,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3') = k5_relat_1('#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_2061])).

tff(c_2100,plain,(
    k5_relat_1('#skF_2','#skF_3') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1070,c_2082])).

tff(c_461,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_452])).

tff(c_468,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_461])).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_538,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_529])).

tff(c_545,plain,(
    k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_538])).

tff(c_1172,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_1136])).

tff(c_1189,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_1172])).

tff(c_1746,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1189,c_2])).

tff(c_1779,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1746])).

tff(c_521,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_512])).

tff(c_528,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_521])).

tff(c_546,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_528])).

tff(c_565,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_3'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_559])).

tff(c_572,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_545,c_565])).

tff(c_1732,plain,
    ( v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1189,c_26])).

tff(c_1770,plain,(
    v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_572,c_1732])).

tff(c_1775,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1189,c_18])).

tff(c_1811,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1775,c_34])).

tff(c_1814,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1779,c_1770,c_1811])).

tff(c_1823,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1814,c_6])).

tff(c_1837,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_68,c_468,c_1823])).

tff(c_1106,plain,(
    ! [B_172] :
      ( k2_funct_1('#skF_3') = B_172
      | k5_relat_1(B_172,'#skF_3') != k6_partfun1('#skF_1')
      | k2_relat_1(B_172) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_172)
      | ~ v1_relat_1(B_172)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_1098])).

tff(c_1114,plain,(
    ! [B_172] :
      ( k2_funct_1('#skF_3') = B_172
      | k5_relat_1(B_172,'#skF_3') != k6_partfun1('#skF_1')
      | k2_relat_1(B_172) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_172)
      | ~ v1_relat_1(B_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_68,c_468,c_1106])).

tff(c_29021,plain,(
    ! [B_828] :
      ( k2_funct_1('#skF_3') = B_828
      | k5_relat_1(B_828,'#skF_3') != k6_partfun1('#skF_1')
      | k2_relat_1(B_828) != '#skF_1'
      | ~ v1_funct_1(B_828)
      | ~ v1_relat_1(B_828) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1837,c_1114])).

tff(c_29324,plain,
    ( k2_funct_1('#skF_3') = '#skF_2'
    | k5_relat_1('#skF_2','#skF_3') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_2') != '#skF_1'
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_103,c_29021])).

tff(c_29563,plain,(
    k2_funct_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_412,c_2100,c_29324])).

tff(c_28,plain,(
    ! [C_23,A_21,B_22] :
      ( v2_funct_1(C_23)
      | ~ v3_funct_2(C_23,A_21,B_22)
      | ~ v1_funct_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1735,plain,
    ( v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1189,c_28])).

tff(c_1773,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_572,c_1735])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_relat_1(k2_funct_1(A_6)) = k2_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_relat_1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_78,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_partfun1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_12])).

tff(c_4058,plain,(
    ! [A_300] :
      ( k2_funct_1(k2_funct_1(A_300)) = A_300
      | k6_partfun1(k2_relat_1(k2_funct_1(A_300))) != k6_partfun1(k1_relat_1(A_300))
      | k1_relat_1(k2_funct_1(A_300)) != k2_relat_1(A_300)
      | ~ v2_funct_1(k2_funct_1(A_300))
      | ~ v1_funct_1(A_300)
      | ~ v1_relat_1(A_300)
      | ~ v1_funct_1(k2_funct_1(A_300))
      | ~ v1_relat_1(k2_funct_1(A_300))
      | ~ v2_funct_1(A_300)
      | ~ v1_funct_1(A_300)
      | ~ v1_relat_1(A_300) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_1098])).

tff(c_4064,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | k6_partfun1(k1_relat_1('#skF_3')) != k6_partfun1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1814,c_4058])).

tff(c_4071,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_68,c_468,c_1779,c_546,c_104,c_68,c_1773,c_337,c_1837,c_4064])).

tff(c_4258,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4071])).

tff(c_4292,plain,
    ( k2_relat_1('#skF_3') != '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_4258])).

tff(c_4295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_68,c_468,c_337,c_4292])).

tff(c_4296,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4071])).

tff(c_10,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_relat_1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_79,plain,(
    ! [A_7] :
      ( k5_relat_1(k2_funct_1(A_7),A_7) = k6_partfun1(k2_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_10])).

tff(c_4365,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4296,c_79])).

tff(c_4386,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1779,c_546,c_1773,c_1814,c_4365])).

tff(c_29656,plain,(
    k5_relat_1('#skF_3','#skF_2') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29563,c_4386])).

tff(c_29744,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2334,c_29656])).

tff(c_29745,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1652])).

tff(c_58,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_552,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_58])).

tff(c_29768,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29745,c_552])).

tff(c_29794,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_29768])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:51:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.45/12.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.45/12.74  
% 21.45/12.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.45/12.74  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 21.45/12.74  
% 21.45/12.74  %Foreground sorts:
% 21.45/12.74  
% 21.45/12.74  
% 21.45/12.74  %Background operators:
% 21.45/12.74  
% 21.45/12.74  
% 21.45/12.74  %Foreground operators:
% 21.45/12.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 21.45/12.74  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 21.45/12.74  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 21.45/12.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.45/12.74  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 21.45/12.74  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 21.45/12.74  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 21.45/12.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 21.45/12.74  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 21.45/12.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 21.45/12.74  tff('#skF_2', type, '#skF_2': $i).
% 21.45/12.74  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 21.45/12.74  tff('#skF_3', type, '#skF_3': $i).
% 21.45/12.74  tff('#skF_1', type, '#skF_1': $i).
% 21.45/12.74  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 21.45/12.74  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 21.45/12.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.45/12.74  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 21.45/12.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.45/12.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 21.45/12.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 21.45/12.74  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 21.45/12.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.45/12.74  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 21.45/12.74  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 21.45/12.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 21.45/12.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.45/12.74  
% 21.45/12.77  tff(f_185, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 21.45/12.77  tff(f_89, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 21.45/12.77  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 21.45/12.77  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 21.45/12.77  tff(f_109, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 21.45/12.77  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 21.45/12.77  tff(f_163, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 21.45/12.77  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 21.45/12.77  tff(f_161, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 21.45/12.77  tff(f_137, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 21.45/12.77  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 21.45/12.77  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 21.45/12.77  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 21.45/12.77  tff(f_121, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 21.45/12.77  tff(f_141, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 21.45/12.77  tff(f_151, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 21.45/12.77  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 21.45/12.77  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_185])).
% 21.45/12.77  tff(c_156, plain, (![A_65, B_66, D_67]: (r2_relset_1(A_65, B_66, D_67, D_67) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 21.45/12.77  tff(c_165, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_156])).
% 21.45/12.77  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_185])).
% 21.45/12.77  tff(c_92, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 21.45/12.77  tff(c_104, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_92])).
% 21.45/12.77  tff(c_141, plain, (![C_60, B_61, A_62]: (v5_relat_1(C_60, B_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_62, B_61))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 21.45/12.77  tff(c_153, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_141])).
% 21.45/12.77  tff(c_179, plain, (![B_70, A_71]: (k2_relat_1(B_70)=A_71 | ~v2_funct_2(B_70, A_71) | ~v5_relat_1(B_70, A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_109])).
% 21.45/12.77  tff(c_185, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_153, c_179])).
% 21.45/12.77  tff(c_194, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_185])).
% 21.45/12.77  tff(c_198, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_194])).
% 21.45/12.77  tff(c_64, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 21.45/12.77  tff(c_318, plain, (![C_89, B_90, A_91]: (v2_funct_2(C_89, B_90) | ~v3_funct_2(C_89, A_91, B_90) | ~v1_funct_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 21.45/12.77  tff(c_327, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_318])).
% 21.45/12.77  tff(c_334, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_327])).
% 21.45/12.77  tff(c_336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_198, c_334])).
% 21.45/12.77  tff(c_337, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_194])).
% 21.45/12.77  tff(c_70, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_185])).
% 21.45/12.77  tff(c_103, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_92])).
% 21.45/12.77  tff(c_76, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_185])).
% 21.45/12.77  tff(c_72, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 21.45/12.77  tff(c_452, plain, (![C_107, A_108, B_109]: (v2_funct_1(C_107) | ~v3_funct_2(C_107, A_108, B_109) | ~v1_funct_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 21.45/12.77  tff(c_458, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_452])).
% 21.45/12.77  tff(c_465, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_458])).
% 21.45/12.77  tff(c_152, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_141])).
% 21.45/12.77  tff(c_188, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_152, c_179])).
% 21.45/12.77  tff(c_197, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_188])).
% 21.45/12.77  tff(c_349, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_197])).
% 21.45/12.77  tff(c_396, plain, (![C_100, B_101, A_102]: (v2_funct_2(C_100, B_101) | ~v3_funct_2(C_100, A_102, B_101) | ~v1_funct_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_102, B_101))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 21.45/12.77  tff(c_402, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_396])).
% 21.45/12.77  tff(c_409, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_402])).
% 21.45/12.77  tff(c_411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_349, c_409])).
% 21.45/12.77  tff(c_412, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_197])).
% 21.45/12.77  tff(c_56, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_163])).
% 21.45/12.77  tff(c_14, plain, (![A_8, B_10]: (k2_funct_1(A_8)=B_10 | k6_relat_1(k2_relat_1(A_8))!=k5_relat_1(B_10, A_8) | k2_relat_1(B_10)!=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_71])).
% 21.45/12.77  tff(c_1098, plain, (![A_171, B_172]: (k2_funct_1(A_171)=B_172 | k6_partfun1(k2_relat_1(A_171))!=k5_relat_1(B_172, A_171) | k2_relat_1(B_172)!=k1_relat_1(A_171) | ~v2_funct_1(A_171) | ~v1_funct_1(B_172) | ~v1_relat_1(B_172) | ~v1_funct_1(A_171) | ~v1_relat_1(A_171))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_14])).
% 21.45/12.77  tff(c_1104, plain, (![B_172]: (k2_funct_1('#skF_2')=B_172 | k5_relat_1(B_172, '#skF_2')!=k6_partfun1('#skF_1') | k2_relat_1(B_172)!=k1_relat_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1(B_172) | ~v1_relat_1(B_172) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_412, c_1098])).
% 21.45/12.77  tff(c_1115, plain, (![B_173]: (k2_funct_1('#skF_2')=B_173 | k5_relat_1(B_173, '#skF_2')!=k6_partfun1('#skF_1') | k2_relat_1(B_173)!=k1_relat_1('#skF_2') | ~v1_funct_1(B_173) | ~v1_relat_1(B_173))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_76, c_465, c_1104])).
% 21.45/12.77  tff(c_1121, plain, (k2_funct_1('#skF_2')='#skF_3' | k5_relat_1('#skF_3', '#skF_2')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_104, c_1115])).
% 21.45/12.77  tff(c_1131, plain, (k2_funct_1('#skF_2')='#skF_3' | k5_relat_1('#skF_3', '#skF_2')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_337, c_1121])).
% 21.45/12.77  tff(c_1252, plain, (k1_relat_1('#skF_2')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1131])).
% 21.45/12.77  tff(c_74, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 21.45/12.77  tff(c_529, plain, (![A_121, B_122]: (k2_funct_2(A_121, B_122)=k2_funct_1(B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(k2_zfmisc_1(A_121, A_121))) | ~v3_funct_2(B_122, A_121, A_121) | ~v1_funct_2(B_122, A_121, A_121) | ~v1_funct_1(B_122))), inference(cnfTransformation, [status(thm)], [f_161])).
% 21.45/12.77  tff(c_535, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_529])).
% 21.45/12.77  tff(c_542, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_535])).
% 21.45/12.77  tff(c_512, plain, (![A_119, B_120]: (v1_funct_1(k2_funct_2(A_119, B_120)) | ~m1_subset_1(B_120, k1_zfmisc_1(k2_zfmisc_1(A_119, A_119))) | ~v3_funct_2(B_120, A_119, A_119) | ~v1_funct_2(B_120, A_119, A_119) | ~v1_funct_1(B_120))), inference(cnfTransformation, [status(thm)], [f_137])).
% 21.45/12.77  tff(c_518, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2')) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_512])).
% 21.45/12.77  tff(c_525, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_518])).
% 21.45/12.77  tff(c_551, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_542, c_525])).
% 21.45/12.77  tff(c_559, plain, (![A_125, B_126]: (v3_funct_2(k2_funct_2(A_125, B_126), A_125, A_125) | ~m1_subset_1(B_126, k1_zfmisc_1(k2_zfmisc_1(A_125, A_125))) | ~v3_funct_2(B_126, A_125, A_125) | ~v1_funct_2(B_126, A_125, A_125) | ~v1_funct_1(B_126))), inference(cnfTransformation, [status(thm)], [f_137])).
% 21.45/12.77  tff(c_563, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_2'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_559])).
% 21.45/12.77  tff(c_569, plain, (v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_542, c_563])).
% 21.45/12.77  tff(c_1136, plain, (![A_174, B_175]: (m1_subset_1(k2_funct_2(A_174, B_175), k1_zfmisc_1(k2_zfmisc_1(A_174, A_174))) | ~m1_subset_1(B_175, k1_zfmisc_1(k2_zfmisc_1(A_174, A_174))) | ~v3_funct_2(B_175, A_174, A_174) | ~v1_funct_2(B_175, A_174, A_174) | ~v1_funct_1(B_175))), inference(cnfTransformation, [status(thm)], [f_137])).
% 21.45/12.77  tff(c_1169, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_542, c_1136])).
% 21.45/12.77  tff(c_1187, plain, (m1_subset_1(k2_funct_1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_1169])).
% 21.45/12.77  tff(c_26, plain, (![C_23, B_22, A_21]: (v2_funct_2(C_23, B_22) | ~v3_funct_2(C_23, A_21, B_22) | ~v1_funct_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 21.45/12.77  tff(c_1202, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_2'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_1187, c_26])).
% 21.45/12.77  tff(c_1234, plain, (v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_551, c_569, c_1202])).
% 21.45/12.77  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 21.45/12.77  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 21.45/12.77  tff(c_1216, plain, (v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_1187, c_2])).
% 21.45/12.77  tff(c_1243, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1216])).
% 21.45/12.77  tff(c_18, plain, (![C_16, B_15, A_14]: (v5_relat_1(C_16, B_15) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 21.45/12.77  tff(c_1239, plain, (v5_relat_1(k2_funct_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_1187, c_18])).
% 21.45/12.77  tff(c_34, plain, (![B_25, A_24]: (k2_relat_1(B_25)=A_24 | ~v2_funct_2(B_25, A_24) | ~v5_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_109])).
% 21.45/12.77  tff(c_1256, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_1239, c_34])).
% 21.45/12.77  tff(c_1259, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1243, c_1256])).
% 21.45/12.77  tff(c_1626, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1234, c_1259])).
% 21.45/12.77  tff(c_6, plain, (![A_6]: (k2_relat_1(k2_funct_1(A_6))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 21.45/12.77  tff(c_1635, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1626, c_6])).
% 21.45/12.77  tff(c_1649, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_76, c_465, c_1635])).
% 21.45/12.77  tff(c_1651, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1252, c_1649])).
% 21.45/12.77  tff(c_1652, plain, (k5_relat_1('#skF_3', '#skF_2')!=k6_partfun1('#skF_1') | k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_1131])).
% 21.45/12.77  tff(c_2334, plain, (k5_relat_1('#skF_3', '#skF_2')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1652])).
% 21.45/12.77  tff(c_1009, plain, (![A_163, E_166, C_165, D_161, B_162, F_164]: (m1_subset_1(k1_partfun1(A_163, B_162, C_165, D_161, E_166, F_164), k1_zfmisc_1(k2_zfmisc_1(A_163, D_161))) | ~m1_subset_1(F_164, k1_zfmisc_1(k2_zfmisc_1(C_165, D_161))) | ~v1_funct_1(F_164) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(A_163, B_162))) | ~v1_funct_1(E_166))), inference(cnfTransformation, [status(thm)], [f_121])).
% 21.45/12.77  tff(c_50, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 21.45/12.77  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 21.45/12.77  tff(c_488, plain, (![D_115, C_116, A_117, B_118]: (D_115=C_116 | ~r2_relset_1(A_117, B_118, C_116, D_115) | ~m1_subset_1(D_115, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 21.45/12.77  tff(c_496, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_488])).
% 21.45/12.77  tff(c_511, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_496])).
% 21.45/12.77  tff(c_574, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_511])).
% 21.45/12.77  tff(c_1028, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_1009, c_574])).
% 21.45/12.77  tff(c_1069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_70, c_68, c_62, c_1028])).
% 21.45/12.77  tff(c_1070, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_511])).
% 21.45/12.77  tff(c_1782, plain, (![D_216, F_213, B_217, C_214, A_212, E_215]: (k1_partfun1(A_212, B_217, C_214, D_216, E_215, F_213)=k5_relat_1(E_215, F_213) | ~m1_subset_1(F_213, k1_zfmisc_1(k2_zfmisc_1(C_214, D_216))) | ~v1_funct_1(F_213) | ~m1_subset_1(E_215, k1_zfmisc_1(k2_zfmisc_1(A_212, B_217))) | ~v1_funct_1(E_215))), inference(cnfTransformation, [status(thm)], [f_151])).
% 21.45/12.77  tff(c_1794, plain, (![A_212, B_217, E_215]: (k1_partfun1(A_212, B_217, '#skF_1', '#skF_1', E_215, '#skF_3')=k5_relat_1(E_215, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_215, k1_zfmisc_1(k2_zfmisc_1(A_212, B_217))) | ~v1_funct_1(E_215))), inference(resolution, [status(thm)], [c_62, c_1782])).
% 21.45/12.77  tff(c_2061, plain, (![A_227, B_228, E_229]: (k1_partfun1(A_227, B_228, '#skF_1', '#skF_1', E_229, '#skF_3')=k5_relat_1(E_229, '#skF_3') | ~m1_subset_1(E_229, k1_zfmisc_1(k2_zfmisc_1(A_227, B_228))) | ~v1_funct_1(E_229))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1794])).
% 21.45/12.77  tff(c_2082, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3')=k5_relat_1('#skF_2', '#skF_3') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_70, c_2061])).
% 21.45/12.77  tff(c_2100, plain, (k5_relat_1('#skF_2', '#skF_3')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1070, c_2082])).
% 21.45/12.77  tff(c_461, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_452])).
% 21.45/12.77  tff(c_468, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_461])).
% 21.45/12.77  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_185])).
% 21.45/12.77  tff(c_538, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_529])).
% 21.45/12.77  tff(c_545, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_538])).
% 21.45/12.77  tff(c_1172, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_545, c_1136])).
% 21.45/12.77  tff(c_1189, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_1172])).
% 21.45/12.77  tff(c_1746, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_1189, c_2])).
% 21.45/12.77  tff(c_1779, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1746])).
% 21.45/12.77  tff(c_521, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_512])).
% 21.45/12.77  tff(c_528, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_521])).
% 21.45/12.77  tff(c_546, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_545, c_528])).
% 21.45/12.77  tff(c_565, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_3'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_559])).
% 21.45/12.77  tff(c_572, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_545, c_565])).
% 21.45/12.77  tff(c_1732, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1189, c_26])).
% 21.45/12.77  tff(c_1770, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_546, c_572, c_1732])).
% 21.45/12.77  tff(c_1775, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_1189, c_18])).
% 21.45/12.77  tff(c_1811, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1775, c_34])).
% 21.45/12.77  tff(c_1814, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1779, c_1770, c_1811])).
% 21.45/12.77  tff(c_1823, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1814, c_6])).
% 21.45/12.77  tff(c_1837, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_68, c_468, c_1823])).
% 21.45/12.77  tff(c_1106, plain, (![B_172]: (k2_funct_1('#skF_3')=B_172 | k5_relat_1(B_172, '#skF_3')!=k6_partfun1('#skF_1') | k2_relat_1(B_172)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_172) | ~v1_relat_1(B_172) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_337, c_1098])).
% 21.45/12.77  tff(c_1114, plain, (![B_172]: (k2_funct_1('#skF_3')=B_172 | k5_relat_1(B_172, '#skF_3')!=k6_partfun1('#skF_1') | k2_relat_1(B_172)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_172) | ~v1_relat_1(B_172))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_68, c_468, c_1106])).
% 21.45/12.77  tff(c_29021, plain, (![B_828]: (k2_funct_1('#skF_3')=B_828 | k5_relat_1(B_828, '#skF_3')!=k6_partfun1('#skF_1') | k2_relat_1(B_828)!='#skF_1' | ~v1_funct_1(B_828) | ~v1_relat_1(B_828))), inference(demodulation, [status(thm), theory('equality')], [c_1837, c_1114])).
% 21.45/12.77  tff(c_29324, plain, (k2_funct_1('#skF_3')='#skF_2' | k5_relat_1('#skF_2', '#skF_3')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_2')!='#skF_1' | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_103, c_29021])).
% 21.45/12.77  tff(c_29563, plain, (k2_funct_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_412, c_2100, c_29324])).
% 21.45/12.77  tff(c_28, plain, (![C_23, A_21, B_22]: (v2_funct_1(C_23) | ~v3_funct_2(C_23, A_21, B_22) | ~v1_funct_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 21.45/12.77  tff(c_1735, plain, (v2_funct_1(k2_funct_1('#skF_3')) | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1189, c_28])).
% 21.45/12.77  tff(c_1773, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_546, c_572, c_1735])).
% 21.45/12.77  tff(c_8, plain, (![A_6]: (k1_relat_1(k2_funct_1(A_6))=k2_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 21.45/12.77  tff(c_12, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_relat_1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 21.45/12.77  tff(c_78, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_partfun1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_12])).
% 21.45/12.77  tff(c_4058, plain, (![A_300]: (k2_funct_1(k2_funct_1(A_300))=A_300 | k6_partfun1(k2_relat_1(k2_funct_1(A_300)))!=k6_partfun1(k1_relat_1(A_300)) | k1_relat_1(k2_funct_1(A_300))!=k2_relat_1(A_300) | ~v2_funct_1(k2_funct_1(A_300)) | ~v1_funct_1(A_300) | ~v1_relat_1(A_300) | ~v1_funct_1(k2_funct_1(A_300)) | ~v1_relat_1(k2_funct_1(A_300)) | ~v2_funct_1(A_300) | ~v1_funct_1(A_300) | ~v1_relat_1(A_300))), inference(superposition, [status(thm), theory('equality')], [c_78, c_1098])).
% 21.45/12.77  tff(c_4064, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | k6_partfun1(k1_relat_1('#skF_3'))!=k6_partfun1('#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1814, c_4058])).
% 21.45/12.77  tff(c_4071, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_68, c_468, c_1779, c_546, c_104, c_68, c_1773, c_337, c_1837, c_4064])).
% 21.45/12.77  tff(c_4258, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_4071])).
% 21.45/12.77  tff(c_4292, plain, (k2_relat_1('#skF_3')!='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_4258])).
% 21.45/12.77  tff(c_4295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_68, c_468, c_337, c_4292])).
% 21.45/12.77  tff(c_4296, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(splitRight, [status(thm)], [c_4071])).
% 21.45/12.77  tff(c_10, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_relat_1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 21.45/12.77  tff(c_79, plain, (![A_7]: (k5_relat_1(k2_funct_1(A_7), A_7)=k6_partfun1(k2_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_10])).
% 21.45/12.77  tff(c_4365, plain, (k6_partfun1(k2_relat_1(k2_funct_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4296, c_79])).
% 21.45/12.77  tff(c_4386, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1779, c_546, c_1773, c_1814, c_4365])).
% 21.45/12.77  tff(c_29656, plain, (k5_relat_1('#skF_3', '#skF_2')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_29563, c_4386])).
% 21.45/12.77  tff(c_29744, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2334, c_29656])).
% 21.45/12.77  tff(c_29745, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_1652])).
% 21.45/12.77  tff(c_58, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_185])).
% 21.45/12.77  tff(c_552, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_542, c_58])).
% 21.45/12.77  tff(c_29768, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_29745, c_552])).
% 21.45/12.77  tff(c_29794, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_165, c_29768])).
% 21.45/12.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.45/12.77  
% 21.45/12.77  Inference rules
% 21.45/12.77  ----------------------
% 21.45/12.77  #Ref     : 0
% 21.45/12.77  #Sup     : 6205
% 21.45/12.77  #Fact    : 0
% 21.45/12.77  #Define  : 0
% 21.45/12.77  #Split   : 60
% 21.45/12.77  #Chain   : 0
% 21.45/12.77  #Close   : 0
% 21.45/12.77  
% 21.45/12.77  Ordering : KBO
% 21.45/12.77  
% 21.45/12.77  Simplification rules
% 21.45/12.77  ----------------------
% 21.45/12.77  #Subsume      : 580
% 21.45/12.77  #Demod        : 17951
% 21.45/12.77  #Tautology    : 857
% 21.45/12.77  #SimpNegUnit  : 20
% 21.45/12.77  #BackRed      : 475
% 21.45/12.77  
% 21.45/12.77  #Partial instantiations: 0
% 21.45/12.77  #Strategies tried      : 1
% 21.45/12.77  
% 21.45/12.77  Timing (in seconds)
% 21.45/12.77  ----------------------
% 21.72/12.77  Preprocessing        : 0.50
% 21.72/12.77  Parsing              : 0.29
% 21.72/12.77  CNF conversion       : 0.03
% 21.72/12.77  Main loop            : 11.43
% 21.72/12.77  Inferencing          : 1.73
% 21.72/12.77  Reduction            : 6.99
% 21.72/12.77  Demodulation         : 6.21
% 21.72/12.77  BG Simplification    : 0.14
% 21.72/12.77  Subsumption          : 2.17
% 21.72/12.77  Abstraction          : 0.24
% 21.72/12.77  MUC search           : 0.00
% 21.72/12.77  Cooper               : 0.00
% 21.72/12.77  Total                : 11.99
% 21.72/12.77  Index Insertion      : 0.00
% 21.72/12.77  Index Deletion       : 0.00
% 21.72/12.77  Index Matching       : 0.00
% 21.72/12.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
