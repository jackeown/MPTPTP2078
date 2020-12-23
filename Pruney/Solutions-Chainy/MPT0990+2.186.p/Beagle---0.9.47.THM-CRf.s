%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:24 EST 2020

% Result     : Theorem 7.50s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 593 expanded)
%              Number of leaves         :   43 ( 224 expanded)
%              Depth                    :   15
%              Number of atoms          :  317 (2390 expanded)
%              Number of equality atoms :   90 ( 827 expanded)
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

tff(f_205,negated_conjecture,(
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

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_179,axiom,(
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

tff(f_120,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_96,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_118,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_108,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_137,axiom,(
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

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_163,axiom,(
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

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(c_56,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_103,plain,(
    ! [B_63,A_64] :
      ( v1_relat_1(B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_64))
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_112,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_103])).

tff(c_121,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_112])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_204,plain,(
    ! [A_74,B_75,C_76] :
      ( k2_relset_1(A_74,B_75,C_76) = k2_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_217,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_204])).

tff(c_2137,plain,(
    ! [A_174,C_175,B_176] :
      ( k6_partfun1(A_174) = k5_relat_1(C_175,k2_funct_1(C_175))
      | k1_xboole_0 = B_176
      | ~ v2_funct_1(C_175)
      | k2_relset_1(A_174,B_176,C_175) != B_176
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_174,B_176)))
      | ~ v1_funct_2(C_175,A_174,B_176)
      | ~ v1_funct_1(C_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_2143,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_2137])).

tff(c_2153,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_217,c_2143])).

tff(c_2154,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2153])).

tff(c_2177,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2154])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_40,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_32,plain,(
    ! [A_26] : m1_subset_1(k6_relat_1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_79,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32])).

tff(c_178,plain,(
    ! [A_69,B_70,D_71] :
      ( r2_relset_1(A_69,B_70,D_71,D_71)
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_185,plain,(
    ! [A_26] : r2_relset_1(A_26,A_26,k6_partfun1(A_26),k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_79,c_178])).

tff(c_969,plain,(
    ! [C_110,A_108,D_112,B_113,E_109,F_111] :
      ( k1_partfun1(A_108,B_113,C_110,D_112,E_109,F_111) = k5_relat_1(E_109,F_111)
      | ~ m1_subset_1(F_111,k1_zfmisc_1(k2_zfmisc_1(C_110,D_112)))
      | ~ v1_funct_1(F_111)
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_108,B_113)))
      | ~ v1_funct_1(E_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_975,plain,(
    ! [A_108,B_113,E_109] :
      ( k1_partfun1(A_108,B_113,'#skF_2','#skF_1',E_109,'#skF_4') = k5_relat_1(E_109,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_108,B_113)))
      | ~ v1_funct_1(E_109) ) ),
    inference(resolution,[status(thm)],[c_68,c_969])).

tff(c_1287,plain,(
    ! [A_130,B_131,E_132] :
      ( k1_partfun1(A_130,B_131,'#skF_2','#skF_1',E_132,'#skF_4') = k5_relat_1(E_132,'#skF_4')
      | ~ m1_subset_1(E_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131)))
      | ~ v1_funct_1(E_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_975])).

tff(c_1293,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1287])).

tff(c_1300,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1293])).

tff(c_64,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_473,plain,(
    ! [D_87,C_88,A_89,B_90] :
      ( D_87 = C_88
      | ~ r2_relset_1(A_89,B_90,C_88,D_87)
      | ~ m1_subset_1(D_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90)))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_481,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_64,c_473])).

tff(c_496,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_481])).

tff(c_526,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_496])).

tff(c_1404,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1300,c_526])).

tff(c_1496,plain,(
    ! [C_137,B_140,D_138,A_141,E_139,F_136] :
      ( m1_subset_1(k1_partfun1(A_141,B_140,C_137,D_138,E_139,F_136),k1_zfmisc_1(k2_zfmisc_1(A_141,D_138)))
      | ~ m1_subset_1(F_136,k1_zfmisc_1(k2_zfmisc_1(C_137,D_138)))
      | ~ v1_funct_1(F_136)
      | ~ m1_subset_1(E_139,k1_zfmisc_1(k2_zfmisc_1(A_141,B_140)))
      | ~ v1_funct_1(E_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1530,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1300,c_1496])).

tff(c_1553,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_1530])).

tff(c_1555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1404,c_1553])).

tff(c_1556,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_496])).

tff(c_3077,plain,(
    ! [A_209,B_210,C_211,D_212] :
      ( k2_relset_1(A_209,B_210,C_211) = B_210
      | ~ r2_relset_1(B_210,B_210,k1_partfun1(B_210,A_209,A_209,B_210,D_212,C_211),k6_partfun1(B_210))
      | ~ m1_subset_1(D_212,k1_zfmisc_1(k2_zfmisc_1(B_210,A_209)))
      | ~ v1_funct_2(D_212,B_210,A_209)
      | ~ v1_funct_1(D_212)
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210)))
      | ~ v1_funct_2(C_211,A_209,B_210)
      | ~ v1_funct_1(C_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_3083,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1556,c_3077])).

tff(c_3087,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_78,c_76,c_74,c_185,c_217,c_3083])).

tff(c_3089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2177,c_3087])).

tff(c_3090,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2154])).

tff(c_3130,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3090])).

tff(c_18,plain,(
    ! [A_16] : v2_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_80,plain,(
    ! [A_16] : v2_funct_1(k6_partfun1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_4070,plain,(
    ! [D_249,E_248,C_250,A_247,B_246] :
      ( k1_xboole_0 = C_250
      | v2_funct_1(E_248)
      | k2_relset_1(A_247,B_246,D_249) != B_246
      | ~ v2_funct_1(k1_partfun1(A_247,B_246,B_246,C_250,D_249,E_248))
      | ~ m1_subset_1(E_248,k1_zfmisc_1(k2_zfmisc_1(B_246,C_250)))
      | ~ v1_funct_2(E_248,B_246,C_250)
      | ~ v1_funct_1(E_248)
      | ~ m1_subset_1(D_249,k1_zfmisc_1(k2_zfmisc_1(A_247,B_246)))
      | ~ v1_funct_2(D_249,A_247,B_246)
      | ~ v1_funct_1(D_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_4076,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1556,c_4070])).

tff(c_4084,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_70,c_68,c_80,c_66,c_4076])).

tff(c_4086,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3130,c_60,c_4084])).

tff(c_4088,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_3090])).

tff(c_14,plain,(
    ! [A_15] :
      ( v1_relat_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4087,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3090])).

tff(c_16,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_81,plain,(
    ! [A_16] : v1_relat_1(k6_partfun1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_16])).

tff(c_8,plain,(
    ! [A_13] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_13)),A_13) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_83,plain,(
    ! [A_13] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_13)),A_13) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8])).

tff(c_235,plain,(
    ! [A_77,B_78,C_79] :
      ( k5_relat_1(k5_relat_1(A_77,B_78),C_79) = k5_relat_1(A_77,k5_relat_1(B_78,C_79))
      | ~ v1_relat_1(C_79)
      | ~ v1_relat_1(B_78)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_257,plain,(
    ! [A_13,C_79] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_13)),k5_relat_1(A_13,C_79)) = k5_relat_1(A_13,C_79)
      | ~ v1_relat_1(C_79)
      | ~ v1_relat_1(A_13)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_13)))
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_235])).

tff(c_272,plain,(
    ! [A_13,C_79] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_13)),k5_relat_1(A_13,C_79)) = k5_relat_1(A_13,C_79)
      | ~ v1_relat_1(C_79)
      | ~ v1_relat_1(A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_257])).

tff(c_4092,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k6_partfun1('#skF_2')) = k5_relat_1('#skF_4',k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4087,c_272])).

tff(c_4099,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k6_partfun1('#skF_2')) = k6_partfun1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_4087,c_4092])).

tff(c_4315,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4099])).

tff(c_4380,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_4315])).

tff(c_4384,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_72,c_4380])).

tff(c_4386,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4099])).

tff(c_109,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_103])).

tff(c_118,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_109])).

tff(c_210,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_204])).

tff(c_216,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_210])).

tff(c_10,plain,(
    ! [A_14] :
      ( k5_relat_1(A_14,k6_relat_1(k2_relat_1(A_14))) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_82,plain,(
    ! [A_14] :
      ( k5_relat_1(A_14,k6_partfun1(k2_relat_1(A_14))) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_10])).

tff(c_221,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_82])).

tff(c_225,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_221])).

tff(c_3091,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2154])).

tff(c_163,plain,(
    ! [A_68] :
      ( k1_relat_1(k2_funct_1(A_68)) = k2_relat_1(A_68)
      | ~ v2_funct_1(A_68)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5677,plain,(
    ! [A_301] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_301)),k2_funct_1(A_301)) = k2_funct_1(A_301)
      | ~ v1_relat_1(k2_funct_1(A_301))
      | ~ v2_funct_1(A_301)
      | ~ v1_funct_1(A_301)
      | ~ v1_relat_1(A_301) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_83])).

tff(c_5703,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3091,c_5677])).

tff(c_5727,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_72,c_4088,c_4386,c_5703])).

tff(c_2091,plain,(
    ! [A_163,C_165,F_166,E_164,D_167,B_168] :
      ( k1_partfun1(A_163,B_168,C_165,D_167,E_164,F_166) = k5_relat_1(E_164,F_166)
      | ~ m1_subset_1(F_166,k1_zfmisc_1(k2_zfmisc_1(C_165,D_167)))
      | ~ v1_funct_1(F_166)
      | ~ m1_subset_1(E_164,k1_zfmisc_1(k2_zfmisc_1(A_163,B_168)))
      | ~ v1_funct_1(E_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2097,plain,(
    ! [A_163,B_168,E_164] :
      ( k1_partfun1(A_163,B_168,'#skF_2','#skF_1',E_164,'#skF_4') = k5_relat_1(E_164,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_164,k1_zfmisc_1(k2_zfmisc_1(A_163,B_168)))
      | ~ v1_funct_1(E_164) ) ),
    inference(resolution,[status(thm)],[c_68,c_2091])).

tff(c_4139,plain,(
    ! [A_251,B_252,E_253] :
      ( k1_partfun1(A_251,B_252,'#skF_2','#skF_1',E_253,'#skF_4') = k5_relat_1(E_253,'#skF_4')
      | ~ m1_subset_1(E_253,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252)))
      | ~ v1_funct_1(E_253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2097])).

tff(c_4145,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_4139])).

tff(c_4152,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1556,c_4145])).

tff(c_6,plain,(
    ! [A_6,B_10,C_12] :
      ( k5_relat_1(k5_relat_1(A_6,B_10),C_12) = k5_relat_1(A_6,k5_relat_1(B_10,C_12))
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4168,plain,(
    ! [C_12] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_12) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_12))
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4152,c_6])).

tff(c_4178,plain,(
    ! [C_12] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_12) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_12))
      | ~ v1_relat_1(C_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_121,c_4168])).

tff(c_5733,plain,
    ( k5_relat_1('#skF_3',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5727,c_4178])).

tff(c_5749,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4386,c_225,c_4087,c_5733])).

tff(c_24,plain,(
    ! [A_18] :
      ( k2_funct_1(k2_funct_1(A_18)) = A_18
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5784,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5749,c_24])).

tff(c_5802,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_72,c_4088,c_5784])).

tff(c_5804,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_5802])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.50/2.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.50/2.80  
% 7.50/2.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.50/2.81  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.50/2.81  
% 7.50/2.81  %Foreground sorts:
% 7.50/2.81  
% 7.50/2.81  
% 7.50/2.81  %Background operators:
% 7.50/2.81  
% 7.50/2.81  
% 7.50/2.81  %Foreground operators:
% 7.50/2.81  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.50/2.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.50/2.81  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.50/2.81  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.50/2.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.50/2.81  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.50/2.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.50/2.81  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.50/2.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.50/2.81  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.50/2.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.50/2.81  tff('#skF_2', type, '#skF_2': $i).
% 7.50/2.81  tff('#skF_3', type, '#skF_3': $i).
% 7.50/2.81  tff('#skF_1', type, '#skF_1': $i).
% 7.50/2.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.50/2.81  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.50/2.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.50/2.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.50/2.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.50/2.81  tff('#skF_4', type, '#skF_4': $i).
% 7.50/2.81  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.50/2.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.50/2.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.50/2.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.50/2.81  
% 7.65/2.83  tff(f_205, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 7.65/2.83  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.65/2.83  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.65/2.83  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.65/2.83  tff(f_179, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 7.65/2.83  tff(f_120, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.65/2.83  tff(f_96, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 7.65/2.83  tff(f_94, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.65/2.83  tff(f_118, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.65/2.83  tff(f_108, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.65/2.83  tff(f_137, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.65/2.83  tff(f_64, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.65/2.83  tff(f_163, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 7.65/2.83  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.65/2.83  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 7.65/2.83  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 7.65/2.83  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 7.65/2.83  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 7.65/2.83  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 7.65/2.83  tff(c_56, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_205])).
% 7.65/2.83  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.65/2.83  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 7.65/2.83  tff(c_103, plain, (![B_63, A_64]: (v1_relat_1(B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_64)) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.65/2.83  tff(c_112, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_68, c_103])).
% 7.65/2.83  tff(c_121, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_112])).
% 7.65/2.83  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 7.65/2.83  tff(c_60, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_205])).
% 7.65/2.83  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 7.65/2.83  tff(c_204, plain, (![A_74, B_75, C_76]: (k2_relset_1(A_74, B_75, C_76)=k2_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.65/2.83  tff(c_217, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_204])).
% 7.65/2.83  tff(c_2137, plain, (![A_174, C_175, B_176]: (k6_partfun1(A_174)=k5_relat_1(C_175, k2_funct_1(C_175)) | k1_xboole_0=B_176 | ~v2_funct_1(C_175) | k2_relset_1(A_174, B_176, C_175)!=B_176 | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_174, B_176))) | ~v1_funct_2(C_175, A_174, B_176) | ~v1_funct_1(C_175))), inference(cnfTransformation, [status(thm)], [f_179])).
% 7.65/2.83  tff(c_2143, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_2137])).
% 7.65/2.83  tff(c_2153, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_217, c_2143])).
% 7.65/2.83  tff(c_2154, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_60, c_2153])).
% 7.65/2.83  tff(c_2177, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2154])).
% 7.65/2.83  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 7.65/2.83  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 7.65/2.83  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 7.65/2.83  tff(c_40, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.65/2.83  tff(c_32, plain, (![A_26]: (m1_subset_1(k6_relat_1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.65/2.83  tff(c_79, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32])).
% 7.65/2.83  tff(c_178, plain, (![A_69, B_70, D_71]: (r2_relset_1(A_69, B_70, D_71, D_71) | ~m1_subset_1(D_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.65/2.83  tff(c_185, plain, (![A_26]: (r2_relset_1(A_26, A_26, k6_partfun1(A_26), k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_79, c_178])).
% 7.65/2.83  tff(c_969, plain, (![C_110, A_108, D_112, B_113, E_109, F_111]: (k1_partfun1(A_108, B_113, C_110, D_112, E_109, F_111)=k5_relat_1(E_109, F_111) | ~m1_subset_1(F_111, k1_zfmisc_1(k2_zfmisc_1(C_110, D_112))) | ~v1_funct_1(F_111) | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_108, B_113))) | ~v1_funct_1(E_109))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.65/2.83  tff(c_975, plain, (![A_108, B_113, E_109]: (k1_partfun1(A_108, B_113, '#skF_2', '#skF_1', E_109, '#skF_4')=k5_relat_1(E_109, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_108, B_113))) | ~v1_funct_1(E_109))), inference(resolution, [status(thm)], [c_68, c_969])).
% 7.65/2.83  tff(c_1287, plain, (![A_130, B_131, E_132]: (k1_partfun1(A_130, B_131, '#skF_2', '#skF_1', E_132, '#skF_4')=k5_relat_1(E_132, '#skF_4') | ~m1_subset_1(E_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))) | ~v1_funct_1(E_132))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_975])).
% 7.65/2.83  tff(c_1293, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1287])).
% 7.65/2.83  tff(c_1300, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1293])).
% 7.65/2.83  tff(c_64, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 7.65/2.83  tff(c_473, plain, (![D_87, C_88, A_89, B_90]: (D_87=C_88 | ~r2_relset_1(A_89, B_90, C_88, D_87) | ~m1_subset_1(D_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.65/2.83  tff(c_481, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_64, c_473])).
% 7.65/2.83  tff(c_496, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_481])).
% 7.65/2.83  tff(c_526, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_496])).
% 7.65/2.83  tff(c_1404, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1300, c_526])).
% 7.65/2.83  tff(c_1496, plain, (![C_137, B_140, D_138, A_141, E_139, F_136]: (m1_subset_1(k1_partfun1(A_141, B_140, C_137, D_138, E_139, F_136), k1_zfmisc_1(k2_zfmisc_1(A_141, D_138))) | ~m1_subset_1(F_136, k1_zfmisc_1(k2_zfmisc_1(C_137, D_138))) | ~v1_funct_1(F_136) | ~m1_subset_1(E_139, k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))) | ~v1_funct_1(E_139))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.65/2.83  tff(c_1530, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1300, c_1496])).
% 7.65/2.83  tff(c_1553, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_1530])).
% 7.65/2.83  tff(c_1555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1404, c_1553])).
% 7.65/2.83  tff(c_1556, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_496])).
% 7.65/2.83  tff(c_3077, plain, (![A_209, B_210, C_211, D_212]: (k2_relset_1(A_209, B_210, C_211)=B_210 | ~r2_relset_1(B_210, B_210, k1_partfun1(B_210, A_209, A_209, B_210, D_212, C_211), k6_partfun1(B_210)) | ~m1_subset_1(D_212, k1_zfmisc_1(k2_zfmisc_1(B_210, A_209))) | ~v1_funct_2(D_212, B_210, A_209) | ~v1_funct_1(D_212) | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))) | ~v1_funct_2(C_211, A_209, B_210) | ~v1_funct_1(C_211))), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.65/2.83  tff(c_3083, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1556, c_3077])).
% 7.65/2.83  tff(c_3087, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_78, c_76, c_74, c_185, c_217, c_3083])).
% 7.65/2.83  tff(c_3089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2177, c_3087])).
% 7.65/2.83  tff(c_3090, plain, (~v2_funct_1('#skF_4') | k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2154])).
% 7.65/2.83  tff(c_3130, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_3090])).
% 7.65/2.83  tff(c_18, plain, (![A_16]: (v2_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.65/2.83  tff(c_80, plain, (![A_16]: (v2_funct_1(k6_partfun1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_18])).
% 7.65/2.83  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_205])).
% 7.65/2.83  tff(c_4070, plain, (![D_249, E_248, C_250, A_247, B_246]: (k1_xboole_0=C_250 | v2_funct_1(E_248) | k2_relset_1(A_247, B_246, D_249)!=B_246 | ~v2_funct_1(k1_partfun1(A_247, B_246, B_246, C_250, D_249, E_248)) | ~m1_subset_1(E_248, k1_zfmisc_1(k2_zfmisc_1(B_246, C_250))) | ~v1_funct_2(E_248, B_246, C_250) | ~v1_funct_1(E_248) | ~m1_subset_1(D_249, k1_zfmisc_1(k2_zfmisc_1(A_247, B_246))) | ~v1_funct_2(D_249, A_247, B_246) | ~v1_funct_1(D_249))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.65/2.83  tff(c_4076, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1556, c_4070])).
% 7.65/2.83  tff(c_4084, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_70, c_68, c_80, c_66, c_4076])).
% 7.65/2.83  tff(c_4086, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3130, c_60, c_4084])).
% 7.65/2.83  tff(c_4088, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_3090])).
% 7.65/2.83  tff(c_14, plain, (![A_15]: (v1_relat_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.65/2.83  tff(c_4087, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_3090])).
% 7.65/2.83  tff(c_16, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.65/2.83  tff(c_81, plain, (![A_16]: (v1_relat_1(k6_partfun1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_16])).
% 7.65/2.83  tff(c_8, plain, (![A_13]: (k5_relat_1(k6_relat_1(k1_relat_1(A_13)), A_13)=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.65/2.83  tff(c_83, plain, (![A_13]: (k5_relat_1(k6_partfun1(k1_relat_1(A_13)), A_13)=A_13 | ~v1_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8])).
% 7.65/2.83  tff(c_235, plain, (![A_77, B_78, C_79]: (k5_relat_1(k5_relat_1(A_77, B_78), C_79)=k5_relat_1(A_77, k5_relat_1(B_78, C_79)) | ~v1_relat_1(C_79) | ~v1_relat_1(B_78) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.65/2.83  tff(c_257, plain, (![A_13, C_79]: (k5_relat_1(k6_partfun1(k1_relat_1(A_13)), k5_relat_1(A_13, C_79))=k5_relat_1(A_13, C_79) | ~v1_relat_1(C_79) | ~v1_relat_1(A_13) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_13))) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_83, c_235])).
% 7.65/2.83  tff(c_272, plain, (![A_13, C_79]: (k5_relat_1(k6_partfun1(k1_relat_1(A_13)), k5_relat_1(A_13, C_79))=k5_relat_1(A_13, C_79) | ~v1_relat_1(C_79) | ~v1_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_257])).
% 7.65/2.83  tff(c_4092, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k6_partfun1('#skF_2'))=k5_relat_1('#skF_4', k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4087, c_272])).
% 7.65/2.83  tff(c_4099, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k6_partfun1('#skF_2'))=k6_partfun1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_4087, c_4092])).
% 7.65/2.83  tff(c_4315, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_4099])).
% 7.65/2.83  tff(c_4380, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_4315])).
% 7.65/2.83  tff(c_4384, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_72, c_4380])).
% 7.65/2.83  tff(c_4386, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4099])).
% 7.65/2.83  tff(c_109, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_103])).
% 7.65/2.83  tff(c_118, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_109])).
% 7.65/2.83  tff(c_210, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_204])).
% 7.65/2.83  tff(c_216, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_210])).
% 7.65/2.83  tff(c_10, plain, (![A_14]: (k5_relat_1(A_14, k6_relat_1(k2_relat_1(A_14)))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.65/2.83  tff(c_82, plain, (![A_14]: (k5_relat_1(A_14, k6_partfun1(k2_relat_1(A_14)))=A_14 | ~v1_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_10])).
% 7.65/2.83  tff(c_221, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_216, c_82])).
% 7.65/2.83  tff(c_225, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_221])).
% 7.65/2.83  tff(c_3091, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_2154])).
% 7.65/2.83  tff(c_163, plain, (![A_68]: (k1_relat_1(k2_funct_1(A_68))=k2_relat_1(A_68) | ~v2_funct_1(A_68) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.65/2.83  tff(c_5677, plain, (![A_301]: (k5_relat_1(k6_partfun1(k2_relat_1(A_301)), k2_funct_1(A_301))=k2_funct_1(A_301) | ~v1_relat_1(k2_funct_1(A_301)) | ~v2_funct_1(A_301) | ~v1_funct_1(A_301) | ~v1_relat_1(A_301))), inference(superposition, [status(thm), theory('equality')], [c_163, c_83])).
% 7.65/2.83  tff(c_5703, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3091, c_5677])).
% 7.65/2.83  tff(c_5727, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_72, c_4088, c_4386, c_5703])).
% 7.65/2.83  tff(c_2091, plain, (![A_163, C_165, F_166, E_164, D_167, B_168]: (k1_partfun1(A_163, B_168, C_165, D_167, E_164, F_166)=k5_relat_1(E_164, F_166) | ~m1_subset_1(F_166, k1_zfmisc_1(k2_zfmisc_1(C_165, D_167))) | ~v1_funct_1(F_166) | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(A_163, B_168))) | ~v1_funct_1(E_164))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.65/2.83  tff(c_2097, plain, (![A_163, B_168, E_164]: (k1_partfun1(A_163, B_168, '#skF_2', '#skF_1', E_164, '#skF_4')=k5_relat_1(E_164, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_164, k1_zfmisc_1(k2_zfmisc_1(A_163, B_168))) | ~v1_funct_1(E_164))), inference(resolution, [status(thm)], [c_68, c_2091])).
% 7.65/2.83  tff(c_4139, plain, (![A_251, B_252, E_253]: (k1_partfun1(A_251, B_252, '#skF_2', '#skF_1', E_253, '#skF_4')=k5_relat_1(E_253, '#skF_4') | ~m1_subset_1(E_253, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))) | ~v1_funct_1(E_253))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2097])).
% 7.65/2.83  tff(c_4145, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_4139])).
% 7.65/2.83  tff(c_4152, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1556, c_4145])).
% 7.65/2.83  tff(c_6, plain, (![A_6, B_10, C_12]: (k5_relat_1(k5_relat_1(A_6, B_10), C_12)=k5_relat_1(A_6, k5_relat_1(B_10, C_12)) | ~v1_relat_1(C_12) | ~v1_relat_1(B_10) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.65/2.83  tff(c_4168, plain, (![C_12]: (k5_relat_1(k6_partfun1('#skF_1'), C_12)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_12)) | ~v1_relat_1(C_12) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4152, c_6])).
% 7.65/2.83  tff(c_4178, plain, (![C_12]: (k5_relat_1(k6_partfun1('#skF_1'), C_12)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_12)) | ~v1_relat_1(C_12))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_121, c_4168])).
% 7.65/2.83  tff(c_5733, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5727, c_4178])).
% 7.65/2.83  tff(c_5749, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4386, c_225, c_4087, c_5733])).
% 7.65/2.83  tff(c_24, plain, (![A_18]: (k2_funct_1(k2_funct_1(A_18))=A_18 | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.65/2.83  tff(c_5784, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5749, c_24])).
% 7.65/2.83  tff(c_5802, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_121, c_72, c_4088, c_5784])).
% 7.65/2.83  tff(c_5804, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_5802])).
% 7.65/2.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/2.83  
% 7.65/2.83  Inference rules
% 7.65/2.83  ----------------------
% 7.65/2.83  #Ref     : 0
% 7.65/2.83  #Sup     : 1257
% 7.65/2.83  #Fact    : 0
% 7.65/2.83  #Define  : 0
% 7.65/2.83  #Split   : 19
% 7.65/2.83  #Chain   : 0
% 7.65/2.83  #Close   : 0
% 7.65/2.83  
% 7.65/2.83  Ordering : KBO
% 7.65/2.83  
% 7.65/2.83  Simplification rules
% 7.65/2.83  ----------------------
% 7.65/2.83  #Subsume      : 31
% 7.65/2.83  #Demod        : 1794
% 7.65/2.83  #Tautology    : 553
% 7.65/2.83  #SimpNegUnit  : 58
% 7.65/2.83  #BackRed      : 31
% 7.65/2.83  
% 7.65/2.83  #Partial instantiations: 0
% 7.65/2.83  #Strategies tried      : 1
% 7.65/2.83  
% 7.65/2.83  Timing (in seconds)
% 7.65/2.83  ----------------------
% 7.65/2.83  Preprocessing        : 0.51
% 7.65/2.83  Parsing              : 0.28
% 7.65/2.83  CNF conversion       : 0.03
% 7.65/2.83  Main loop            : 1.36
% 7.65/2.83  Inferencing          : 0.47
% 7.65/2.83  Reduction            : 0.54
% 7.65/2.83  Demodulation         : 0.41
% 7.65/2.83  BG Simplification    : 0.06
% 7.65/2.83  Subsumption          : 0.21
% 7.65/2.83  Abstraction          : 0.07
% 7.65/2.83  MUC search           : 0.00
% 7.65/2.83  Cooper               : 0.00
% 7.65/2.83  Total                : 1.91
% 7.65/2.83  Index Insertion      : 0.00
% 7.65/2.83  Index Deletion       : 0.00
% 7.65/2.83  Index Matching       : 0.00
% 7.65/2.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
