%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:56 EST 2020

% Result     : Theorem 5.34s
% Output     : CNFRefutation 5.81s
% Verified   : 
% Statistics : Number of formulae       :  206 (2245 expanded)
%              Number of leaves         :   45 ( 744 expanded)
%              Depth                    :   17
%              Number of atoms          :  389 (5686 expanded)
%              Number of equality atoms :  147 (2017 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_186,negated_conjecture,(
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

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_120,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_37,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_164,axiom,(
    ! [A,B,C] :
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

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_62,axiom,(
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

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_849,plain,(
    ! [A_126,B_127,D_128] :
      ( r2_relset_1(A_126,B_127,D_128,D_128)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_860,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_849])).

tff(c_46,plain,(
    ! [A_29] : k6_relat_1(A_29) = k6_partfun1(A_29) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_8,plain,(
    ! [A_2] : k2_relat_1(k6_relat_1(A_2)) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_77,plain,(
    ! [A_2] : k2_relat_1(k6_partfun1(A_2)) = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_12,plain,(
    ! [A_4] : v1_relat_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_75,plain,(
    ! [A_4] : v1_relat_1(k6_partfun1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_110,plain,(
    ! [A_48] :
      ( k2_relat_1(A_48) != k1_xboole_0
      | k1_xboole_0 = A_48
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_113,plain,(
    ! [A_4] :
      ( k2_relat_1(k6_partfun1(A_4)) != k1_xboole_0
      | k6_partfun1(A_4) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_75,c_110])).

tff(c_115,plain,(
    ! [A_4] :
      ( k1_xboole_0 != A_4
      | k6_partfun1(A_4) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_113])).

tff(c_56,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_204,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),k1_xboole_0)
    | k1_xboole_0 != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_56])).

tff(c_241,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_72,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_70,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_66,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_188,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_201,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_188])).

tff(c_265,plain,(
    ! [C_60,B_61,A_62] :
      ( v5_relat_1(C_60,B_61)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_62,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_281,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_265])).

tff(c_331,plain,(
    ! [B_73,A_74] :
      ( k2_relat_1(B_73) = A_74
      | ~ v2_funct_2(B_73,A_74)
      | ~ v5_relat_1(B_73,A_74)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_340,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_281,c_331])).

tff(c_352,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_340])).

tff(c_356,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_352])).

tff(c_68,plain,(
    v3_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_634,plain,(
    ! [C_106,B_107,A_108] :
      ( v2_funct_2(C_106,B_107)
      | ~ v3_funct_2(C_106,A_108,B_107)
      | ~ v1_funct_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_646,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_634])).

tff(c_655,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_646])).

tff(c_657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_356,c_655])).

tff(c_658,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_352])).

tff(c_869,plain,(
    ! [A_130,B_131,C_132] :
      ( k2_relset_1(A_130,B_131,C_132) = k2_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_881,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_869])).

tff(c_889,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_881])).

tff(c_922,plain,(
    ! [C_136,A_137,B_138] :
      ( v2_funct_1(C_136)
      | ~ v3_funct_2(C_136,A_137,B_138)
      | ~ v1_funct_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_934,plain,
    ( v2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_922])).

tff(c_944,plain,(
    v2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_934])).

tff(c_1302,plain,(
    ! [C_186,D_187,B_188,A_189] :
      ( k2_funct_1(C_186) = D_187
      | k1_xboole_0 = B_188
      | k1_xboole_0 = A_189
      | ~ v2_funct_1(C_186)
      | ~ r2_relset_1(A_189,A_189,k1_partfun1(A_189,B_188,B_188,A_189,C_186,D_187),k6_partfun1(A_189))
      | k2_relset_1(A_189,B_188,C_186) != B_188
      | ~ m1_subset_1(D_187,k1_zfmisc_1(k2_zfmisc_1(B_188,A_189)))
      | ~ v1_funct_2(D_187,B_188,A_189)
      | ~ v1_funct_1(D_187)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_189,B_188)))
      | ~ v1_funct_2(C_186,A_189,B_188)
      | ~ v1_funct_1(C_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_1305,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_2')
    | k2_relset_1('#skF_1','#skF_1','#skF_2') != '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1302])).

tff(c_1311,plain,
    ( k2_funct_1('#skF_2') = '#skF_3'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_62,c_58,c_889,c_944,c_1305])).

tff(c_1312,plain,(
    k2_funct_1('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_1311])).

tff(c_1072,plain,(
    ! [A_151,B_152] :
      ( k2_funct_2(A_151,B_152) = k2_funct_1(B_152)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(k2_zfmisc_1(A_151,A_151)))
      | ~ v3_funct_2(B_152,A_151,A_151)
      | ~ v1_funct_2(B_152,A_151,A_151)
      | ~ v1_funct_1(B_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1084,plain,
    ( k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1072])).

tff(c_1092,plain,(
    k2_funct_2('#skF_1','#skF_2') = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1084])).

tff(c_54,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_2('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_1097,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1092,c_54])).

tff(c_1313,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1312,c_1097])).

tff(c_1317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_1313])).

tff(c_1319,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_200,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_188])).

tff(c_2,plain,(
    ! [A_1] :
      ( k2_relat_1(A_1) != k1_xboole_0
      | k1_xboole_0 = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_212,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_200,c_2])).

tff(c_222,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_212])).

tff(c_1321,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1319,c_222])).

tff(c_1337,plain,(
    ! [C_190,B_191,A_192] :
      ( v5_relat_1(C_190,B_191)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_192,B_191))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1348,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_1337])).

tff(c_1477,plain,(
    ! [B_212,A_213] :
      ( k2_relat_1(B_212) = A_213
      | ~ v2_funct_2(B_212,A_213)
      | ~ v5_relat_1(B_212,A_213)
      | ~ v1_relat_1(B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1489,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1348,c_1477])).

tff(c_1502,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_1489])).

tff(c_1503,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1321,c_1502])).

tff(c_60,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_1655,plain,(
    ! [C_227,B_228,A_229] :
      ( v2_funct_2(C_227,B_228)
      | ~ v3_funct_2(C_227,A_229,B_228)
      | ~ v1_funct_1(C_227)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_229,B_228))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1664,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1655])).

tff(c_1673,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_1664])).

tff(c_1675,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1503,c_1673])).

tff(c_1676,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_212])).

tff(c_117,plain,(
    ! [A_49] :
      ( k1_xboole_0 != A_49
      | k6_partfun1(A_49) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_113])).

tff(c_6,plain,(
    ! [A_2] : k1_relat_1(k6_relat_1(A_2)) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78,plain,(
    ! [A_2] : k1_relat_1(k6_partfun1(A_2)) = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_6])).

tff(c_126,plain,(
    ! [A_49] :
      ( k1_relat_1(k1_xboole_0) = A_49
      | k1_xboole_0 != A_49 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_78])).

tff(c_1733,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1676,c_1676,c_126])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_relat_1(A_1) != k1_xboole_0
      | k1_xboole_0 = A_1
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_211,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_200,c_4])).

tff(c_221,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_1678,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1676,c_221])).

tff(c_1736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1733,c_1678])).

tff(c_1737,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_1774,plain,
    ( r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_2','#skF_3'),'#skF_3')
    | '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1737,c_1737,c_204])).

tff(c_1775,plain,(
    '#skF_3' != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1774])).

tff(c_129,plain,(
    ! [A_49] :
      ( k2_relat_1(k1_xboole_0) = A_49
      | k1_xboole_0 != A_49 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_77])).

tff(c_1835,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1737,c_1737,c_129])).

tff(c_1781,plain,(
    ! [C_234,B_235,A_236] :
      ( v5_relat_1(C_234,B_235)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_236,B_235))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1792,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_1781])).

tff(c_1884,plain,(
    ! [B_249,A_250] :
      ( k2_relat_1(B_249) = A_250
      | ~ v2_funct_2(B_249,A_250)
      | ~ v5_relat_1(B_249,A_250)
      | ~ v1_relat_1(B_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1896,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1792,c_1884])).

tff(c_1908,plain,
    ( '#skF_3' = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_1835,c_1896])).

tff(c_1909,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1775,c_1908])).

tff(c_2104,plain,(
    ! [C_268,B_269,A_270] :
      ( v2_funct_2(C_268,B_269)
      | ~ v3_funct_2(C_268,A_270,B_269)
      | ~ v1_funct_1(C_268)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_270,B_269))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2113,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2104])).

tff(c_2124,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_2113])).

tff(c_2126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1909,c_2124])).

tff(c_2128,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1774])).

tff(c_2131,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_1737])).

tff(c_42,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_123,plain,(
    ! [A_49] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_49,A_49)))
      | k1_xboole_0 != A_49 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_42])).

tff(c_2679,plain,(
    ! [A_49] :
      ( m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_49,A_49)))
      | A_49 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2131,c_2131,c_123])).

tff(c_2772,plain,(
    ! [A_332,B_333,D_334] :
      ( r2_relset_1(A_332,B_333,D_334,D_334)
      | ~ m1_subset_1(D_334,k1_zfmisc_1(k2_zfmisc_1(A_332,B_333))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2786,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2679,c_2772])).

tff(c_2136,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_62])).

tff(c_2137,plain,(
    v3_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_60])).

tff(c_2138,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_64])).

tff(c_1738,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_1769,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1737,c_1738])).

tff(c_2129,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_2128,c_1769])).

tff(c_1756,plain,(
    ! [A_49] :
      ( k2_relat_1('#skF_3') = A_49
      | A_49 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1737,c_1737,c_129])).

tff(c_2175,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_2128,c_1756])).

tff(c_2132,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_200])).

tff(c_10,plain,(
    ! [A_3] :
      ( k5_relat_1(A_3,k6_relat_1(k2_relat_1(A_3))) = A_3
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1739,plain,(
    ! [A_232] :
      ( k5_relat_1(A_232,k6_partfun1(k2_relat_1(A_232))) = A_232
      | ~ v1_relat_1(A_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_1748,plain,(
    ! [A_232] :
      ( k5_relat_1(A_232,k1_xboole_0) = A_232
      | ~ v1_relat_1(A_232)
      | k2_relat_1(A_232) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_1739])).

tff(c_2756,plain,(
    ! [A_331] :
      ( k5_relat_1(A_331,'#skF_1') = A_331
      | ~ v1_relat_1(A_331)
      | k2_relat_1(A_331) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2131,c_2131,c_1748])).

tff(c_2759,plain,
    ( k5_relat_1('#skF_1','#skF_1') = '#skF_1'
    | k2_relat_1('#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_2132,c_2756])).

tff(c_2765,plain,(
    k5_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2175,c_2759])).

tff(c_14,plain,(
    ! [A_4] : v2_funct_1(k6_relat_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_74,plain,(
    ! [A_4] : v2_funct_1(k6_partfun1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_14])).

tff(c_136,plain,(
    ! [A_49] :
      ( v2_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_49 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_74])).

tff(c_155,plain,(
    ! [A_49] : k1_xboole_0 != A_49 ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_161,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_155])).

tff(c_162,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_1760,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1737,c_162])).

tff(c_2130,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_1760])).

tff(c_1762,plain,(
    ! [A_4] :
      ( A_4 != '#skF_3'
      | k6_partfun1(A_4) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1737,c_1737,c_115])).

tff(c_2580,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_2128,c_1762])).

tff(c_16,plain,(
    ! [A_5,B_7] :
      ( k2_funct_1(A_5) = B_7
      | k6_relat_1(k1_relat_1(A_5)) != k5_relat_1(A_5,B_7)
      | k2_relat_1(A_5) != k1_relat_1(B_7)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2925,plain,(
    ! [A_359,B_360] :
      ( k2_funct_1(A_359) = B_360
      | k6_partfun1(k1_relat_1(A_359)) != k5_relat_1(A_359,B_360)
      | k2_relat_1(A_359) != k1_relat_1(B_360)
      | ~ v2_funct_1(A_359)
      | ~ v1_funct_1(B_360)
      | ~ v1_relat_1(B_360)
      | ~ v1_funct_1(A_359)
      | ~ v1_relat_1(A_359) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_16])).

tff(c_2934,plain,(
    ! [B_360] :
      ( k2_funct_1('#skF_1') = B_360
      | k5_relat_1('#skF_1',B_360) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_1') != k1_relat_1(B_360)
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1(B_360)
      | ~ v1_relat_1(B_360)
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2129,c_2925])).

tff(c_3048,plain,(
    ! [B_364] :
      ( k2_funct_1('#skF_1') = B_364
      | k5_relat_1('#skF_1',B_364) != '#skF_1'
      | k1_relat_1(B_364) != '#skF_1'
      | ~ v1_funct_1(B_364)
      | ~ v1_relat_1(B_364) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2132,c_2138,c_2130,c_2175,c_2580,c_2934])).

tff(c_3051,plain,
    ( k2_funct_1('#skF_1') = '#skF_1'
    | k5_relat_1('#skF_1','#skF_1') != '#skF_1'
    | k1_relat_1('#skF_1') != '#skF_1'
    | ~ v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2132,c_3048])).

tff(c_3057,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2138,c_2129,c_2765,c_3051])).

tff(c_2914,plain,(
    ! [A_357,B_358] :
      ( k2_funct_2(A_357,B_358) = k2_funct_1(B_358)
      | ~ m1_subset_1(B_358,k1_zfmisc_1(k2_zfmisc_1(A_357,A_357)))
      | ~ v3_funct_2(B_358,A_357,A_357)
      | ~ v1_funct_2(B_358,A_357,A_357)
      | ~ v1_funct_1(B_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2917,plain,(
    ! [A_49] :
      ( k2_funct_2(A_49,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_49,A_49)
      | ~ v1_funct_2('#skF_1',A_49,A_49)
      | ~ v1_funct_1('#skF_1')
      | A_49 != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_2679,c_2914])).

tff(c_2923,plain,(
    ! [A_49] :
      ( k2_funct_2(A_49,'#skF_1') = k2_funct_1('#skF_1')
      | ~ v3_funct_2('#skF_1',A_49,A_49)
      | ~ v1_funct_2('#skF_1',A_49,A_49)
      | A_49 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2138,c_2917])).

tff(c_3120,plain,(
    ! [A_379] :
      ( k2_funct_2(A_379,'#skF_1') = '#skF_1'
      | ~ v3_funct_2('#skF_1',A_379,A_379)
      | ~ v1_funct_2('#skF_1',A_379,A_379)
      | A_379 != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3057,c_2923])).

tff(c_3123,plain,
    ( k2_funct_2('#skF_1','#skF_1') = '#skF_1'
    | ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2137,c_3120])).

tff(c_3126,plain,(
    k2_funct_2('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2136,c_3123])).

tff(c_220,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_201,c_2])).

tff(c_2199,plain,
    ( k2_relat_1('#skF_2') != '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2131,c_2131,c_220])).

tff(c_2200,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2199])).

tff(c_2185,plain,(
    ! [C_277,B_278,A_279] :
      ( v5_relat_1(C_277,B_278)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(k2_zfmisc_1(A_279,B_278))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2197,plain,(
    v5_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_2185])).

tff(c_2421,plain,(
    ! [B_301,A_302] :
      ( k2_relat_1(B_301) = A_302
      | ~ v2_funct_2(B_301,A_302)
      | ~ v5_relat_1(B_301,A_302)
      | ~ v1_relat_1(B_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2430,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2197,c_2421])).

tff(c_2439,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_2430])).

tff(c_2440,plain,(
    ~ v2_funct_2('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2200,c_2439])).

tff(c_2522,plain,(
    ! [C_312,B_313,A_314] :
      ( v2_funct_2(C_312,B_313)
      | ~ v3_funct_2(C_312,A_314,B_313)
      | ~ v1_funct_1(C_312)
      | ~ m1_subset_1(C_312,k1_zfmisc_1(k2_zfmisc_1(A_314,B_313))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2531,plain,
    ( v2_funct_2('#skF_2','#skF_1')
    | ~ v3_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_2522])).

tff(c_2539,plain,(
    v2_funct_2('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_2531])).

tff(c_2541,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2440,c_2539])).

tff(c_2542,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2199])).

tff(c_219,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_201,c_4])).

tff(c_2183,plain,
    ( k1_relat_1('#skF_2') != '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2131,c_2131,c_219])).

tff(c_2184,plain,(
    k1_relat_1('#skF_2') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2183])).

tff(c_2547,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2542,c_2184])).

tff(c_2557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2129,c_2547])).

tff(c_2558,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2183])).

tff(c_2134,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_54])).

tff(c_2632,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k2_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2558,c_2134])).

tff(c_3127,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3126,c_2632])).

tff(c_3130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2786,c_3127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.34/2.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.64/2.20  
% 5.64/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.73/2.20  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.73/2.20  
% 5.73/2.20  %Foreground sorts:
% 5.73/2.20  
% 5.73/2.20  
% 5.73/2.20  %Background operators:
% 5.73/2.20  
% 5.73/2.20  
% 5.73/2.20  %Foreground operators:
% 5.73/2.20  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.73/2.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.73/2.20  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.73/2.20  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.73/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.73/2.20  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.73/2.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.73/2.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.73/2.20  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 5.73/2.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.73/2.20  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.73/2.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.73/2.20  tff('#skF_2', type, '#skF_2': $i).
% 5.73/2.20  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.73/2.20  tff('#skF_3', type, '#skF_3': $i).
% 5.73/2.20  tff('#skF_1', type, '#skF_1': $i).
% 5.73/2.20  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.73/2.20  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.73/2.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.73/2.20  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.73/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.73/2.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.73/2.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.73/2.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.73/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.73/2.20  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.73/2.20  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.73/2.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.73/2.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.73/2.20  
% 5.81/2.23  tff(f_186, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 5.81/2.23  tff(f_84, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.81/2.23  tff(f_120, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.81/2.23  tff(f_37, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.81/2.23  tff(f_45, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 5.81/2.23  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.81/2.23  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.81/2.23  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.81/2.23  tff(f_104, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 5.81/2.23  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.81/2.23  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.81/2.23  tff(f_164, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 5.81/2.23  tff(f_118, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 5.81/2.23  tff(f_108, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 5.81/2.23  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 5.81/2.23  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 5.81/2.23  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.81/2.23  tff(c_849, plain, (![A_126, B_127, D_128]: (r2_relset_1(A_126, B_127, D_128, D_128) | ~m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.81/2.23  tff(c_860, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_849])).
% 5.81/2.23  tff(c_46, plain, (![A_29]: (k6_relat_1(A_29)=k6_partfun1(A_29))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.81/2.23  tff(c_8, plain, (![A_2]: (k2_relat_1(k6_relat_1(A_2))=A_2)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.81/2.23  tff(c_77, plain, (![A_2]: (k2_relat_1(k6_partfun1(A_2))=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8])).
% 5.81/2.23  tff(c_12, plain, (![A_4]: (v1_relat_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.81/2.23  tff(c_75, plain, (![A_4]: (v1_relat_1(k6_partfun1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 5.81/2.23  tff(c_110, plain, (![A_48]: (k2_relat_1(A_48)!=k1_xboole_0 | k1_xboole_0=A_48 | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.81/2.23  tff(c_113, plain, (![A_4]: (k2_relat_1(k6_partfun1(A_4))!=k1_xboole_0 | k6_partfun1(A_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_75, c_110])).
% 5.81/2.23  tff(c_115, plain, (![A_4]: (k1_xboole_0!=A_4 | k6_partfun1(A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_77, c_113])).
% 5.81/2.23  tff(c_56, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.81/2.23  tff(c_204, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), k1_xboole_0) | k1_xboole_0!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_115, c_56])).
% 5.81/2.23  tff(c_241, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_204])).
% 5.81/2.23  tff(c_72, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.81/2.23  tff(c_70, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.81/2.23  tff(c_66, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.81/2.23  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.81/2.23  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.81/2.23  tff(c_188, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.81/2.23  tff(c_201, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_188])).
% 5.81/2.23  tff(c_265, plain, (![C_60, B_61, A_62]: (v5_relat_1(C_60, B_61) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_62, B_61))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.81/2.23  tff(c_281, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_265])).
% 5.81/2.23  tff(c_331, plain, (![B_73, A_74]: (k2_relat_1(B_73)=A_74 | ~v2_funct_2(B_73, A_74) | ~v5_relat_1(B_73, A_74) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.81/2.23  tff(c_340, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_281, c_331])).
% 5.81/2.23  tff(c_352, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_201, c_340])).
% 5.81/2.23  tff(c_356, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_352])).
% 5.81/2.23  tff(c_68, plain, (v3_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.81/2.23  tff(c_634, plain, (![C_106, B_107, A_108]: (v2_funct_2(C_106, B_107) | ~v3_funct_2(C_106, A_108, B_107) | ~v1_funct_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.81/2.23  tff(c_646, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_634])).
% 5.81/2.23  tff(c_655, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_646])).
% 5.81/2.23  tff(c_657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_356, c_655])).
% 5.81/2.23  tff(c_658, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_352])).
% 5.81/2.23  tff(c_869, plain, (![A_130, B_131, C_132]: (k2_relset_1(A_130, B_131, C_132)=k2_relat_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.81/2.23  tff(c_881, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_869])).
% 5.81/2.23  tff(c_889, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_658, c_881])).
% 5.81/2.23  tff(c_922, plain, (![C_136, A_137, B_138]: (v2_funct_1(C_136) | ~v3_funct_2(C_136, A_137, B_138) | ~v1_funct_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.81/2.23  tff(c_934, plain, (v2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_922])).
% 5.81/2.23  tff(c_944, plain, (v2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_934])).
% 5.81/2.23  tff(c_1302, plain, (![C_186, D_187, B_188, A_189]: (k2_funct_1(C_186)=D_187 | k1_xboole_0=B_188 | k1_xboole_0=A_189 | ~v2_funct_1(C_186) | ~r2_relset_1(A_189, A_189, k1_partfun1(A_189, B_188, B_188, A_189, C_186, D_187), k6_partfun1(A_189)) | k2_relset_1(A_189, B_188, C_186)!=B_188 | ~m1_subset_1(D_187, k1_zfmisc_1(k2_zfmisc_1(B_188, A_189))) | ~v1_funct_2(D_187, B_188, A_189) | ~v1_funct_1(D_187) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_189, B_188))) | ~v1_funct_2(C_186, A_189, B_188) | ~v1_funct_1(C_186))), inference(cnfTransformation, [status(thm)], [f_164])).
% 5.81/2.23  tff(c_1305, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_2') | k2_relset_1('#skF_1', '#skF_1', '#skF_2')!='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_1302])).
% 5.81/2.23  tff(c_1311, plain, (k2_funct_1('#skF_2')='#skF_3' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_62, c_58, c_889, c_944, c_1305])).
% 5.81/2.23  tff(c_1312, plain, (k2_funct_1('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_241, c_1311])).
% 5.81/2.23  tff(c_1072, plain, (![A_151, B_152]: (k2_funct_2(A_151, B_152)=k2_funct_1(B_152) | ~m1_subset_1(B_152, k1_zfmisc_1(k2_zfmisc_1(A_151, A_151))) | ~v3_funct_2(B_152, A_151, A_151) | ~v1_funct_2(B_152, A_151, A_151) | ~v1_funct_1(B_152))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.81/2.23  tff(c_1084, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_1072])).
% 5.81/2.23  tff(c_1092, plain, (k2_funct_2('#skF_1', '#skF_2')=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1084])).
% 5.81/2.23  tff(c_54, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_2('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.81/2.23  tff(c_1097, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1092, c_54])).
% 5.81/2.23  tff(c_1313, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1312, c_1097])).
% 5.81/2.23  tff(c_1317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_860, c_1313])).
% 5.81/2.23  tff(c_1319, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_204])).
% 5.81/2.23  tff(c_200, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_188])).
% 5.81/2.23  tff(c_2, plain, (![A_1]: (k2_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.81/2.23  tff(c_212, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_200, c_2])).
% 5.81/2.23  tff(c_222, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_212])).
% 5.81/2.23  tff(c_1321, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1319, c_222])).
% 5.81/2.23  tff(c_1337, plain, (![C_190, B_191, A_192]: (v5_relat_1(C_190, B_191) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_192, B_191))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.81/2.23  tff(c_1348, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_1337])).
% 5.81/2.23  tff(c_1477, plain, (![B_212, A_213]: (k2_relat_1(B_212)=A_213 | ~v2_funct_2(B_212, A_213) | ~v5_relat_1(B_212, A_213) | ~v1_relat_1(B_212))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.81/2.23  tff(c_1489, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1348, c_1477])).
% 5.81/2.23  tff(c_1502, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_1489])).
% 5.81/2.23  tff(c_1503, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1321, c_1502])).
% 5.81/2.23  tff(c_60, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 5.81/2.23  tff(c_1655, plain, (![C_227, B_228, A_229]: (v2_funct_2(C_227, B_228) | ~v3_funct_2(C_227, A_229, B_228) | ~v1_funct_1(C_227) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_229, B_228))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.81/2.23  tff(c_1664, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_1655])).
% 5.81/2.23  tff(c_1673, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_1664])).
% 5.81/2.23  tff(c_1675, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1503, c_1673])).
% 5.81/2.23  tff(c_1676, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_212])).
% 5.81/2.23  tff(c_117, plain, (![A_49]: (k1_xboole_0!=A_49 | k6_partfun1(A_49)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_77, c_113])).
% 5.81/2.23  tff(c_6, plain, (![A_2]: (k1_relat_1(k6_relat_1(A_2))=A_2)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.81/2.23  tff(c_78, plain, (![A_2]: (k1_relat_1(k6_partfun1(A_2))=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_6])).
% 5.81/2.23  tff(c_126, plain, (![A_49]: (k1_relat_1(k1_xboole_0)=A_49 | k1_xboole_0!=A_49)), inference(superposition, [status(thm), theory('equality')], [c_117, c_78])).
% 5.81/2.23  tff(c_1733, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1676, c_1676, c_126])).
% 5.81/2.23  tff(c_4, plain, (![A_1]: (k1_relat_1(A_1)!=k1_xboole_0 | k1_xboole_0=A_1 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.81/2.23  tff(c_211, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_200, c_4])).
% 5.81/2.23  tff(c_221, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_211])).
% 5.81/2.23  tff(c_1678, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1676, c_221])).
% 5.81/2.23  tff(c_1736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1733, c_1678])).
% 5.81/2.23  tff(c_1737, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_211])).
% 5.81/2.23  tff(c_1774, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_2', '#skF_3'), '#skF_3') | '#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1737, c_1737, c_204])).
% 5.81/2.23  tff(c_1775, plain, ('#skF_3'!='#skF_1'), inference(splitLeft, [status(thm)], [c_1774])).
% 5.81/2.23  tff(c_129, plain, (![A_49]: (k2_relat_1(k1_xboole_0)=A_49 | k1_xboole_0!=A_49)), inference(superposition, [status(thm), theory('equality')], [c_117, c_77])).
% 5.81/2.23  tff(c_1835, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1737, c_1737, c_129])).
% 5.81/2.23  tff(c_1781, plain, (![C_234, B_235, A_236]: (v5_relat_1(C_234, B_235) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_236, B_235))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.81/2.23  tff(c_1792, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_1781])).
% 5.81/2.23  tff(c_1884, plain, (![B_249, A_250]: (k2_relat_1(B_249)=A_250 | ~v2_funct_2(B_249, A_250) | ~v5_relat_1(B_249, A_250) | ~v1_relat_1(B_249))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.81/2.23  tff(c_1896, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1792, c_1884])).
% 5.81/2.23  tff(c_1908, plain, ('#skF_3'='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_1835, c_1896])).
% 5.81/2.23  tff(c_1909, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1775, c_1908])).
% 5.81/2.23  tff(c_2104, plain, (![C_268, B_269, A_270]: (v2_funct_2(C_268, B_269) | ~v3_funct_2(C_268, A_270, B_269) | ~v1_funct_1(C_268) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(A_270, B_269))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.81/2.23  tff(c_2113, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2104])).
% 5.81/2.23  tff(c_2124, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_2113])).
% 5.81/2.23  tff(c_2126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1909, c_2124])).
% 5.81/2.23  tff(c_2128, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_1774])).
% 5.81/2.23  tff(c_2131, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_1737])).
% 5.81/2.23  tff(c_42, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.81/2.23  tff(c_123, plain, (![A_49]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_49, A_49))) | k1_xboole_0!=A_49)), inference(superposition, [status(thm), theory('equality')], [c_117, c_42])).
% 5.81/2.23  tff(c_2679, plain, (![A_49]: (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_49, A_49))) | A_49!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2131, c_2131, c_123])).
% 5.81/2.23  tff(c_2772, plain, (![A_332, B_333, D_334]: (r2_relset_1(A_332, B_333, D_334, D_334) | ~m1_subset_1(D_334, k1_zfmisc_1(k2_zfmisc_1(A_332, B_333))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.81/2.23  tff(c_2786, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2679, c_2772])).
% 5.81/2.23  tff(c_2136, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_62])).
% 5.81/2.23  tff(c_2137, plain, (v3_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_60])).
% 5.81/2.23  tff(c_2138, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_64])).
% 5.81/2.23  tff(c_1738, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_211])).
% 5.81/2.23  tff(c_1769, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1737, c_1738])).
% 5.81/2.23  tff(c_2129, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_2128, c_1769])).
% 5.81/2.23  tff(c_1756, plain, (![A_49]: (k2_relat_1('#skF_3')=A_49 | A_49!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1737, c_1737, c_129])).
% 5.81/2.23  tff(c_2175, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_2128, c_1756])).
% 5.81/2.23  tff(c_2132, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_200])).
% 5.81/2.23  tff(c_10, plain, (![A_3]: (k5_relat_1(A_3, k6_relat_1(k2_relat_1(A_3)))=A_3 | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.81/2.23  tff(c_1739, plain, (![A_232]: (k5_relat_1(A_232, k6_partfun1(k2_relat_1(A_232)))=A_232 | ~v1_relat_1(A_232))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10])).
% 5.81/2.23  tff(c_1748, plain, (![A_232]: (k5_relat_1(A_232, k1_xboole_0)=A_232 | ~v1_relat_1(A_232) | k2_relat_1(A_232)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_115, c_1739])).
% 5.81/2.23  tff(c_2756, plain, (![A_331]: (k5_relat_1(A_331, '#skF_1')=A_331 | ~v1_relat_1(A_331) | k2_relat_1(A_331)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2131, c_2131, c_1748])).
% 5.81/2.23  tff(c_2759, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1' | k2_relat_1('#skF_1')!='#skF_1'), inference(resolution, [status(thm)], [c_2132, c_2756])).
% 5.81/2.23  tff(c_2765, plain, (k5_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2175, c_2759])).
% 5.81/2.23  tff(c_14, plain, (![A_4]: (v2_funct_1(k6_relat_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.81/2.23  tff(c_74, plain, (![A_4]: (v2_funct_1(k6_partfun1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_14])).
% 5.81/2.23  tff(c_136, plain, (![A_49]: (v2_funct_1(k1_xboole_0) | k1_xboole_0!=A_49)), inference(superposition, [status(thm), theory('equality')], [c_117, c_74])).
% 5.81/2.23  tff(c_155, plain, (![A_49]: (k1_xboole_0!=A_49)), inference(splitLeft, [status(thm)], [c_136])).
% 5.81/2.23  tff(c_161, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_155])).
% 5.81/2.23  tff(c_162, plain, (v2_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_136])).
% 5.81/2.23  tff(c_1760, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1737, c_162])).
% 5.81/2.23  tff(c_2130, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_1760])).
% 5.81/2.23  tff(c_1762, plain, (![A_4]: (A_4!='#skF_3' | k6_partfun1(A_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1737, c_1737, c_115])).
% 5.81/2.23  tff(c_2580, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_2128, c_1762])).
% 5.81/2.23  tff(c_16, plain, (![A_5, B_7]: (k2_funct_1(A_5)=B_7 | k6_relat_1(k1_relat_1(A_5))!=k5_relat_1(A_5, B_7) | k2_relat_1(A_5)!=k1_relat_1(B_7) | ~v2_funct_1(A_5) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.81/2.23  tff(c_2925, plain, (![A_359, B_360]: (k2_funct_1(A_359)=B_360 | k6_partfun1(k1_relat_1(A_359))!=k5_relat_1(A_359, B_360) | k2_relat_1(A_359)!=k1_relat_1(B_360) | ~v2_funct_1(A_359) | ~v1_funct_1(B_360) | ~v1_relat_1(B_360) | ~v1_funct_1(A_359) | ~v1_relat_1(A_359))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_16])).
% 5.81/2.23  tff(c_2934, plain, (![B_360]: (k2_funct_1('#skF_1')=B_360 | k5_relat_1('#skF_1', B_360)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_1')!=k1_relat_1(B_360) | ~v2_funct_1('#skF_1') | ~v1_funct_1(B_360) | ~v1_relat_1(B_360) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2129, c_2925])).
% 5.81/2.23  tff(c_3048, plain, (![B_364]: (k2_funct_1('#skF_1')=B_364 | k5_relat_1('#skF_1', B_364)!='#skF_1' | k1_relat_1(B_364)!='#skF_1' | ~v1_funct_1(B_364) | ~v1_relat_1(B_364))), inference(demodulation, [status(thm), theory('equality')], [c_2132, c_2138, c_2130, c_2175, c_2580, c_2934])).
% 5.81/2.23  tff(c_3051, plain, (k2_funct_1('#skF_1')='#skF_1' | k5_relat_1('#skF_1', '#skF_1')!='#skF_1' | k1_relat_1('#skF_1')!='#skF_1' | ~v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_2132, c_3048])).
% 5.81/2.23  tff(c_3057, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2138, c_2129, c_2765, c_3051])).
% 5.81/2.23  tff(c_2914, plain, (![A_357, B_358]: (k2_funct_2(A_357, B_358)=k2_funct_1(B_358) | ~m1_subset_1(B_358, k1_zfmisc_1(k2_zfmisc_1(A_357, A_357))) | ~v3_funct_2(B_358, A_357, A_357) | ~v1_funct_2(B_358, A_357, A_357) | ~v1_funct_1(B_358))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.81/2.23  tff(c_2917, plain, (![A_49]: (k2_funct_2(A_49, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_49, A_49) | ~v1_funct_2('#skF_1', A_49, A_49) | ~v1_funct_1('#skF_1') | A_49!='#skF_1')), inference(resolution, [status(thm)], [c_2679, c_2914])).
% 5.81/2.23  tff(c_2923, plain, (![A_49]: (k2_funct_2(A_49, '#skF_1')=k2_funct_1('#skF_1') | ~v3_funct_2('#skF_1', A_49, A_49) | ~v1_funct_2('#skF_1', A_49, A_49) | A_49!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2138, c_2917])).
% 5.81/2.23  tff(c_3120, plain, (![A_379]: (k2_funct_2(A_379, '#skF_1')='#skF_1' | ~v3_funct_2('#skF_1', A_379, A_379) | ~v1_funct_2('#skF_1', A_379, A_379) | A_379!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3057, c_2923])).
% 5.81/2.23  tff(c_3123, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1' | ~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2137, c_3120])).
% 5.81/2.23  tff(c_3126, plain, (k2_funct_2('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2136, c_3123])).
% 5.81/2.23  tff(c_220, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_201, c_2])).
% 5.81/2.23  tff(c_2199, plain, (k2_relat_1('#skF_2')!='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2131, c_2131, c_220])).
% 5.81/2.23  tff(c_2200, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2199])).
% 5.81/2.23  tff(c_2185, plain, (![C_277, B_278, A_279]: (v5_relat_1(C_277, B_278) | ~m1_subset_1(C_277, k1_zfmisc_1(k2_zfmisc_1(A_279, B_278))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.81/2.23  tff(c_2197, plain, (v5_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_2185])).
% 5.81/2.23  tff(c_2421, plain, (![B_301, A_302]: (k2_relat_1(B_301)=A_302 | ~v2_funct_2(B_301, A_302) | ~v5_relat_1(B_301, A_302) | ~v1_relat_1(B_301))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.81/2.23  tff(c_2430, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2197, c_2421])).
% 5.81/2.23  tff(c_2439, plain, (k2_relat_1('#skF_2')='#skF_1' | ~v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_201, c_2430])).
% 5.81/2.23  tff(c_2440, plain, (~v2_funct_2('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2200, c_2439])).
% 5.81/2.23  tff(c_2522, plain, (![C_312, B_313, A_314]: (v2_funct_2(C_312, B_313) | ~v3_funct_2(C_312, A_314, B_313) | ~v1_funct_1(C_312) | ~m1_subset_1(C_312, k1_zfmisc_1(k2_zfmisc_1(A_314, B_313))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.81/2.23  tff(c_2531, plain, (v2_funct_2('#skF_2', '#skF_1') | ~v3_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_66, c_2522])).
% 5.81/2.23  tff(c_2539, plain, (v2_funct_2('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_2531])).
% 5.81/2.23  tff(c_2541, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2440, c_2539])).
% 5.81/2.23  tff(c_2542, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_2199])).
% 5.81/2.23  tff(c_219, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_201, c_4])).
% 5.81/2.23  tff(c_2183, plain, (k1_relat_1('#skF_2')!='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2131, c_2131, c_219])).
% 5.81/2.23  tff(c_2184, plain, (k1_relat_1('#skF_2')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2183])).
% 5.81/2.23  tff(c_2547, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2542, c_2184])).
% 5.81/2.23  tff(c_2557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2129, c_2547])).
% 5.81/2.23  tff(c_2558, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_2183])).
% 5.81/2.23  tff(c_2134, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_54])).
% 5.81/2.23  tff(c_2632, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k2_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2558, c_2134])).
% 5.81/2.23  tff(c_3127, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3126, c_2632])).
% 5.81/2.23  tff(c_3130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2786, c_3127])).
% 5.81/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.23  
% 5.81/2.23  Inference rules
% 5.81/2.23  ----------------------
% 5.81/2.23  #Ref     : 9
% 5.81/2.23  #Sup     : 637
% 5.81/2.23  #Fact    : 0
% 5.81/2.23  #Define  : 0
% 5.81/2.23  #Split   : 22
% 5.81/2.23  #Chain   : 0
% 5.81/2.23  #Close   : 0
% 5.81/2.23  
% 5.81/2.23  Ordering : KBO
% 5.81/2.23  
% 5.81/2.23  Simplification rules
% 5.81/2.23  ----------------------
% 5.81/2.23  #Subsume      : 132
% 5.81/2.23  #Demod        : 690
% 5.81/2.23  #Tautology    : 311
% 5.81/2.23  #SimpNegUnit  : 17
% 5.81/2.23  #BackRed      : 65
% 5.81/2.23  
% 5.81/2.23  #Partial instantiations: 0
% 5.81/2.23  #Strategies tried      : 1
% 5.81/2.23  
% 5.81/2.23  Timing (in seconds)
% 5.81/2.23  ----------------------
% 5.81/2.23  Preprocessing        : 0.58
% 5.81/2.23  Parsing              : 0.32
% 5.81/2.23  CNF conversion       : 0.04
% 5.81/2.23  Main loop            : 0.84
% 5.81/2.23  Inferencing          : 0.28
% 5.81/2.23  Reduction            : 0.31
% 5.81/2.23  Demodulation         : 0.22
% 5.81/2.23  BG Simplification    : 0.04
% 5.81/2.23  Subsumption          : 0.14
% 5.81/2.23  Abstraction          : 0.04
% 5.81/2.23  MUC search           : 0.00
% 5.81/2.23  Cooper               : 0.00
% 5.81/2.23  Total                : 1.49
% 5.81/2.23  Index Insertion      : 0.00
% 5.81/2.23  Index Deletion       : 0.00
% 5.81/2.23  Index Matching       : 0.00
% 5.81/2.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
