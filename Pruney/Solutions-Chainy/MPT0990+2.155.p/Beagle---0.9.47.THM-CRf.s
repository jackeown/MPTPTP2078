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
% DateTime   : Thu Dec  3 10:13:19 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 831 expanded)
%              Number of leaves         :   42 ( 312 expanded)
%              Depth                    :   18
%              Number of atoms          :  357 (3520 expanded)
%              Number of equality atoms :  122 (1233 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_195,negated_conjecture,(
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

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_152,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_90,axiom,(
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

tff(f_140,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_150,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_136,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_169,axiom,(
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

tff(f_53,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_51,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(c_56,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_100,plain,(
    ! [B_54,A_55] :
      ( v1_relat_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_100])).

tff(c_118,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_109])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_106,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_74,c_100])).

tff(c_115,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_106])).

tff(c_78,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_62,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_76,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_148,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_relset_1(A_62,B_63,C_64) = k1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_159,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_148])).

tff(c_252,plain,(
    ! [B_80,A_81,C_82] :
      ( k1_xboole_0 = B_80
      | k1_relset_1(A_81,B_80,C_82) = A_81
      | ~ v1_funct_2(C_82,A_81,B_80)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_258,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_252])).

tff(c_266,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_159,c_258])).

tff(c_267,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_266])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_180,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_186,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_180])).

tff(c_192,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_186])).

tff(c_52,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_20,plain,(
    ! [A_12,B_14] :
      ( k2_funct_1(A_12) = B_14
      | k6_relat_1(k2_relat_1(A_12)) != k5_relat_1(B_14,A_12)
      | k2_relat_1(B_14) != k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_364,plain,(
    ! [A_96,B_97] :
      ( k2_funct_1(A_96) = B_97
      | k6_partfun1(k2_relat_1(A_96)) != k5_relat_1(B_97,A_96)
      | k2_relat_1(B_97) != k1_relat_1(A_96)
      | ~ v2_funct_1(A_96)
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97)
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_20])).

tff(c_370,plain,(
    ! [B_97] :
      ( k2_funct_1('#skF_3') = B_97
      | k5_relat_1(B_97,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_97) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_364])).

tff(c_377,plain,(
    ! [B_98] :
      ( k2_funct_1('#skF_3') = B_98
      | k5_relat_1(B_98,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_98) != '#skF_1'
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_78,c_62,c_267,c_370])).

tff(c_383,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_118,c_377])).

tff(c_393,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_383])).

tff(c_394,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_393])).

tff(c_399,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_48,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_138,plain,(
    ! [A_59,B_60,D_61] :
      ( r2_relset_1(A_59,B_60,D_61,D_61)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_145,plain,(
    ! [A_34] : r2_relset_1(A_34,A_34,k6_partfun1(A_34),k6_partfun1(A_34)) ),
    inference(resolution,[status(thm)],[c_48,c_138])).

tff(c_193,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_180])).

tff(c_455,plain,(
    ! [E_119,A_116,B_121,F_117,D_120,C_118] :
      ( k1_partfun1(A_116,B_121,C_118,D_120,E_119,F_117) = k5_relat_1(E_119,F_117)
      | ~ m1_subset_1(F_117,k1_zfmisc_1(k2_zfmisc_1(C_118,D_120)))
      | ~ v1_funct_1(F_117)
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_116,B_121)))
      | ~ v1_funct_1(E_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_461,plain,(
    ! [A_116,B_121,E_119] :
      ( k1_partfun1(A_116,B_121,'#skF_2','#skF_1',E_119,'#skF_4') = k5_relat_1(E_119,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_116,B_121)))
      | ~ v1_funct_1(E_119) ) ),
    inference(resolution,[status(thm)],[c_68,c_455])).

tff(c_497,plain,(
    ! [A_126,B_127,E_128] :
      ( k1_partfun1(A_126,B_127,'#skF_2','#skF_1',E_128,'#skF_4') = k5_relat_1(E_128,'#skF_4')
      | ~ m1_subset_1(E_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ v1_funct_1(E_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_461])).

tff(c_503,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_497])).

tff(c_510,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_503])).

tff(c_64,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_340,plain,(
    ! [D_92,C_93,A_94,B_95] :
      ( D_92 = C_93
      | ~ r2_relset_1(A_94,B_95,C_93,D_92)
      | ~ m1_subset_1(D_92,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_348,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_64,c_340])).

tff(c_363,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_348])).

tff(c_400,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_363])).

tff(c_515,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_400])).

tff(c_521,plain,(
    ! [B_133,F_129,C_132,E_130,D_134,A_131] :
      ( m1_subset_1(k1_partfun1(A_131,B_133,C_132,D_134,E_130,F_129),k1_zfmisc_1(k2_zfmisc_1(A_131,D_134)))
      | ~ m1_subset_1(F_129,k1_zfmisc_1(k2_zfmisc_1(C_132,D_134)))
      | ~ v1_funct_1(F_129)
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_131,B_133)))
      | ~ v1_funct_1(E_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_569,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_521])).

tff(c_594,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_569])).

tff(c_604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_515,c_594])).

tff(c_605,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_363])).

tff(c_1001,plain,(
    ! [A_167,B_168,C_169,D_170] :
      ( k2_relset_1(A_167,B_168,C_169) = B_168
      | ~ r2_relset_1(B_168,B_168,k1_partfun1(B_168,A_167,A_167,B_168,D_170,C_169),k6_partfun1(B_168))
      | ~ m1_subset_1(D_170,k1_zfmisc_1(k2_zfmisc_1(B_168,A_167)))
      | ~ v1_funct_2(D_170,B_168,A_167)
      | ~ v1_funct_1(D_170)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168)))
      | ~ v1_funct_2(C_169,A_167,B_168)
      | ~ v1_funct_1(C_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1007,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_1001])).

tff(c_1011,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_78,c_76,c_74,c_145,c_193,c_1007])).

tff(c_1013,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_399,c_1011])).

tff(c_1014,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_160,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_148])).

tff(c_261,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_252])).

tff(c_270,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_160,c_261])).

tff(c_271,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_270])).

tff(c_1015,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_79,plain,(
    ! [A_12,B_14] :
      ( k2_funct_1(A_12) = B_14
      | k6_partfun1(k2_relat_1(A_12)) != k5_relat_1(B_14,A_12)
      | k2_relat_1(B_14) != k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_20])).

tff(c_1019,plain,(
    ! [B_14] :
      ( k2_funct_1('#skF_4') = B_14
      | k5_relat_1(B_14,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_14) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1015,c_79])).

tff(c_1023,plain,(
    ! [B_14] :
      ( k2_funct_1('#skF_4') = B_14
      | k5_relat_1(B_14,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_14) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_72,c_271,c_1019])).

tff(c_1244,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1023])).

tff(c_10,plain,(
    ! [A_9] : v2_funct_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_82,plain,(
    ! [A_9] : v2_funct_1(k6_partfun1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_10])).

tff(c_1083,plain,(
    ! [B_191,C_188,A_186,E_189,F_187,D_190] :
      ( k1_partfun1(A_186,B_191,C_188,D_190,E_189,F_187) = k5_relat_1(E_189,F_187)
      | ~ m1_subset_1(F_187,k1_zfmisc_1(k2_zfmisc_1(C_188,D_190)))
      | ~ v1_funct_1(F_187)
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(A_186,B_191)))
      | ~ v1_funct_1(E_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1089,plain,(
    ! [A_186,B_191,E_189] :
      ( k1_partfun1(A_186,B_191,'#skF_2','#skF_1',E_189,'#skF_4') = k5_relat_1(E_189,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_189,k1_zfmisc_1(k2_zfmisc_1(A_186,B_191)))
      | ~ v1_funct_1(E_189) ) ),
    inference(resolution,[status(thm)],[c_68,c_1083])).

tff(c_1125,plain,(
    ! [A_196,B_197,E_198] :
      ( k1_partfun1(A_196,B_197,'#skF_2','#skF_1',E_198,'#skF_4') = k5_relat_1(E_198,'#skF_4')
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197)))
      | ~ v1_funct_1(E_198) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1089])).

tff(c_1131,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1125])).

tff(c_1138,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1131])).

tff(c_1029,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_363])).

tff(c_1143,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1138,c_1029])).

tff(c_1149,plain,(
    ! [F_199,D_204,B_203,E_200,C_202,A_201] :
      ( m1_subset_1(k1_partfun1(A_201,B_203,C_202,D_204,E_200,F_199),k1_zfmisc_1(k2_zfmisc_1(A_201,D_204)))
      | ~ m1_subset_1(F_199,k1_zfmisc_1(k2_zfmisc_1(C_202,D_204)))
      | ~ v1_funct_1(F_199)
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_201,B_203)))
      | ~ v1_funct_1(E_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1197,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1138,c_1149])).

tff(c_1222,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_1197])).

tff(c_1232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1143,c_1222])).

tff(c_1233,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_363])).

tff(c_1299,plain,(
    ! [C_222,F_221,E_223,B_225,A_220,D_224] :
      ( k1_partfun1(A_220,B_225,C_222,D_224,E_223,F_221) = k5_relat_1(E_223,F_221)
      | ~ m1_subset_1(F_221,k1_zfmisc_1(k2_zfmisc_1(C_222,D_224)))
      | ~ v1_funct_1(F_221)
      | ~ m1_subset_1(E_223,k1_zfmisc_1(k2_zfmisc_1(A_220,B_225)))
      | ~ v1_funct_1(E_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1305,plain,(
    ! [A_220,B_225,E_223] :
      ( k1_partfun1(A_220,B_225,'#skF_2','#skF_1',E_223,'#skF_4') = k5_relat_1(E_223,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_223,k1_zfmisc_1(k2_zfmisc_1(A_220,B_225)))
      | ~ v1_funct_1(E_223) ) ),
    inference(resolution,[status(thm)],[c_68,c_1299])).

tff(c_1659,plain,(
    ! [A_240,B_241,E_242] :
      ( k1_partfun1(A_240,B_241,'#skF_2','#skF_1',E_242,'#skF_4') = k5_relat_1(E_242,'#skF_4')
      | ~ m1_subset_1(E_242,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241)))
      | ~ v1_funct_1(E_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1305])).

tff(c_1677,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1659])).

tff(c_1694,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1233,c_1677])).

tff(c_6,plain,(
    ! [A_6,B_8] :
      ( v2_funct_1(A_6)
      | k2_relat_1(B_8) != k1_relat_1(A_6)
      | ~ v2_funct_1(k5_relat_1(B_8,A_6))
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1704,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1694,c_6])).

tff(c_1710,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_72,c_115,c_78,c_82,c_192,c_271,c_1704])).

tff(c_1712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1244,c_1710])).

tff(c_1714,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1023])).

tff(c_1715,plain,(
    ! [B_243] :
      ( k2_funct_1('#skF_4') = B_243
      | k5_relat_1(B_243,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_243) != '#skF_2'
      | ~ v1_funct_1(B_243)
      | ~ v1_relat_1(B_243) ) ),
    inference(splitRight,[status(thm)],[c_1023])).

tff(c_1724,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_115,c_1715])).

tff(c_1734,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_192,c_1724])).

tff(c_1736,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1734])).

tff(c_1800,plain,(
    ! [A_263,E_266,F_264,D_267,C_265,B_268] :
      ( k1_partfun1(A_263,B_268,C_265,D_267,E_266,F_264) = k5_relat_1(E_266,F_264)
      | ~ m1_subset_1(F_264,k1_zfmisc_1(k2_zfmisc_1(C_265,D_267)))
      | ~ v1_funct_1(F_264)
      | ~ m1_subset_1(E_266,k1_zfmisc_1(k2_zfmisc_1(A_263,B_268)))
      | ~ v1_funct_1(E_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1806,plain,(
    ! [A_263,B_268,E_266] :
      ( k1_partfun1(A_263,B_268,'#skF_2','#skF_1',E_266,'#skF_4') = k5_relat_1(E_266,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_266,k1_zfmisc_1(k2_zfmisc_1(A_263,B_268)))
      | ~ v1_funct_1(E_266) ) ),
    inference(resolution,[status(thm)],[c_68,c_1800])).

tff(c_1815,plain,(
    ! [A_269,B_270,E_271] :
      ( k1_partfun1(A_269,B_270,'#skF_2','#skF_1',E_271,'#skF_4') = k5_relat_1(E_271,'#skF_4')
      | ~ m1_subset_1(E_271,k1_zfmisc_1(k2_zfmisc_1(A_269,B_270)))
      | ~ v1_funct_1(E_271) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1806])).

tff(c_1821,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_1815])).

tff(c_1828,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1233,c_1821])).

tff(c_1830,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1736,c_1828])).

tff(c_1831,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1734])).

tff(c_18,plain,(
    ! [A_11] :
      ( k5_relat_1(A_11,k2_funct_1(A_11)) = k6_relat_1(k1_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_80,plain,(
    ! [A_11] :
      ( k5_relat_1(A_11,k2_funct_1(A_11)) = k6_partfun1(k1_relat_1(A_11))
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_18])).

tff(c_1837,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k5_relat_1('#skF_4','#skF_3')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1831,c_80])).

tff(c_1850,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_72,c_1714,c_271,c_1837])).

tff(c_1852,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1014,c_1850])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:39:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.51/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.78  
% 4.51/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.79  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.51/1.79  
% 4.51/1.79  %Foreground sorts:
% 4.51/1.79  
% 4.51/1.79  
% 4.51/1.79  %Background operators:
% 4.51/1.79  
% 4.51/1.79  
% 4.51/1.79  %Foreground operators:
% 4.51/1.79  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.51/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.51/1.79  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.51/1.79  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.51/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.79  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.51/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.51/1.79  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.51/1.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.51/1.79  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.51/1.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.51/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.51/1.79  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.51/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.51/1.79  tff('#skF_1', type, '#skF_1': $i).
% 4.51/1.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.51/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.51/1.79  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.51/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.51/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.51/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.51/1.79  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.51/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.51/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.51/1.79  
% 4.51/1.81  tff(f_195, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.51/1.81  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.51/1.81  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.51/1.81  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.51/1.81  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.51/1.81  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.51/1.81  tff(f_152, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.51/1.81  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 4.51/1.81  tff(f_140, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.51/1.81  tff(f_106, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.51/1.81  tff(f_150, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.51/1.81  tff(f_136, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.51/1.81  tff(f_169, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.51/1.81  tff(f_53, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 4.51/1.81  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 4.51/1.81  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 4.51/1.81  tff(c_56, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.51/1.81  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.51/1.81  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.51/1.81  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.51/1.81  tff(c_100, plain, (![B_54, A_55]: (v1_relat_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.51/1.81  tff(c_109, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_68, c_100])).
% 4.51/1.81  tff(c_118, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_109])).
% 4.51/1.81  tff(c_74, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.51/1.81  tff(c_106, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_74, c_100])).
% 4.51/1.81  tff(c_115, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_106])).
% 4.51/1.81  tff(c_78, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.51/1.81  tff(c_62, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.51/1.81  tff(c_58, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.51/1.81  tff(c_76, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.51/1.81  tff(c_148, plain, (![A_62, B_63, C_64]: (k1_relset_1(A_62, B_63, C_64)=k1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.51/1.81  tff(c_159, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_148])).
% 4.51/1.81  tff(c_252, plain, (![B_80, A_81, C_82]: (k1_xboole_0=B_80 | k1_relset_1(A_81, B_80, C_82)=A_81 | ~v1_funct_2(C_82, A_81, B_80) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.51/1.81  tff(c_258, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_252])).
% 4.51/1.81  tff(c_266, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_159, c_258])).
% 4.51/1.81  tff(c_267, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_58, c_266])).
% 4.51/1.81  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.51/1.81  tff(c_180, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.51/1.81  tff(c_186, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_180])).
% 4.51/1.81  tff(c_192, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_186])).
% 4.51/1.81  tff(c_52, plain, (![A_41]: (k6_relat_1(A_41)=k6_partfun1(A_41))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.51/1.81  tff(c_20, plain, (![A_12, B_14]: (k2_funct_1(A_12)=B_14 | k6_relat_1(k2_relat_1(A_12))!=k5_relat_1(B_14, A_12) | k2_relat_1(B_14)!=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.51/1.81  tff(c_364, plain, (![A_96, B_97]: (k2_funct_1(A_96)=B_97 | k6_partfun1(k2_relat_1(A_96))!=k5_relat_1(B_97, A_96) | k2_relat_1(B_97)!=k1_relat_1(A_96) | ~v2_funct_1(A_96) | ~v1_funct_1(B_97) | ~v1_relat_1(B_97) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_20])).
% 4.51/1.81  tff(c_370, plain, (![B_97]: (k2_funct_1('#skF_3')=B_97 | k5_relat_1(B_97, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_97)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_97) | ~v1_relat_1(B_97) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_192, c_364])).
% 4.51/1.81  tff(c_377, plain, (![B_98]: (k2_funct_1('#skF_3')=B_98 | k5_relat_1(B_98, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_98)!='#skF_1' | ~v1_funct_1(B_98) | ~v1_relat_1(B_98))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_78, c_62, c_267, c_370])).
% 4.51/1.81  tff(c_383, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_118, c_377])).
% 4.51/1.81  tff(c_393, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_383])).
% 4.51/1.81  tff(c_394, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_56, c_393])).
% 4.51/1.81  tff(c_399, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_394])).
% 4.51/1.81  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.51/1.81  tff(c_48, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.51/1.81  tff(c_138, plain, (![A_59, B_60, D_61]: (r2_relset_1(A_59, B_60, D_61, D_61) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.51/1.81  tff(c_145, plain, (![A_34]: (r2_relset_1(A_34, A_34, k6_partfun1(A_34), k6_partfun1(A_34)))), inference(resolution, [status(thm)], [c_48, c_138])).
% 4.51/1.81  tff(c_193, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_180])).
% 4.51/1.81  tff(c_455, plain, (![E_119, A_116, B_121, F_117, D_120, C_118]: (k1_partfun1(A_116, B_121, C_118, D_120, E_119, F_117)=k5_relat_1(E_119, F_117) | ~m1_subset_1(F_117, k1_zfmisc_1(k2_zfmisc_1(C_118, D_120))) | ~v1_funct_1(F_117) | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_116, B_121))) | ~v1_funct_1(E_119))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.51/1.81  tff(c_461, plain, (![A_116, B_121, E_119]: (k1_partfun1(A_116, B_121, '#skF_2', '#skF_1', E_119, '#skF_4')=k5_relat_1(E_119, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_116, B_121))) | ~v1_funct_1(E_119))), inference(resolution, [status(thm)], [c_68, c_455])).
% 4.51/1.81  tff(c_497, plain, (![A_126, B_127, E_128]: (k1_partfun1(A_126, B_127, '#skF_2', '#skF_1', E_128, '#skF_4')=k5_relat_1(E_128, '#skF_4') | ~m1_subset_1(E_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~v1_funct_1(E_128))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_461])).
% 4.51/1.81  tff(c_503, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_497])).
% 4.51/1.81  tff(c_510, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_503])).
% 4.51/1.81  tff(c_64, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.51/1.81  tff(c_340, plain, (![D_92, C_93, A_94, B_95]: (D_92=C_93 | ~r2_relset_1(A_94, B_95, C_93, D_92) | ~m1_subset_1(D_92, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.51/1.81  tff(c_348, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_64, c_340])).
% 4.51/1.81  tff(c_363, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_348])).
% 4.51/1.81  tff(c_400, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_363])).
% 4.51/1.81  tff(c_515, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_510, c_400])).
% 4.51/1.81  tff(c_521, plain, (![B_133, F_129, C_132, E_130, D_134, A_131]: (m1_subset_1(k1_partfun1(A_131, B_133, C_132, D_134, E_130, F_129), k1_zfmisc_1(k2_zfmisc_1(A_131, D_134))) | ~m1_subset_1(F_129, k1_zfmisc_1(k2_zfmisc_1(C_132, D_134))) | ~v1_funct_1(F_129) | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_131, B_133))) | ~v1_funct_1(E_130))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.51/1.81  tff(c_569, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_510, c_521])).
% 4.51/1.81  tff(c_594, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_569])).
% 4.51/1.81  tff(c_604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_515, c_594])).
% 4.51/1.81  tff(c_605, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_363])).
% 4.51/1.81  tff(c_1001, plain, (![A_167, B_168, C_169, D_170]: (k2_relset_1(A_167, B_168, C_169)=B_168 | ~r2_relset_1(B_168, B_168, k1_partfun1(B_168, A_167, A_167, B_168, D_170, C_169), k6_partfun1(B_168)) | ~m1_subset_1(D_170, k1_zfmisc_1(k2_zfmisc_1(B_168, A_167))) | ~v1_funct_2(D_170, B_168, A_167) | ~v1_funct_1(D_170) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))) | ~v1_funct_2(C_169, A_167, B_168) | ~v1_funct_1(C_169))), inference(cnfTransformation, [status(thm)], [f_169])).
% 4.51/1.81  tff(c_1007, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_605, c_1001])).
% 4.51/1.81  tff(c_1011, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_78, c_76, c_74, c_145, c_193, c_1007])).
% 4.51/1.81  tff(c_1013, plain, $false, inference(negUnitSimplification, [status(thm)], [c_399, c_1011])).
% 4.51/1.81  tff(c_1014, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_394])).
% 4.51/1.81  tff(c_60, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_195])).
% 4.51/1.81  tff(c_160, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_148])).
% 4.51/1.81  tff(c_261, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_252])).
% 4.51/1.81  tff(c_270, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_160, c_261])).
% 4.51/1.81  tff(c_271, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_60, c_270])).
% 4.51/1.81  tff(c_1015, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_394])).
% 4.51/1.81  tff(c_79, plain, (![A_12, B_14]: (k2_funct_1(A_12)=B_14 | k6_partfun1(k2_relat_1(A_12))!=k5_relat_1(B_14, A_12) | k2_relat_1(B_14)!=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_20])).
% 4.51/1.81  tff(c_1019, plain, (![B_14]: (k2_funct_1('#skF_4')=B_14 | k5_relat_1(B_14, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_14)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1015, c_79])).
% 4.51/1.81  tff(c_1023, plain, (![B_14]: (k2_funct_1('#skF_4')=B_14 | k5_relat_1(B_14, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_14)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_72, c_271, c_1019])).
% 4.51/1.81  tff(c_1244, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1023])).
% 4.51/1.81  tff(c_10, plain, (![A_9]: (v2_funct_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.51/1.81  tff(c_82, plain, (![A_9]: (v2_funct_1(k6_partfun1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_10])).
% 4.51/1.81  tff(c_1083, plain, (![B_191, C_188, A_186, E_189, F_187, D_190]: (k1_partfun1(A_186, B_191, C_188, D_190, E_189, F_187)=k5_relat_1(E_189, F_187) | ~m1_subset_1(F_187, k1_zfmisc_1(k2_zfmisc_1(C_188, D_190))) | ~v1_funct_1(F_187) | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(A_186, B_191))) | ~v1_funct_1(E_189))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.51/1.81  tff(c_1089, plain, (![A_186, B_191, E_189]: (k1_partfun1(A_186, B_191, '#skF_2', '#skF_1', E_189, '#skF_4')=k5_relat_1(E_189, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_189, k1_zfmisc_1(k2_zfmisc_1(A_186, B_191))) | ~v1_funct_1(E_189))), inference(resolution, [status(thm)], [c_68, c_1083])).
% 4.51/1.81  tff(c_1125, plain, (![A_196, B_197, E_198]: (k1_partfun1(A_196, B_197, '#skF_2', '#skF_1', E_198, '#skF_4')=k5_relat_1(E_198, '#skF_4') | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))) | ~v1_funct_1(E_198))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1089])).
% 4.51/1.81  tff(c_1131, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1125])).
% 4.51/1.81  tff(c_1138, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1131])).
% 4.51/1.81  tff(c_1029, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_363])).
% 4.51/1.81  tff(c_1143, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1138, c_1029])).
% 4.51/1.81  tff(c_1149, plain, (![F_199, D_204, B_203, E_200, C_202, A_201]: (m1_subset_1(k1_partfun1(A_201, B_203, C_202, D_204, E_200, F_199), k1_zfmisc_1(k2_zfmisc_1(A_201, D_204))) | ~m1_subset_1(F_199, k1_zfmisc_1(k2_zfmisc_1(C_202, D_204))) | ~v1_funct_1(F_199) | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_201, B_203))) | ~v1_funct_1(E_200))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.51/1.81  tff(c_1197, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1138, c_1149])).
% 4.51/1.81  tff(c_1222, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_1197])).
% 4.51/1.81  tff(c_1232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1143, c_1222])).
% 4.51/1.81  tff(c_1233, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_363])).
% 4.51/1.81  tff(c_1299, plain, (![C_222, F_221, E_223, B_225, A_220, D_224]: (k1_partfun1(A_220, B_225, C_222, D_224, E_223, F_221)=k5_relat_1(E_223, F_221) | ~m1_subset_1(F_221, k1_zfmisc_1(k2_zfmisc_1(C_222, D_224))) | ~v1_funct_1(F_221) | ~m1_subset_1(E_223, k1_zfmisc_1(k2_zfmisc_1(A_220, B_225))) | ~v1_funct_1(E_223))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.51/1.81  tff(c_1305, plain, (![A_220, B_225, E_223]: (k1_partfun1(A_220, B_225, '#skF_2', '#skF_1', E_223, '#skF_4')=k5_relat_1(E_223, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_223, k1_zfmisc_1(k2_zfmisc_1(A_220, B_225))) | ~v1_funct_1(E_223))), inference(resolution, [status(thm)], [c_68, c_1299])).
% 4.51/1.81  tff(c_1659, plain, (![A_240, B_241, E_242]: (k1_partfun1(A_240, B_241, '#skF_2', '#skF_1', E_242, '#skF_4')=k5_relat_1(E_242, '#skF_4') | ~m1_subset_1(E_242, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))) | ~v1_funct_1(E_242))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1305])).
% 4.51/1.81  tff(c_1677, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1659])).
% 4.51/1.81  tff(c_1694, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1233, c_1677])).
% 4.51/1.81  tff(c_6, plain, (![A_6, B_8]: (v2_funct_1(A_6) | k2_relat_1(B_8)!=k1_relat_1(A_6) | ~v2_funct_1(k5_relat_1(B_8, A_6)) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.51/1.81  tff(c_1704, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1694, c_6])).
% 4.51/1.81  tff(c_1710, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_72, c_115, c_78, c_82, c_192, c_271, c_1704])).
% 4.51/1.81  tff(c_1712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1244, c_1710])).
% 4.51/1.81  tff(c_1714, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1023])).
% 4.51/1.81  tff(c_1715, plain, (![B_243]: (k2_funct_1('#skF_4')=B_243 | k5_relat_1(B_243, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_243)!='#skF_2' | ~v1_funct_1(B_243) | ~v1_relat_1(B_243))), inference(splitRight, [status(thm)], [c_1023])).
% 4.51/1.81  tff(c_1724, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_115, c_1715])).
% 4.51/1.81  tff(c_1734, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_192, c_1724])).
% 4.51/1.81  tff(c_1736, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1734])).
% 4.51/1.81  tff(c_1800, plain, (![A_263, E_266, F_264, D_267, C_265, B_268]: (k1_partfun1(A_263, B_268, C_265, D_267, E_266, F_264)=k5_relat_1(E_266, F_264) | ~m1_subset_1(F_264, k1_zfmisc_1(k2_zfmisc_1(C_265, D_267))) | ~v1_funct_1(F_264) | ~m1_subset_1(E_266, k1_zfmisc_1(k2_zfmisc_1(A_263, B_268))) | ~v1_funct_1(E_266))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.51/1.81  tff(c_1806, plain, (![A_263, B_268, E_266]: (k1_partfun1(A_263, B_268, '#skF_2', '#skF_1', E_266, '#skF_4')=k5_relat_1(E_266, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_266, k1_zfmisc_1(k2_zfmisc_1(A_263, B_268))) | ~v1_funct_1(E_266))), inference(resolution, [status(thm)], [c_68, c_1800])).
% 4.51/1.81  tff(c_1815, plain, (![A_269, B_270, E_271]: (k1_partfun1(A_269, B_270, '#skF_2', '#skF_1', E_271, '#skF_4')=k5_relat_1(E_271, '#skF_4') | ~m1_subset_1(E_271, k1_zfmisc_1(k2_zfmisc_1(A_269, B_270))) | ~v1_funct_1(E_271))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1806])).
% 4.51/1.81  tff(c_1821, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_74, c_1815])).
% 4.51/1.81  tff(c_1828, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1233, c_1821])).
% 4.51/1.81  tff(c_1830, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1736, c_1828])).
% 4.51/1.81  tff(c_1831, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1734])).
% 4.51/1.81  tff(c_18, plain, (![A_11]: (k5_relat_1(A_11, k2_funct_1(A_11))=k6_relat_1(k1_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.51/1.81  tff(c_80, plain, (![A_11]: (k5_relat_1(A_11, k2_funct_1(A_11))=k6_partfun1(k1_relat_1(A_11)) | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_18])).
% 4.51/1.81  tff(c_1837, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k5_relat_1('#skF_4', '#skF_3') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1831, c_80])).
% 4.51/1.81  tff(c_1850, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_72, c_1714, c_271, c_1837])).
% 4.51/1.81  tff(c_1852, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1014, c_1850])).
% 4.51/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.81  
% 4.51/1.81  Inference rules
% 4.51/1.81  ----------------------
% 4.51/1.81  #Ref     : 0
% 4.51/1.81  #Sup     : 373
% 4.51/1.81  #Fact    : 0
% 4.51/1.81  #Define  : 0
% 4.51/1.81  #Split   : 18
% 4.51/1.81  #Chain   : 0
% 4.51/1.81  #Close   : 0
% 4.51/1.81  
% 4.51/1.81  Ordering : KBO
% 4.51/1.81  
% 4.51/1.81  Simplification rules
% 4.51/1.81  ----------------------
% 4.51/1.81  #Subsume      : 2
% 4.51/1.81  #Demod        : 291
% 4.51/1.81  #Tautology    : 95
% 4.51/1.81  #SimpNegUnit  : 24
% 4.51/1.81  #BackRed      : 20
% 4.51/1.81  
% 4.51/1.81  #Partial instantiations: 0
% 4.51/1.81  #Strategies tried      : 1
% 4.51/1.81  
% 4.51/1.81  Timing (in seconds)
% 4.51/1.81  ----------------------
% 4.51/1.82  Preprocessing        : 0.37
% 4.51/1.82  Parsing              : 0.20
% 4.51/1.82  CNF conversion       : 0.02
% 4.51/1.82  Main loop            : 0.65
% 4.51/1.82  Inferencing          : 0.23
% 4.51/1.82  Reduction            : 0.22
% 4.51/1.82  Demodulation         : 0.15
% 4.51/1.82  BG Simplification    : 0.03
% 4.51/1.82  Subsumption          : 0.12
% 4.51/1.82  Abstraction          : 0.03
% 4.51/1.82  MUC search           : 0.00
% 4.51/1.82  Cooper               : 0.00
% 4.82/1.82  Total                : 1.08
% 4.82/1.82  Index Insertion      : 0.00
% 4.82/1.82  Index Deletion       : 0.00
% 4.82/1.82  Index Matching       : 0.00
% 4.82/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
