%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:03 EST 2020

% Result     : Theorem 9.37s
% Output     : CNFRefutation 9.45s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 482 expanded)
%              Number of leaves         :   37 ( 200 expanded)
%              Depth                    :   14
%              Number of atoms          :  335 (2494 expanded)
%              Number of equality atoms :  108 ( 766 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_156,negated_conjecture,(
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

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_90,axiom,(
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

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_114,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_52,axiom,(
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

tff(f_112,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(c_44,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_118,plain,(
    ! [A_49,B_50,C_51] :
      ( k1_relset_1(A_49,B_50,C_51) = k1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_125,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_118])).

tff(c_156,plain,(
    ! [B_60,A_61,C_62] :
      ( k1_xboole_0 = B_60
      | k1_relset_1(A_61,B_60,C_62) = A_61
      | ~ v1_funct_2(C_62,A_61,B_60)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_159,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_156])).

tff(c_165,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_125,c_159])).

tff(c_166,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_165])).

tff(c_83,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_90,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_83])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_91,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_83])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_50,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_54,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_99,plain,(
    ! [A_45,B_46,C_47] :
      ( k2_relset_1(A_45,B_46,C_47) = k2_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_105,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_99])).

tff(c_108,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_105])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_64,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_126,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_118])).

tff(c_162,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_156])).

tff(c_169,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_126,c_162])).

tff(c_170,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_169])).

tff(c_36,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_6,plain,(
    ! [A_2,B_4] :
      ( k2_funct_1(A_2) = B_4
      | k6_relat_1(k1_relat_1(A_2)) != k5_relat_1(A_2,B_4)
      | k2_relat_1(A_2) != k1_relat_1(B_4)
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8395,plain,(
    ! [A_378,B_379] :
      ( k2_funct_1(A_378) = B_379
      | k6_partfun1(k1_relat_1(A_378)) != k5_relat_1(A_378,B_379)
      | k2_relat_1(A_378) != k1_relat_1(B_379)
      | ~ v2_funct_1(A_378)
      | ~ v1_funct_1(B_379)
      | ~ v1_relat_1(B_379)
      | ~ v1_funct_1(A_378)
      | ~ v1_relat_1(A_378) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6])).

tff(c_8397,plain,(
    ! [B_379] :
      ( k2_funct_1('#skF_3') = B_379
      | k5_relat_1('#skF_3',B_379) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_379)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_379)
      | ~ v1_relat_1(B_379)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_8395])).

tff(c_8486,plain,(
    ! [B_383] :
      ( k2_funct_1('#skF_3') = B_383
      | k5_relat_1('#skF_3',B_383) != k6_partfun1('#skF_1')
      | k1_relat_1(B_383) != '#skF_2'
      | ~ v1_funct_1(B_383)
      | ~ v1_relat_1(B_383) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_66,c_50,c_108,c_8397])).

tff(c_8495,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_8486])).

tff(c_8502,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_166,c_8495])).

tff(c_8503,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_8502])).

tff(c_301,plain,(
    ! [C_89,B_92,E_91,F_88,A_93,D_90] :
      ( k1_partfun1(A_93,B_92,C_89,D_90,E_91,F_88) = k5_relat_1(E_91,F_88)
      | ~ m1_subset_1(F_88,k1_zfmisc_1(k2_zfmisc_1(C_89,D_90)))
      | ~ v1_funct_1(F_88)
      | ~ m1_subset_1(E_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92)))
      | ~ v1_funct_1(E_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_303,plain,(
    ! [A_93,B_92,E_91] :
      ( k1_partfun1(A_93,B_92,'#skF_2','#skF_1',E_91,'#skF_4') = k5_relat_1(E_91,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92)))
      | ~ v1_funct_1(E_91) ) ),
    inference(resolution,[status(thm)],[c_56,c_301])).

tff(c_348,plain,(
    ! [A_100,B_101,E_102] :
      ( k1_partfun1(A_100,B_101,'#skF_2','#skF_1',E_102,'#skF_4') = k5_relat_1(E_102,'#skF_4')
      | ~ m1_subset_1(E_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ v1_funct_1(E_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_303])).

tff(c_354,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_348])).

tff(c_360,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_354])).

tff(c_52,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_203,plain,(
    ! [D_66,C_67,A_68,B_69] :
      ( D_66 = C_67
      | ~ r2_relset_1(A_68,B_69,C_67,D_66)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_210,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_52,c_203])).

tff(c_232,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_436,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_232])).

tff(c_471,plain,(
    ! [F_112,A_109,C_111,B_113,D_110,E_114] :
      ( m1_subset_1(k1_partfun1(A_109,B_113,C_111,D_110,E_114,F_112),k1_zfmisc_1(k2_zfmisc_1(A_109,D_110)))
      | ~ m1_subset_1(F_112,k1_zfmisc_1(k2_zfmisc_1(C_111,D_110)))
      | ~ v1_funct_1(F_112)
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_109,B_113)))
      | ~ v1_funct_1(E_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_528,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_471])).

tff(c_557,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_528])).

tff(c_559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_436,c_557])).

tff(c_560,plain,
    ( ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_594,plain,(
    ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_560])).

tff(c_4,plain,(
    ! [A_1] :
      ( k5_relat_1(A_1,k2_funct_1(A_1)) = k6_relat_1(k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ! [A_1] :
      ( k5_relat_1(A_1,k2_funct_1(A_1)) = k6_partfun1(k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4])).

tff(c_219,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_funct_1(k2_funct_1(C_70))
      | k2_relset_1(A_71,B_72,C_70) != B_72
      | ~ v2_funct_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ v1_funct_2(C_70,A_71,B_72)
      | ~ v1_funct_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_225,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_219])).

tff(c_231,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_50,c_54,c_225])).

tff(c_38,plain,(
    ! [C_36,B_35,A_34] :
      ( m1_subset_1(k2_funct_1(C_36),k1_zfmisc_1(k2_zfmisc_1(B_35,A_34)))
      | k2_relset_1(A_34,B_35,C_36) != B_35
      | ~ v2_funct_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_2(C_36,A_34,B_35)
      | ~ v1_funct_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_805,plain,(
    ! [C_140,D_141,B_143,A_144,F_139,E_142] :
      ( k1_partfun1(A_144,B_143,C_140,D_141,E_142,F_139) = k5_relat_1(E_142,F_139)
      | ~ m1_subset_1(F_139,k1_zfmisc_1(k2_zfmisc_1(C_140,D_141)))
      | ~ v1_funct_1(F_139)
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_144,B_143)))
      | ~ v1_funct_1(E_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_811,plain,(
    ! [A_144,B_143,E_142] :
      ( k1_partfun1(A_144,B_143,'#skF_2','#skF_1',E_142,'#skF_4') = k5_relat_1(E_142,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_144,B_143)))
      | ~ v1_funct_1(E_142) ) ),
    inference(resolution,[status(thm)],[c_56,c_805])).

tff(c_824,plain,(
    ! [A_145,B_146,E_147] :
      ( k1_partfun1(A_145,B_146,'#skF_2','#skF_1',E_147,'#skF_4') = k5_relat_1(E_147,'#skF_4')
      | ~ m1_subset_1(E_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146)))
      | ~ v1_funct_1(E_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_811])).

tff(c_6882,plain,(
    ! [B_363,A_364,C_365] :
      ( k1_partfun1(B_363,A_364,'#skF_2','#skF_1',k2_funct_1(C_365),'#skF_4') = k5_relat_1(k2_funct_1(C_365),'#skF_4')
      | ~ v1_funct_1(k2_funct_1(C_365))
      | k2_relset_1(A_364,B_363,C_365) != B_363
      | ~ v2_funct_1(C_365)
      | ~ m1_subset_1(C_365,k1_zfmisc_1(k2_zfmisc_1(A_364,B_363)))
      | ~ v1_funct_2(C_365,A_364,B_363)
      | ~ v1_funct_1(C_365) ) ),
    inference(resolution,[status(thm)],[c_38,c_824])).

tff(c_6936,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_2','#skF_1',k2_funct_1('#skF_3'),'#skF_4') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_6882])).

tff(c_6986,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_2','#skF_1',k2_funct_1('#skF_3'),'#skF_4') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_50,c_54,c_231,c_6936])).

tff(c_873,plain,(
    ! [D_149,B_152,A_148,E_153,F_151,C_150] :
      ( m1_subset_1(k1_partfun1(A_148,B_152,C_150,D_149,E_153,F_151),k1_zfmisc_1(k2_zfmisc_1(A_148,D_149)))
      | ~ m1_subset_1(F_151,k1_zfmisc_1(k2_zfmisc_1(C_150,D_149)))
      | ~ v1_funct_1(F_151)
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_148,B_152)))
      | ~ v1_funct_1(E_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28,plain,(
    ! [B_19,A_18,C_20] :
      ( k1_xboole_0 = B_19
      | k1_relset_1(A_18,B_19,C_20) = A_18
      | ~ v1_funct_2(C_20,A_18,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_940,plain,(
    ! [D_149,B_152,A_148,E_153,F_151,C_150] :
      ( k1_xboole_0 = D_149
      | k1_relset_1(A_148,D_149,k1_partfun1(A_148,B_152,C_150,D_149,E_153,F_151)) = A_148
      | ~ v1_funct_2(k1_partfun1(A_148,B_152,C_150,D_149,E_153,F_151),A_148,D_149)
      | ~ m1_subset_1(F_151,k1_zfmisc_1(k2_zfmisc_1(C_150,D_149)))
      | ~ v1_funct_1(F_151)
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_148,B_152)))
      | ~ v1_funct_1(E_153) ) ),
    inference(resolution,[status(thm)],[c_873,c_28])).

tff(c_6997,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1',k1_partfun1('#skF_2','#skF_1','#skF_2','#skF_1',k2_funct_1('#skF_3'),'#skF_4')) = '#skF_2'
    | ~ v1_funct_2(k5_relat_1(k2_funct_1('#skF_3'),'#skF_4'),'#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6986,c_940])).

tff(c_7016,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1',k5_relat_1(k2_funct_1('#skF_3'),'#skF_4')) = '#skF_2'
    | ~ v1_funct_2(k5_relat_1(k2_funct_1('#skF_3'),'#skF_4'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_60,c_56,c_6986,c_6997])).

tff(c_7017,plain,
    ( k1_relset_1('#skF_2','#skF_1',k5_relat_1(k2_funct_1('#skF_3'),'#skF_4')) = '#skF_2'
    | ~ v1_funct_2(k5_relat_1(k2_funct_1('#skF_3'),'#skF_4'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_7016])).

tff(c_7029,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_7017])).

tff(c_7032,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_7029])).

tff(c_7036,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_50,c_54,c_7032])).

tff(c_7038,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_7017])).

tff(c_3513,plain,(
    ! [C_242,B_239,A_237,E_240,B_241,A_238] :
      ( k1_partfun1(A_238,B_239,B_241,A_237,E_240,k2_funct_1(C_242)) = k5_relat_1(E_240,k2_funct_1(C_242))
      | ~ v1_funct_1(k2_funct_1(C_242))
      | ~ m1_subset_1(E_240,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239)))
      | ~ v1_funct_1(E_240)
      | k2_relset_1(A_237,B_241,C_242) != B_241
      | ~ v2_funct_1(C_242)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_237,B_241)))
      | ~ v1_funct_2(C_242,A_237,B_241)
      | ~ v1_funct_1(C_242) ) ),
    inference(resolution,[status(thm)],[c_38,c_805])).

tff(c_3545,plain,(
    ! [B_241,A_237,C_242] :
      ( k1_partfun1('#skF_1','#skF_2',B_241,A_237,'#skF_3',k2_funct_1(C_242)) = k5_relat_1('#skF_3',k2_funct_1(C_242))
      | ~ v1_funct_1(k2_funct_1(C_242))
      | ~ v1_funct_1('#skF_3')
      | k2_relset_1(A_237,B_241,C_242) != B_241
      | ~ v2_funct_1(C_242)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_237,B_241)))
      | ~ v1_funct_2(C_242,A_237,B_241)
      | ~ v1_funct_1(C_242) ) ),
    inference(resolution,[status(thm)],[c_62,c_3513])).

tff(c_7520,plain,(
    ! [B_372,A_373,C_374] :
      ( k1_partfun1('#skF_1','#skF_2',B_372,A_373,'#skF_3',k2_funct_1(C_374)) = k5_relat_1('#skF_3',k2_funct_1(C_374))
      | ~ v1_funct_1(k2_funct_1(C_374))
      | k2_relset_1(A_373,B_372,C_374) != B_372
      | ~ v2_funct_1(C_374)
      | ~ m1_subset_1(C_374,k1_zfmisc_1(k2_zfmisc_1(A_373,B_372)))
      | ~ v1_funct_2(C_374,A_373,B_372)
      | ~ v1_funct_1(C_374) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3545])).

tff(c_7577,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_7520])).

tff(c_7630,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_50,c_54,c_231,c_7577])).

tff(c_30,plain,(
    ! [A_21,B_22,D_24,C_23,F_26,E_25] :
      ( m1_subset_1(k1_partfun1(A_21,B_22,C_23,D_24,E_25,F_26),k1_zfmisc_1(k2_zfmisc_1(A_21,D_24)))
      | ~ m1_subset_1(F_26,k1_zfmisc_1(k2_zfmisc_1(C_23,D_24)))
      | ~ v1_funct_1(F_26)
      | ~ m1_subset_1(E_25,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_1(E_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_8078,plain,
    ( m1_subset_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7630,c_30])).

tff(c_8097,plain,(
    m1_subset_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_231,c_7038,c_8078])).

tff(c_8245,plain,
    ( m1_subset_1(k6_partfun1(k1_relat_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_8097])).

tff(c_8390,plain,(
    m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_66,c_50,c_170,c_8245])).

tff(c_8392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_594,c_8390])).

tff(c_8393,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_560])).

tff(c_8686,plain,(
    ! [C_412,B_415,A_416,E_414,D_413,F_411] :
      ( k1_partfun1(A_416,B_415,C_412,D_413,E_414,F_411) = k5_relat_1(E_414,F_411)
      | ~ m1_subset_1(F_411,k1_zfmisc_1(k2_zfmisc_1(C_412,D_413)))
      | ~ v1_funct_1(F_411)
      | ~ m1_subset_1(E_414,k1_zfmisc_1(k2_zfmisc_1(A_416,B_415)))
      | ~ v1_funct_1(E_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_8692,plain,(
    ! [A_416,B_415,E_414] :
      ( k1_partfun1(A_416,B_415,'#skF_2','#skF_1',E_414,'#skF_4') = k5_relat_1(E_414,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_414,k1_zfmisc_1(k2_zfmisc_1(A_416,B_415)))
      | ~ v1_funct_1(E_414) ) ),
    inference(resolution,[status(thm)],[c_56,c_8686])).

tff(c_8705,plain,(
    ! [A_417,B_418,E_419] :
      ( k1_partfun1(A_417,B_418,'#skF_2','#skF_1',E_419,'#skF_4') = k5_relat_1(E_419,'#skF_4')
      | ~ m1_subset_1(E_419,k1_zfmisc_1(k2_zfmisc_1(A_417,B_418)))
      | ~ v1_funct_1(E_419) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_8692])).

tff(c_8717,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_8705])).

tff(c_8727,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8393,c_8717])).

tff(c_8729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8503,c_8727])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.37/3.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.37/3.83  
% 9.37/3.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.37/3.83  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.37/3.83  
% 9.37/3.83  %Foreground sorts:
% 9.37/3.83  
% 9.37/3.83  
% 9.37/3.83  %Background operators:
% 9.37/3.83  
% 9.37/3.83  
% 9.37/3.83  %Foreground operators:
% 9.37/3.83  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.37/3.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.37/3.83  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.37/3.83  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.37/3.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.37/3.83  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.37/3.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.37/3.83  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.37/3.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.37/3.83  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.37/3.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.37/3.83  tff('#skF_2', type, '#skF_2': $i).
% 9.37/3.83  tff('#skF_3', type, '#skF_3': $i).
% 9.37/3.83  tff('#skF_1', type, '#skF_1': $i).
% 9.37/3.83  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.37/3.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.37/3.83  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.37/3.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.37/3.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.37/3.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.37/3.83  tff('#skF_4', type, '#skF_4': $i).
% 9.37/3.83  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.37/3.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.37/3.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.37/3.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.37/3.83  
% 9.45/3.85  tff(f_156, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 9.45/3.85  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.45/3.85  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.45/3.85  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.45/3.85  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.45/3.85  tff(f_114, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.45/3.85  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 9.45/3.85  tff(f_112, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.45/3.85  tff(f_72, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.45/3.85  tff(f_102, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.45/3.85  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 9.45/3.85  tff(f_130, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 9.45/3.85  tff(c_44, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.45/3.85  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.45/3.85  tff(c_48, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.45/3.85  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.45/3.85  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.45/3.85  tff(c_118, plain, (![A_49, B_50, C_51]: (k1_relset_1(A_49, B_50, C_51)=k1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.45/3.85  tff(c_125, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_118])).
% 9.45/3.85  tff(c_156, plain, (![B_60, A_61, C_62]: (k1_xboole_0=B_60 | k1_relset_1(A_61, B_60, C_62)=A_61 | ~v1_funct_2(C_62, A_61, B_60) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.45/3.85  tff(c_159, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_156])).
% 9.45/3.85  tff(c_165, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_125, c_159])).
% 9.45/3.85  tff(c_166, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_48, c_165])).
% 9.45/3.85  tff(c_83, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.45/3.85  tff(c_90, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_83])).
% 9.45/3.85  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.45/3.85  tff(c_91, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_83])).
% 9.45/3.85  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.45/3.85  tff(c_50, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.45/3.85  tff(c_54, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.45/3.85  tff(c_99, plain, (![A_45, B_46, C_47]: (k2_relset_1(A_45, B_46, C_47)=k2_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.45/3.85  tff(c_105, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_99])).
% 9.45/3.85  tff(c_108, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_105])).
% 9.45/3.85  tff(c_46, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.45/3.85  tff(c_64, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.45/3.85  tff(c_126, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_118])).
% 9.45/3.85  tff(c_162, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_156])).
% 9.45/3.85  tff(c_169, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_126, c_162])).
% 9.45/3.85  tff(c_170, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_46, c_169])).
% 9.45/3.85  tff(c_36, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_114])).
% 9.45/3.85  tff(c_6, plain, (![A_2, B_4]: (k2_funct_1(A_2)=B_4 | k6_relat_1(k1_relat_1(A_2))!=k5_relat_1(A_2, B_4) | k2_relat_1(A_2)!=k1_relat_1(B_4) | ~v2_funct_1(A_2) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.45/3.85  tff(c_8395, plain, (![A_378, B_379]: (k2_funct_1(A_378)=B_379 | k6_partfun1(k1_relat_1(A_378))!=k5_relat_1(A_378, B_379) | k2_relat_1(A_378)!=k1_relat_1(B_379) | ~v2_funct_1(A_378) | ~v1_funct_1(B_379) | ~v1_relat_1(B_379) | ~v1_funct_1(A_378) | ~v1_relat_1(A_378))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6])).
% 9.45/3.85  tff(c_8397, plain, (![B_379]: (k2_funct_1('#skF_3')=B_379 | k5_relat_1('#skF_3', B_379)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_379) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_379) | ~v1_relat_1(B_379) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_170, c_8395])).
% 9.45/3.85  tff(c_8486, plain, (![B_383]: (k2_funct_1('#skF_3')=B_383 | k5_relat_1('#skF_3', B_383)!=k6_partfun1('#skF_1') | k1_relat_1(B_383)!='#skF_2' | ~v1_funct_1(B_383) | ~v1_relat_1(B_383))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_66, c_50, c_108, c_8397])).
% 9.45/3.85  tff(c_8495, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_8486])).
% 9.45/3.85  tff(c_8502, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_166, c_8495])).
% 9.45/3.85  tff(c_8503, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_8502])).
% 9.45/3.85  tff(c_301, plain, (![C_89, B_92, E_91, F_88, A_93, D_90]: (k1_partfun1(A_93, B_92, C_89, D_90, E_91, F_88)=k5_relat_1(E_91, F_88) | ~m1_subset_1(F_88, k1_zfmisc_1(k2_zfmisc_1(C_89, D_90))) | ~v1_funct_1(F_88) | ~m1_subset_1(E_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))) | ~v1_funct_1(E_91))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.45/3.85  tff(c_303, plain, (![A_93, B_92, E_91]: (k1_partfun1(A_93, B_92, '#skF_2', '#skF_1', E_91, '#skF_4')=k5_relat_1(E_91, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))) | ~v1_funct_1(E_91))), inference(resolution, [status(thm)], [c_56, c_301])).
% 9.45/3.85  tff(c_348, plain, (![A_100, B_101, E_102]: (k1_partfun1(A_100, B_101, '#skF_2', '#skF_1', E_102, '#skF_4')=k5_relat_1(E_102, '#skF_4') | ~m1_subset_1(E_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~v1_funct_1(E_102))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_303])).
% 9.45/3.85  tff(c_354, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_348])).
% 9.45/3.85  tff(c_360, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_354])).
% 9.45/3.85  tff(c_52, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 9.45/3.85  tff(c_203, plain, (![D_66, C_67, A_68, B_69]: (D_66=C_67 | ~r2_relset_1(A_68, B_69, C_67, D_66) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.45/3.85  tff(c_210, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_52, c_203])).
% 9.45/3.85  tff(c_232, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_210])).
% 9.45/3.85  tff(c_436, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_360, c_232])).
% 9.45/3.85  tff(c_471, plain, (![F_112, A_109, C_111, B_113, D_110, E_114]: (m1_subset_1(k1_partfun1(A_109, B_113, C_111, D_110, E_114, F_112), k1_zfmisc_1(k2_zfmisc_1(A_109, D_110))) | ~m1_subset_1(F_112, k1_zfmisc_1(k2_zfmisc_1(C_111, D_110))) | ~v1_funct_1(F_112) | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_109, B_113))) | ~v1_funct_1(E_114))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.45/3.85  tff(c_528, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_360, c_471])).
% 9.45/3.85  tff(c_557, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_528])).
% 9.45/3.85  tff(c_559, plain, $false, inference(negUnitSimplification, [status(thm)], [c_436, c_557])).
% 9.45/3.85  tff(c_560, plain, (~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_210])).
% 9.45/3.85  tff(c_594, plain, (~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_560])).
% 9.45/3.85  tff(c_4, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_relat_1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.45/3.85  tff(c_68, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_partfun1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4])).
% 9.45/3.85  tff(c_219, plain, (![C_70, A_71, B_72]: (v1_funct_1(k2_funct_1(C_70)) | k2_relset_1(A_71, B_72, C_70)!=B_72 | ~v2_funct_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | ~v1_funct_2(C_70, A_71, B_72) | ~v1_funct_1(C_70))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.45/3.85  tff(c_225, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_219])).
% 9.45/3.85  tff(c_231, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_50, c_54, c_225])).
% 9.45/3.85  tff(c_38, plain, (![C_36, B_35, A_34]: (m1_subset_1(k2_funct_1(C_36), k1_zfmisc_1(k2_zfmisc_1(B_35, A_34))) | k2_relset_1(A_34, B_35, C_36)!=B_35 | ~v2_funct_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_2(C_36, A_34, B_35) | ~v1_funct_1(C_36))), inference(cnfTransformation, [status(thm)], [f_130])).
% 9.45/3.85  tff(c_805, plain, (![C_140, D_141, B_143, A_144, F_139, E_142]: (k1_partfun1(A_144, B_143, C_140, D_141, E_142, F_139)=k5_relat_1(E_142, F_139) | ~m1_subset_1(F_139, k1_zfmisc_1(k2_zfmisc_1(C_140, D_141))) | ~v1_funct_1(F_139) | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))) | ~v1_funct_1(E_142))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.45/3.85  tff(c_811, plain, (![A_144, B_143, E_142]: (k1_partfun1(A_144, B_143, '#skF_2', '#skF_1', E_142, '#skF_4')=k5_relat_1(E_142, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))) | ~v1_funct_1(E_142))), inference(resolution, [status(thm)], [c_56, c_805])).
% 9.45/3.85  tff(c_824, plain, (![A_145, B_146, E_147]: (k1_partfun1(A_145, B_146, '#skF_2', '#skF_1', E_147, '#skF_4')=k5_relat_1(E_147, '#skF_4') | ~m1_subset_1(E_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))) | ~v1_funct_1(E_147))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_811])).
% 9.45/3.85  tff(c_6882, plain, (![B_363, A_364, C_365]: (k1_partfun1(B_363, A_364, '#skF_2', '#skF_1', k2_funct_1(C_365), '#skF_4')=k5_relat_1(k2_funct_1(C_365), '#skF_4') | ~v1_funct_1(k2_funct_1(C_365)) | k2_relset_1(A_364, B_363, C_365)!=B_363 | ~v2_funct_1(C_365) | ~m1_subset_1(C_365, k1_zfmisc_1(k2_zfmisc_1(A_364, B_363))) | ~v1_funct_2(C_365, A_364, B_363) | ~v1_funct_1(C_365))), inference(resolution, [status(thm)], [c_38, c_824])).
% 9.45/3.85  tff(c_6936, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_2', '#skF_1', k2_funct_1('#skF_3'), '#skF_4')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_6882])).
% 9.45/3.85  tff(c_6986, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_2', '#skF_1', k2_funct_1('#skF_3'), '#skF_4')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_50, c_54, c_231, c_6936])).
% 9.45/3.85  tff(c_873, plain, (![D_149, B_152, A_148, E_153, F_151, C_150]: (m1_subset_1(k1_partfun1(A_148, B_152, C_150, D_149, E_153, F_151), k1_zfmisc_1(k2_zfmisc_1(A_148, D_149))) | ~m1_subset_1(F_151, k1_zfmisc_1(k2_zfmisc_1(C_150, D_149))) | ~v1_funct_1(F_151) | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_148, B_152))) | ~v1_funct_1(E_153))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.45/3.85  tff(c_28, plain, (![B_19, A_18, C_20]: (k1_xboole_0=B_19 | k1_relset_1(A_18, B_19, C_20)=A_18 | ~v1_funct_2(C_20, A_18, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.45/3.85  tff(c_940, plain, (![D_149, B_152, A_148, E_153, F_151, C_150]: (k1_xboole_0=D_149 | k1_relset_1(A_148, D_149, k1_partfun1(A_148, B_152, C_150, D_149, E_153, F_151))=A_148 | ~v1_funct_2(k1_partfun1(A_148, B_152, C_150, D_149, E_153, F_151), A_148, D_149) | ~m1_subset_1(F_151, k1_zfmisc_1(k2_zfmisc_1(C_150, D_149))) | ~v1_funct_1(F_151) | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_148, B_152))) | ~v1_funct_1(E_153))), inference(resolution, [status(thm)], [c_873, c_28])).
% 9.45/3.85  tff(c_6997, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', k1_partfun1('#skF_2', '#skF_1', '#skF_2', '#skF_1', k2_funct_1('#skF_3'), '#skF_4'))='#skF_2' | ~v1_funct_2(k5_relat_1(k2_funct_1('#skF_3'), '#skF_4'), '#skF_2', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6986, c_940])).
% 9.45/3.85  tff(c_7016, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', k5_relat_1(k2_funct_1('#skF_3'), '#skF_4'))='#skF_2' | ~v1_funct_2(k5_relat_1(k2_funct_1('#skF_3'), '#skF_4'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_60, c_56, c_6986, c_6997])).
% 9.45/3.85  tff(c_7017, plain, (k1_relset_1('#skF_2', '#skF_1', k5_relat_1(k2_funct_1('#skF_3'), '#skF_4'))='#skF_2' | ~v1_funct_2(k5_relat_1(k2_funct_1('#skF_3'), '#skF_4'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_48, c_7016])).
% 9.45/3.85  tff(c_7029, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_7017])).
% 9.45/3.85  tff(c_7032, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_7029])).
% 9.45/3.85  tff(c_7036, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_50, c_54, c_7032])).
% 9.45/3.85  tff(c_7038, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_7017])).
% 9.45/3.85  tff(c_3513, plain, (![C_242, B_239, A_237, E_240, B_241, A_238]: (k1_partfun1(A_238, B_239, B_241, A_237, E_240, k2_funct_1(C_242))=k5_relat_1(E_240, k2_funct_1(C_242)) | ~v1_funct_1(k2_funct_1(C_242)) | ~m1_subset_1(E_240, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))) | ~v1_funct_1(E_240) | k2_relset_1(A_237, B_241, C_242)!=B_241 | ~v2_funct_1(C_242) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_237, B_241))) | ~v1_funct_2(C_242, A_237, B_241) | ~v1_funct_1(C_242))), inference(resolution, [status(thm)], [c_38, c_805])).
% 9.45/3.85  tff(c_3545, plain, (![B_241, A_237, C_242]: (k1_partfun1('#skF_1', '#skF_2', B_241, A_237, '#skF_3', k2_funct_1(C_242))=k5_relat_1('#skF_3', k2_funct_1(C_242)) | ~v1_funct_1(k2_funct_1(C_242)) | ~v1_funct_1('#skF_3') | k2_relset_1(A_237, B_241, C_242)!=B_241 | ~v2_funct_1(C_242) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_237, B_241))) | ~v1_funct_2(C_242, A_237, B_241) | ~v1_funct_1(C_242))), inference(resolution, [status(thm)], [c_62, c_3513])).
% 9.45/3.85  tff(c_7520, plain, (![B_372, A_373, C_374]: (k1_partfun1('#skF_1', '#skF_2', B_372, A_373, '#skF_3', k2_funct_1(C_374))=k5_relat_1('#skF_3', k2_funct_1(C_374)) | ~v1_funct_1(k2_funct_1(C_374)) | k2_relset_1(A_373, B_372, C_374)!=B_372 | ~v2_funct_1(C_374) | ~m1_subset_1(C_374, k1_zfmisc_1(k2_zfmisc_1(A_373, B_372))) | ~v1_funct_2(C_374, A_373, B_372) | ~v1_funct_1(C_374))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3545])).
% 9.45/3.85  tff(c_7577, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_7520])).
% 9.45/3.85  tff(c_7630, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_50, c_54, c_231, c_7577])).
% 9.45/3.85  tff(c_30, plain, (![A_21, B_22, D_24, C_23, F_26, E_25]: (m1_subset_1(k1_partfun1(A_21, B_22, C_23, D_24, E_25, F_26), k1_zfmisc_1(k2_zfmisc_1(A_21, D_24))) | ~m1_subset_1(F_26, k1_zfmisc_1(k2_zfmisc_1(C_23, D_24))) | ~v1_funct_1(F_26) | ~m1_subset_1(E_25, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_1(E_25))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.45/3.85  tff(c_8078, plain, (m1_subset_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7630, c_30])).
% 9.45/3.85  tff(c_8097, plain, (m1_subset_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_231, c_7038, c_8078])).
% 9.45/3.85  tff(c_8245, plain, (m1_subset_1(k6_partfun1(k1_relat_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_68, c_8097])).
% 9.45/3.85  tff(c_8390, plain, (m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_66, c_50, c_170, c_8245])).
% 9.45/3.85  tff(c_8392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_594, c_8390])).
% 9.45/3.85  tff(c_8393, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_560])).
% 9.45/3.85  tff(c_8686, plain, (![C_412, B_415, A_416, E_414, D_413, F_411]: (k1_partfun1(A_416, B_415, C_412, D_413, E_414, F_411)=k5_relat_1(E_414, F_411) | ~m1_subset_1(F_411, k1_zfmisc_1(k2_zfmisc_1(C_412, D_413))) | ~v1_funct_1(F_411) | ~m1_subset_1(E_414, k1_zfmisc_1(k2_zfmisc_1(A_416, B_415))) | ~v1_funct_1(E_414))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.45/3.85  tff(c_8692, plain, (![A_416, B_415, E_414]: (k1_partfun1(A_416, B_415, '#skF_2', '#skF_1', E_414, '#skF_4')=k5_relat_1(E_414, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_414, k1_zfmisc_1(k2_zfmisc_1(A_416, B_415))) | ~v1_funct_1(E_414))), inference(resolution, [status(thm)], [c_56, c_8686])).
% 9.45/3.85  tff(c_8705, plain, (![A_417, B_418, E_419]: (k1_partfun1(A_417, B_418, '#skF_2', '#skF_1', E_419, '#skF_4')=k5_relat_1(E_419, '#skF_4') | ~m1_subset_1(E_419, k1_zfmisc_1(k2_zfmisc_1(A_417, B_418))) | ~v1_funct_1(E_419))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_8692])).
% 9.45/3.85  tff(c_8717, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_8705])).
% 9.45/3.85  tff(c_8727, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_8393, c_8717])).
% 9.45/3.85  tff(c_8729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8503, c_8727])).
% 9.45/3.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.45/3.85  
% 9.45/3.85  Inference rules
% 9.45/3.85  ----------------------
% 9.45/3.85  #Ref     : 0
% 9.45/3.85  #Sup     : 1684
% 9.45/3.85  #Fact    : 0
% 9.45/3.85  #Define  : 0
% 9.45/3.85  #Split   : 30
% 9.45/3.85  #Chain   : 0
% 9.45/3.85  #Close   : 0
% 9.45/3.85  
% 9.45/3.85  Ordering : KBO
% 9.45/3.85  
% 9.45/3.85  Simplification rules
% 9.45/3.85  ----------------------
% 9.45/3.85  #Subsume      : 275
% 9.45/3.85  #Demod        : 2665
% 9.45/3.85  #Tautology    : 278
% 9.45/3.85  #SimpNegUnit  : 145
% 9.45/3.85  #BackRed      : 55
% 9.45/3.85  
% 9.45/3.85  #Partial instantiations: 0
% 9.45/3.85  #Strategies tried      : 1
% 9.45/3.86  
% 9.45/3.86  Timing (in seconds)
% 9.45/3.86  ----------------------
% 9.45/3.86  Preprocessing        : 0.44
% 9.45/3.86  Parsing              : 0.23
% 9.45/3.86  CNF conversion       : 0.03
% 9.45/3.86  Main loop            : 2.63
% 9.45/3.86  Inferencing          : 0.65
% 9.45/3.86  Reduction            : 1.26
% 9.45/3.86  Demodulation         : 1.02
% 9.45/3.86  BG Simplification    : 0.06
% 9.45/3.86  Subsumption          : 0.52
% 9.45/3.86  Abstraction          : 0.10
% 9.45/3.86  MUC search           : 0.00
% 9.45/3.86  Cooper               : 0.00
% 9.45/3.86  Total                : 3.12
% 9.45/3.86  Index Insertion      : 0.00
% 9.45/3.86  Index Deletion       : 0.00
% 9.45/3.86  Index Matching       : 0.00
% 9.45/3.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
