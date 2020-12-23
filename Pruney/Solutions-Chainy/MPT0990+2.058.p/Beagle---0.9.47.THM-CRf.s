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
% DateTime   : Thu Dec  3 10:13:04 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 165 expanded)
%              Number of leaves         :   38 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  188 ( 600 expanded)
%              Number of equality atoms :   77 ( 212 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_132,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_94,axiom,(
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

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_106,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_42,axiom,(
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

tff(f_66,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_76,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(c_36,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_100,plain,(
    ! [A_51,B_52,C_53] :
      ( k1_relset_1(A_51,B_52,C_53) = k1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_111,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_100])).

tff(c_185,plain,(
    ! [B_66,A_67,C_68] :
      ( k1_xboole_0 = B_66
      | k1_relset_1(A_67,B_66,C_68) = A_67
      | ~ v1_funct_2(C_68,A_67,B_66)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_67,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_191,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_185])).

tff(c_199,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_111,c_191])).

tff(c_200,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_199])).

tff(c_75,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_86,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_75])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_87,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_75])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_42,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_46,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_121,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_relset_1(A_54,B_55,C_56) = k2_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_130,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_121])).

tff(c_134,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_130])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_56,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_112,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_100])).

tff(c_194,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_185])).

tff(c_203,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_112,c_194])).

tff(c_204,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_203])).

tff(c_34,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k2_funct_1(A_1) = B_3
      | k6_relat_1(k1_relat_1(A_1)) != k5_relat_1(A_1,B_3)
      | k2_relat_1(A_1) != k1_relat_1(B_3)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1131,plain,(
    ! [A_138,B_139] :
      ( k2_funct_1(A_138) = B_139
      | k6_partfun1(k1_relat_1(A_138)) != k5_relat_1(A_138,B_139)
      | k2_relat_1(A_138) != k1_relat_1(B_139)
      | ~ v2_funct_1(A_138)
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139)
      | ~ v1_funct_1(A_138)
      | ~ v1_relat_1(A_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2])).

tff(c_1133,plain,(
    ! [B_139] :
      ( k2_funct_1('#skF_3') = B_139
      | k5_relat_1('#skF_3',B_139) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_139)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_1131])).

tff(c_1140,plain,(
    ! [B_140] :
      ( k2_funct_1('#skF_3') = B_140
      | k5_relat_1('#skF_3',B_140) != k6_partfun1('#skF_1')
      | k1_relat_1(B_140) != '#skF_2'
      | ~ v1_funct_1(B_140)
      | ~ v1_relat_1(B_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_58,c_42,c_134,c_1133])).

tff(c_1149,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_1140])).

tff(c_1156,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_200,c_1149])).

tff(c_1157,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1156])).

tff(c_278,plain,(
    ! [C_78,A_81,B_80,F_82,E_79,D_83] :
      ( k4_relset_1(A_81,B_80,C_78,D_83,E_79,F_82) = k5_relat_1(E_79,F_82)
      | ~ m1_subset_1(F_82,k1_zfmisc_1(k2_zfmisc_1(C_78,D_83)))
      | ~ m1_subset_1(E_79,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_288,plain,(
    ! [A_84,B_85,E_86] :
      ( k4_relset_1(A_84,B_85,'#skF_2','#skF_1',E_86,'#skF_4') = k5_relat_1(E_86,'#skF_4')
      | ~ m1_subset_1(E_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(resolution,[status(thm)],[c_48,c_278])).

tff(c_300,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_288])).

tff(c_396,plain,(
    ! [C_103,F_105,B_102,E_106,A_104,D_101] :
      ( m1_subset_1(k4_relset_1(A_104,B_102,C_103,D_101,E_106,F_105),k1_zfmisc_1(k2_zfmisc_1(A_104,D_101)))
      | ~ m1_subset_1(F_105,k1_zfmisc_1(k2_zfmisc_1(C_103,D_101)))
      | ~ m1_subset_1(E_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_453,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_396])).

tff(c_481,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_453])).

tff(c_678,plain,(
    ! [C_110,A_108,D_112,B_113,E_109,F_111] :
      ( k1_partfun1(A_108,B_113,C_110,D_112,E_109,F_111) = k5_relat_1(E_109,F_111)
      | ~ m1_subset_1(F_111,k1_zfmisc_1(k2_zfmisc_1(C_110,D_112)))
      | ~ v1_funct_1(F_111)
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_108,B_113)))
      | ~ v1_funct_1(E_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_692,plain,(
    ! [A_108,B_113,E_109] :
      ( k1_partfun1(A_108,B_113,'#skF_2','#skF_1',E_109,'#skF_4') = k5_relat_1(E_109,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_108,B_113)))
      | ~ v1_funct_1(E_109) ) ),
    inference(resolution,[status(thm)],[c_48,c_678])).

tff(c_1020,plain,(
    ! [A_125,B_126,E_127] :
      ( k1_partfun1(A_125,B_126,'#skF_2','#skF_1',E_127,'#skF_4') = k5_relat_1(E_127,'#skF_4')
      | ~ m1_subset_1(E_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ v1_funct_1(E_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_692])).

tff(c_1056,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1020])).

tff(c_1072,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1056])).

tff(c_18,plain,(
    ! [A_29] : m1_subset_1(k6_relat_1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_59,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_18])).

tff(c_44,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_253,plain,(
    ! [D_74,C_75,A_76,B_77] :
      ( D_74 = C_75
      | ~ r2_relset_1(A_76,B_77,C_75,D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_259,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_44,c_253])).

tff(c_272,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_259])).

tff(c_277,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_272])).

tff(c_1077,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1072,c_277])).

tff(c_1081,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_1077])).

tff(c_1082,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_272])).

tff(c_1435,plain,(
    ! [A_152,C_154,D_156,F_155,E_153,B_157] :
      ( k1_partfun1(A_152,B_157,C_154,D_156,E_153,F_155) = k5_relat_1(E_153,F_155)
      | ~ m1_subset_1(F_155,k1_zfmisc_1(k2_zfmisc_1(C_154,D_156)))
      | ~ v1_funct_1(F_155)
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_152,B_157)))
      | ~ v1_funct_1(E_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1449,plain,(
    ! [A_152,B_157,E_153] :
      ( k1_partfun1(A_152,B_157,'#skF_2','#skF_1',E_153,'#skF_4') = k5_relat_1(E_153,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_152,B_157)))
      | ~ v1_funct_1(E_153) ) ),
    inference(resolution,[status(thm)],[c_48,c_1435])).

tff(c_1673,plain,(
    ! [A_165,B_166,E_167] :
      ( k1_partfun1(A_165,B_166,'#skF_2','#skF_1',E_167,'#skF_4') = k5_relat_1(E_167,'#skF_4')
      | ~ m1_subset_1(E_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166)))
      | ~ v1_funct_1(E_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1449])).

tff(c_1703,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1673])).

tff(c_1717,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1082,c_1703])).

tff(c_1719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1157,c_1717])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.98/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.67  
% 3.98/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.67  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.98/1.67  
% 3.98/1.67  %Foreground sorts:
% 3.98/1.67  
% 3.98/1.67  
% 3.98/1.67  %Background operators:
% 3.98/1.67  
% 3.98/1.67  
% 3.98/1.67  %Foreground operators:
% 3.98/1.67  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.98/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.98/1.67  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.98/1.67  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.98/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.98/1.67  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.98/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.98/1.67  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.98/1.67  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.98/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.98/1.67  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.98/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.98/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.98/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.98/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.98/1.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.98/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.98/1.67  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.98/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.98/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.98/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.98/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.98/1.67  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.98/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.98/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.98/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.98/1.67  
% 4.15/1.69  tff(f_132, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.15/1.69  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.15/1.69  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.15/1.69  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.15/1.69  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.15/1.69  tff(f_106, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.15/1.69  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 4.15/1.69  tff(f_66, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 4.15/1.69  tff(f_52, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 4.15/1.69  tff(f_104, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.15/1.69  tff(f_76, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 4.15/1.69  tff(f_74, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.15/1.69  tff(c_36, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.15/1.69  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.15/1.69  tff(c_40, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.15/1.69  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.15/1.69  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.15/1.69  tff(c_100, plain, (![A_51, B_52, C_53]: (k1_relset_1(A_51, B_52, C_53)=k1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.15/1.69  tff(c_111, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_100])).
% 4.15/1.69  tff(c_185, plain, (![B_66, A_67, C_68]: (k1_xboole_0=B_66 | k1_relset_1(A_67, B_66, C_68)=A_67 | ~v1_funct_2(C_68, A_67, B_66) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_67, B_66))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.15/1.69  tff(c_191, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_185])).
% 4.15/1.69  tff(c_199, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_111, c_191])).
% 4.15/1.69  tff(c_200, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_40, c_199])).
% 4.15/1.69  tff(c_75, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.15/1.69  tff(c_86, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_75])).
% 4.15/1.69  tff(c_54, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.15/1.69  tff(c_87, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_75])).
% 4.15/1.69  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.15/1.69  tff(c_42, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.15/1.69  tff(c_46, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.15/1.69  tff(c_121, plain, (![A_54, B_55, C_56]: (k2_relset_1(A_54, B_55, C_56)=k2_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.15/1.69  tff(c_130, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_121])).
% 4.15/1.69  tff(c_134, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_130])).
% 4.15/1.69  tff(c_38, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.15/1.69  tff(c_56, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.15/1.69  tff(c_112, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_100])).
% 4.15/1.69  tff(c_194, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_185])).
% 4.15/1.69  tff(c_203, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_112, c_194])).
% 4.15/1.69  tff(c_204, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_38, c_203])).
% 4.15/1.69  tff(c_34, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.15/1.69  tff(c_2, plain, (![A_1, B_3]: (k2_funct_1(A_1)=B_3 | k6_relat_1(k1_relat_1(A_1))!=k5_relat_1(A_1, B_3) | k2_relat_1(A_1)!=k1_relat_1(B_3) | ~v2_funct_1(A_1) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.15/1.69  tff(c_1131, plain, (![A_138, B_139]: (k2_funct_1(A_138)=B_139 | k6_partfun1(k1_relat_1(A_138))!=k5_relat_1(A_138, B_139) | k2_relat_1(A_138)!=k1_relat_1(B_139) | ~v2_funct_1(A_138) | ~v1_funct_1(B_139) | ~v1_relat_1(B_139) | ~v1_funct_1(A_138) | ~v1_relat_1(A_138))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2])).
% 4.15/1.69  tff(c_1133, plain, (![B_139]: (k2_funct_1('#skF_3')=B_139 | k5_relat_1('#skF_3', B_139)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_139) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_139) | ~v1_relat_1(B_139) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_204, c_1131])).
% 4.15/1.69  tff(c_1140, plain, (![B_140]: (k2_funct_1('#skF_3')=B_140 | k5_relat_1('#skF_3', B_140)!=k6_partfun1('#skF_1') | k1_relat_1(B_140)!='#skF_2' | ~v1_funct_1(B_140) | ~v1_relat_1(B_140))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_58, c_42, c_134, c_1133])).
% 4.15/1.69  tff(c_1149, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_1140])).
% 4.15/1.69  tff(c_1156, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_200, c_1149])).
% 4.15/1.69  tff(c_1157, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_1156])).
% 4.15/1.69  tff(c_278, plain, (![C_78, A_81, B_80, F_82, E_79, D_83]: (k4_relset_1(A_81, B_80, C_78, D_83, E_79, F_82)=k5_relat_1(E_79, F_82) | ~m1_subset_1(F_82, k1_zfmisc_1(k2_zfmisc_1(C_78, D_83))) | ~m1_subset_1(E_79, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.15/1.69  tff(c_288, plain, (![A_84, B_85, E_86]: (k4_relset_1(A_84, B_85, '#skF_2', '#skF_1', E_86, '#skF_4')=k5_relat_1(E_86, '#skF_4') | ~m1_subset_1(E_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(resolution, [status(thm)], [c_48, c_278])).
% 4.15/1.69  tff(c_300, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_288])).
% 4.15/1.69  tff(c_396, plain, (![C_103, F_105, B_102, E_106, A_104, D_101]: (m1_subset_1(k4_relset_1(A_104, B_102, C_103, D_101, E_106, F_105), k1_zfmisc_1(k2_zfmisc_1(A_104, D_101))) | ~m1_subset_1(F_105, k1_zfmisc_1(k2_zfmisc_1(C_103, D_101))) | ~m1_subset_1(E_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_102))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.15/1.69  tff(c_453, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_300, c_396])).
% 4.15/1.69  tff(c_481, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_453])).
% 4.15/1.69  tff(c_678, plain, (![C_110, A_108, D_112, B_113, E_109, F_111]: (k1_partfun1(A_108, B_113, C_110, D_112, E_109, F_111)=k5_relat_1(E_109, F_111) | ~m1_subset_1(F_111, k1_zfmisc_1(k2_zfmisc_1(C_110, D_112))) | ~v1_funct_1(F_111) | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_108, B_113))) | ~v1_funct_1(E_109))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.15/1.69  tff(c_692, plain, (![A_108, B_113, E_109]: (k1_partfun1(A_108, B_113, '#skF_2', '#skF_1', E_109, '#skF_4')=k5_relat_1(E_109, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_108, B_113))) | ~v1_funct_1(E_109))), inference(resolution, [status(thm)], [c_48, c_678])).
% 4.15/1.69  tff(c_1020, plain, (![A_125, B_126, E_127]: (k1_partfun1(A_125, B_126, '#skF_2', '#skF_1', E_127, '#skF_4')=k5_relat_1(E_127, '#skF_4') | ~m1_subset_1(E_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~v1_funct_1(E_127))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_692])).
% 4.15/1.69  tff(c_1056, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_1020])).
% 4.15/1.69  tff(c_1072, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1056])).
% 4.15/1.69  tff(c_18, plain, (![A_29]: (m1_subset_1(k6_relat_1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.15/1.69  tff(c_59, plain, (![A_29]: (m1_subset_1(k6_partfun1(A_29), k1_zfmisc_1(k2_zfmisc_1(A_29, A_29))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_18])).
% 4.15/1.69  tff(c_44, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.15/1.69  tff(c_253, plain, (![D_74, C_75, A_76, B_77]: (D_74=C_75 | ~r2_relset_1(A_76, B_77, C_75, D_74) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.15/1.69  tff(c_259, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_44, c_253])).
% 4.15/1.69  tff(c_272, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_259])).
% 4.15/1.69  tff(c_277, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_272])).
% 4.15/1.69  tff(c_1077, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1072, c_277])).
% 4.15/1.69  tff(c_1081, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_481, c_1077])).
% 4.15/1.69  tff(c_1082, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_272])).
% 4.15/1.69  tff(c_1435, plain, (![A_152, C_154, D_156, F_155, E_153, B_157]: (k1_partfun1(A_152, B_157, C_154, D_156, E_153, F_155)=k5_relat_1(E_153, F_155) | ~m1_subset_1(F_155, k1_zfmisc_1(k2_zfmisc_1(C_154, D_156))) | ~v1_funct_1(F_155) | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_152, B_157))) | ~v1_funct_1(E_153))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.15/1.69  tff(c_1449, plain, (![A_152, B_157, E_153]: (k1_partfun1(A_152, B_157, '#skF_2', '#skF_1', E_153, '#skF_4')=k5_relat_1(E_153, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_152, B_157))) | ~v1_funct_1(E_153))), inference(resolution, [status(thm)], [c_48, c_1435])).
% 4.15/1.69  tff(c_1673, plain, (![A_165, B_166, E_167]: (k1_partfun1(A_165, B_166, '#skF_2', '#skF_1', E_167, '#skF_4')=k5_relat_1(E_167, '#skF_4') | ~m1_subset_1(E_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))) | ~v1_funct_1(E_167))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1449])).
% 4.15/1.69  tff(c_1703, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_1673])).
% 4.15/1.69  tff(c_1717, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1082, c_1703])).
% 4.15/1.69  tff(c_1719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1157, c_1717])).
% 4.15/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.15/1.69  
% 4.15/1.69  Inference rules
% 4.15/1.69  ----------------------
% 4.15/1.69  #Ref     : 0
% 4.15/1.69  #Sup     : 399
% 4.15/1.69  #Fact    : 0
% 4.15/1.69  #Define  : 0
% 4.15/1.69  #Split   : 9
% 4.15/1.69  #Chain   : 0
% 4.15/1.69  #Close   : 0
% 4.15/1.69  
% 4.15/1.69  Ordering : KBO
% 4.15/1.69  
% 4.15/1.69  Simplification rules
% 4.15/1.69  ----------------------
% 4.15/1.69  #Subsume      : 1
% 4.15/1.69  #Demod        : 97
% 4.15/1.69  #Tautology    : 87
% 4.15/1.69  #SimpNegUnit  : 34
% 4.15/1.69  #BackRed      : 5
% 4.15/1.69  
% 4.15/1.69  #Partial instantiations: 0
% 4.15/1.69  #Strategies tried      : 1
% 4.15/1.69  
% 4.15/1.69  Timing (in seconds)
% 4.15/1.69  ----------------------
% 4.15/1.69  Preprocessing        : 0.35
% 4.15/1.69  Parsing              : 0.18
% 4.15/1.70  CNF conversion       : 0.02
% 4.15/1.70  Main loop            : 0.58
% 4.15/1.70  Inferencing          : 0.21
% 4.15/1.70  Reduction            : 0.19
% 4.15/1.70  Demodulation         : 0.13
% 4.15/1.70  BG Simplification    : 0.03
% 4.15/1.70  Subsumption          : 0.09
% 4.15/1.70  Abstraction          : 0.04
% 4.15/1.70  MUC search           : 0.00
% 4.15/1.70  Cooper               : 0.00
% 4.15/1.70  Total                : 0.97
% 4.15/1.70  Index Insertion      : 0.00
% 4.15/1.70  Index Deletion       : 0.00
% 4.15/1.70  Index Matching       : 0.00
% 4.15/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
