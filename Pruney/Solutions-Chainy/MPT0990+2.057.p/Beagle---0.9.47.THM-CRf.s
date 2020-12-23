%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:04 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 160 expanded)
%              Number of leaves         :   39 (  74 expanded)
%              Depth                    :   10
%              Number of atoms          :  188 ( 596 expanded)
%              Number of equality atoms :   77 ( 208 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_134,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_108,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(c_38,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_52,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_103,plain,(
    ! [A_53,B_54,C_55] :
      ( k1_relset_1(A_53,B_54,C_55) = k1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_114,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_103])).

tff(c_205,plain,(
    ! [B_70,A_71,C_72] :
      ( k1_xboole_0 = B_70
      | k1_relset_1(A_71,B_70,C_72) = A_71
      | ~ v1_funct_2(C_72,A_71,B_70)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_211,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_205])).

tff(c_219,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_114,c_211])).

tff(c_220,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_219])).

tff(c_77,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_88,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_77])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_89,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_77])).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_44,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_48,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_116,plain,(
    ! [A_56,B_57,C_58] :
      ( k2_relset_1(A_56,B_57,C_58) = k2_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_125,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_116])).

tff(c_129,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_125])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_58,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_115,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_103])).

tff(c_214,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_205])).

tff(c_223,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_115,c_214])).

tff(c_224,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_223])).

tff(c_36,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

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

tff(c_1134,plain,(
    ! [A_139,B_140] :
      ( k2_funct_1(A_139) = B_140
      | k6_partfun1(k1_relat_1(A_139)) != k5_relat_1(A_139,B_140)
      | k2_relat_1(A_139) != k1_relat_1(B_140)
      | ~ v2_funct_1(A_139)
      | ~ v1_funct_1(B_140)
      | ~ v1_relat_1(B_140)
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2])).

tff(c_1136,plain,(
    ! [B_140] :
      ( k2_funct_1('#skF_3') = B_140
      | k5_relat_1('#skF_3',B_140) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_140)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_140)
      | ~ v1_relat_1(B_140)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_1134])).

tff(c_1143,plain,(
    ! [B_141] :
      ( k2_funct_1('#skF_3') = B_141
      | k5_relat_1('#skF_3',B_141) != k6_partfun1('#skF_1')
      | k1_relat_1(B_141) != '#skF_2'
      | ~ v1_funct_1(B_141)
      | ~ v1_relat_1(B_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_60,c_44,c_129,c_1136])).

tff(c_1152,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_1143])).

tff(c_1159,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_220,c_1152])).

tff(c_1160,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1159])).

tff(c_278,plain,(
    ! [A_82,E_80,C_79,B_81,D_84,F_83] :
      ( k4_relset_1(A_82,B_81,C_79,D_84,E_80,F_83) = k5_relat_1(E_80,F_83)
      | ~ m1_subset_1(F_83,k1_zfmisc_1(k2_zfmisc_1(C_79,D_84)))
      | ~ m1_subset_1(E_80,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_288,plain,(
    ! [A_85,B_86,E_87] :
      ( k4_relset_1(A_85,B_86,'#skF_2','#skF_1',E_87,'#skF_4') = k5_relat_1(E_87,'#skF_4')
      | ~ m1_subset_1(E_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(resolution,[status(thm)],[c_50,c_278])).

tff(c_300,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_288])).

tff(c_387,plain,(
    ! [C_103,F_105,B_102,E_106,A_104,D_101] :
      ( m1_subset_1(k4_relset_1(A_104,B_102,C_103,D_101,E_106,F_105),k1_zfmisc_1(k2_zfmisc_1(A_104,D_101)))
      | ~ m1_subset_1(F_105,k1_zfmisc_1(k2_zfmisc_1(C_103,D_101)))
      | ~ m1_subset_1(E_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_441,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_387])).

tff(c_467,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_441])).

tff(c_664,plain,(
    ! [C_110,A_108,D_112,B_113,E_109,F_111] :
      ( k1_partfun1(A_108,B_113,C_110,D_112,E_109,F_111) = k5_relat_1(E_109,F_111)
      | ~ m1_subset_1(F_111,k1_zfmisc_1(k2_zfmisc_1(C_110,D_112)))
      | ~ v1_funct_1(F_111)
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_108,B_113)))
      | ~ v1_funct_1(E_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_678,plain,(
    ! [A_108,B_113,E_109] :
      ( k1_partfun1(A_108,B_113,'#skF_2','#skF_1',E_109,'#skF_4') = k5_relat_1(E_109,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_108,B_113)))
      | ~ v1_funct_1(E_109) ) ),
    inference(resolution,[status(thm)],[c_50,c_664])).

tff(c_1023,plain,(
    ! [A_126,B_127,E_128] :
      ( k1_partfun1(A_126,B_127,'#skF_2','#skF_1',E_128,'#skF_4') = k5_relat_1(E_128,'#skF_4')
      | ~ m1_subset_1(E_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127)))
      | ~ v1_funct_1(E_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_678])).

tff(c_1059,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1023])).

tff(c_1075,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1059])).

tff(c_32,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_46,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_248,plain,(
    ! [D_74,C_75,A_76,B_77] :
      ( D_74 = C_75
      | ~ r2_relset_1(A_76,B_77,C_75,D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_256,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_46,c_248])).

tff(c_271,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_256])).

tff(c_277,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_1080,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1075,c_277])).

tff(c_1084,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_1080])).

tff(c_1085,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_1438,plain,(
    ! [D_157,C_155,F_156,A_153,B_158,E_154] :
      ( k1_partfun1(A_153,B_158,C_155,D_157,E_154,F_156) = k5_relat_1(E_154,F_156)
      | ~ m1_subset_1(F_156,k1_zfmisc_1(k2_zfmisc_1(C_155,D_157)))
      | ~ v1_funct_1(F_156)
      | ~ m1_subset_1(E_154,k1_zfmisc_1(k2_zfmisc_1(A_153,B_158)))
      | ~ v1_funct_1(E_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1452,plain,(
    ! [A_153,B_158,E_154] :
      ( k1_partfun1(A_153,B_158,'#skF_2','#skF_1',E_154,'#skF_4') = k5_relat_1(E_154,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_154,k1_zfmisc_1(k2_zfmisc_1(A_153,B_158)))
      | ~ v1_funct_1(E_154) ) ),
    inference(resolution,[status(thm)],[c_50,c_1438])).

tff(c_1676,plain,(
    ! [A_166,B_167,E_168] :
      ( k1_partfun1(A_166,B_167,'#skF_2','#skF_1',E_168,'#skF_4') = k5_relat_1(E_168,'#skF_4')
      | ~ m1_subset_1(E_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ v1_funct_1(E_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1452])).

tff(c_1706,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1676])).

tff(c_1720,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1085,c_1706])).

tff(c_1722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1160,c_1720])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n016.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:37:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.59  
% 3.62/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.59  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.62/1.59  
% 3.62/1.59  %Foreground sorts:
% 3.62/1.59  
% 3.62/1.59  
% 3.62/1.59  %Background operators:
% 3.62/1.59  
% 3.62/1.59  
% 3.62/1.59  %Foreground operators:
% 3.62/1.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.62/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.62/1.59  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.62/1.59  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.62/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.59  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.62/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.62/1.59  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.62/1.59  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.62/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.62/1.59  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.62/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.62/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.62/1.59  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.62/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.62/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.62/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.62/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.62/1.59  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.62/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.62/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.62/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.62/1.59  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.62/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.62/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.62/1.59  
% 3.95/1.61  tff(f_134, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 3.95/1.61  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.95/1.61  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.95/1.61  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.95/1.61  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.95/1.61  tff(f_108, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.95/1.61  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 3.95/1.61  tff(f_66, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.95/1.61  tff(f_52, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 3.95/1.61  tff(f_106, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.95/1.61  tff(f_96, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.95/1.61  tff(f_74, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.95/1.61  tff(c_38, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.95/1.61  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.95/1.61  tff(c_42, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.95/1.61  tff(c_52, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.95/1.61  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.95/1.61  tff(c_103, plain, (![A_53, B_54, C_55]: (k1_relset_1(A_53, B_54, C_55)=k1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.95/1.61  tff(c_114, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_103])).
% 3.95/1.61  tff(c_205, plain, (![B_70, A_71, C_72]: (k1_xboole_0=B_70 | k1_relset_1(A_71, B_70, C_72)=A_71 | ~v1_funct_2(C_72, A_71, B_70) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.95/1.61  tff(c_211, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_205])).
% 3.95/1.61  tff(c_219, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_114, c_211])).
% 3.95/1.61  tff(c_220, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_42, c_219])).
% 3.95/1.61  tff(c_77, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.95/1.61  tff(c_88, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_77])).
% 3.95/1.61  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.95/1.61  tff(c_89, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_77])).
% 3.95/1.61  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.95/1.61  tff(c_44, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.95/1.61  tff(c_48, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.95/1.61  tff(c_116, plain, (![A_56, B_57, C_58]: (k2_relset_1(A_56, B_57, C_58)=k2_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.95/1.61  tff(c_125, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_116])).
% 3.95/1.61  tff(c_129, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_125])).
% 3.95/1.61  tff(c_40, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.95/1.61  tff(c_58, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.95/1.61  tff(c_115, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_103])).
% 3.95/1.61  tff(c_214, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_205])).
% 3.95/1.61  tff(c_223, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_115, c_214])).
% 3.95/1.61  tff(c_224, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_40, c_223])).
% 3.95/1.61  tff(c_36, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.95/1.61  tff(c_2, plain, (![A_1, B_3]: (k2_funct_1(A_1)=B_3 | k6_relat_1(k1_relat_1(A_1))!=k5_relat_1(A_1, B_3) | k2_relat_1(A_1)!=k1_relat_1(B_3) | ~v2_funct_1(A_1) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.95/1.61  tff(c_1134, plain, (![A_139, B_140]: (k2_funct_1(A_139)=B_140 | k6_partfun1(k1_relat_1(A_139))!=k5_relat_1(A_139, B_140) | k2_relat_1(A_139)!=k1_relat_1(B_140) | ~v2_funct_1(A_139) | ~v1_funct_1(B_140) | ~v1_relat_1(B_140) | ~v1_funct_1(A_139) | ~v1_relat_1(A_139))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2])).
% 3.95/1.61  tff(c_1136, plain, (![B_140]: (k2_funct_1('#skF_3')=B_140 | k5_relat_1('#skF_3', B_140)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_140) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_140) | ~v1_relat_1(B_140) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_224, c_1134])).
% 3.95/1.61  tff(c_1143, plain, (![B_141]: (k2_funct_1('#skF_3')=B_141 | k5_relat_1('#skF_3', B_141)!=k6_partfun1('#skF_1') | k1_relat_1(B_141)!='#skF_2' | ~v1_funct_1(B_141) | ~v1_relat_1(B_141))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_60, c_44, c_129, c_1136])).
% 3.95/1.61  tff(c_1152, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_88, c_1143])).
% 3.95/1.61  tff(c_1159, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_220, c_1152])).
% 3.95/1.61  tff(c_1160, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_38, c_1159])).
% 3.95/1.61  tff(c_278, plain, (![A_82, E_80, C_79, B_81, D_84, F_83]: (k4_relset_1(A_82, B_81, C_79, D_84, E_80, F_83)=k5_relat_1(E_80, F_83) | ~m1_subset_1(F_83, k1_zfmisc_1(k2_zfmisc_1(C_79, D_84))) | ~m1_subset_1(E_80, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.95/1.61  tff(c_288, plain, (![A_85, B_86, E_87]: (k4_relset_1(A_85, B_86, '#skF_2', '#skF_1', E_87, '#skF_4')=k5_relat_1(E_87, '#skF_4') | ~m1_subset_1(E_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(resolution, [status(thm)], [c_50, c_278])).
% 3.95/1.61  tff(c_300, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_288])).
% 3.95/1.61  tff(c_387, plain, (![C_103, F_105, B_102, E_106, A_104, D_101]: (m1_subset_1(k4_relset_1(A_104, B_102, C_103, D_101, E_106, F_105), k1_zfmisc_1(k2_zfmisc_1(A_104, D_101))) | ~m1_subset_1(F_105, k1_zfmisc_1(k2_zfmisc_1(C_103, D_101))) | ~m1_subset_1(E_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_102))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.95/1.61  tff(c_441, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_300, c_387])).
% 3.95/1.61  tff(c_467, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_441])).
% 3.95/1.61  tff(c_664, plain, (![C_110, A_108, D_112, B_113, E_109, F_111]: (k1_partfun1(A_108, B_113, C_110, D_112, E_109, F_111)=k5_relat_1(E_109, F_111) | ~m1_subset_1(F_111, k1_zfmisc_1(k2_zfmisc_1(C_110, D_112))) | ~v1_funct_1(F_111) | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_108, B_113))) | ~v1_funct_1(E_109))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.95/1.61  tff(c_678, plain, (![A_108, B_113, E_109]: (k1_partfun1(A_108, B_113, '#skF_2', '#skF_1', E_109, '#skF_4')=k5_relat_1(E_109, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_108, B_113))) | ~v1_funct_1(E_109))), inference(resolution, [status(thm)], [c_50, c_664])).
% 3.95/1.61  tff(c_1023, plain, (![A_126, B_127, E_128]: (k1_partfun1(A_126, B_127, '#skF_2', '#skF_1', E_128, '#skF_4')=k5_relat_1(E_128, '#skF_4') | ~m1_subset_1(E_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))) | ~v1_funct_1(E_128))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_678])).
% 3.95/1.61  tff(c_1059, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_1023])).
% 3.95/1.61  tff(c_1075, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1059])).
% 3.95/1.61  tff(c_32, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.95/1.61  tff(c_46, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.95/1.61  tff(c_248, plain, (![D_74, C_75, A_76, B_77]: (D_74=C_75 | ~r2_relset_1(A_76, B_77, C_75, D_74) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.95/1.61  tff(c_256, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_46, c_248])).
% 3.95/1.61  tff(c_271, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_256])).
% 3.95/1.61  tff(c_277, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_271])).
% 3.95/1.61  tff(c_1080, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1075, c_277])).
% 3.95/1.61  tff(c_1084, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_467, c_1080])).
% 3.95/1.61  tff(c_1085, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_271])).
% 3.95/1.61  tff(c_1438, plain, (![D_157, C_155, F_156, A_153, B_158, E_154]: (k1_partfun1(A_153, B_158, C_155, D_157, E_154, F_156)=k5_relat_1(E_154, F_156) | ~m1_subset_1(F_156, k1_zfmisc_1(k2_zfmisc_1(C_155, D_157))) | ~v1_funct_1(F_156) | ~m1_subset_1(E_154, k1_zfmisc_1(k2_zfmisc_1(A_153, B_158))) | ~v1_funct_1(E_154))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.95/1.61  tff(c_1452, plain, (![A_153, B_158, E_154]: (k1_partfun1(A_153, B_158, '#skF_2', '#skF_1', E_154, '#skF_4')=k5_relat_1(E_154, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_154, k1_zfmisc_1(k2_zfmisc_1(A_153, B_158))) | ~v1_funct_1(E_154))), inference(resolution, [status(thm)], [c_50, c_1438])).
% 3.95/1.61  tff(c_1676, plain, (![A_166, B_167, E_168]: (k1_partfun1(A_166, B_167, '#skF_2', '#skF_1', E_168, '#skF_4')=k5_relat_1(E_168, '#skF_4') | ~m1_subset_1(E_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~v1_funct_1(E_168))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1452])).
% 3.95/1.61  tff(c_1706, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_1676])).
% 3.95/1.61  tff(c_1720, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1085, c_1706])).
% 3.95/1.61  tff(c_1722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1160, c_1720])).
% 3.95/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.61  
% 3.95/1.61  Inference rules
% 3.95/1.61  ----------------------
% 3.95/1.61  #Ref     : 0
% 3.95/1.61  #Sup     : 401
% 3.95/1.61  #Fact    : 0
% 3.95/1.61  #Define  : 0
% 3.95/1.61  #Split   : 8
% 3.95/1.61  #Chain   : 0
% 3.95/1.61  #Close   : 0
% 3.95/1.61  
% 3.95/1.61  Ordering : KBO
% 3.95/1.61  
% 3.95/1.61  Simplification rules
% 3.95/1.61  ----------------------
% 3.95/1.61  #Subsume      : 1
% 3.95/1.61  #Demod        : 96
% 3.95/1.61  #Tautology    : 89
% 3.95/1.61  #SimpNegUnit  : 34
% 3.95/1.61  #BackRed      : 5
% 3.95/1.61  
% 3.95/1.61  #Partial instantiations: 0
% 3.95/1.61  #Strategies tried      : 1
% 3.95/1.61  
% 3.95/1.61  Timing (in seconds)
% 3.95/1.61  ----------------------
% 3.95/1.62  Preprocessing        : 0.32
% 3.95/1.62  Parsing              : 0.17
% 3.95/1.62  CNF conversion       : 0.02
% 3.95/1.62  Main loop            : 0.56
% 3.95/1.62  Inferencing          : 0.19
% 3.95/1.62  Reduction            : 0.19
% 3.95/1.62  Demodulation         : 0.13
% 3.95/1.62  BG Simplification    : 0.03
% 3.95/1.62  Subsumption          : 0.09
% 3.95/1.62  Abstraction          : 0.03
% 3.95/1.62  MUC search           : 0.00
% 3.95/1.62  Cooper               : 0.00
% 3.95/1.62  Total                : 0.92
% 3.95/1.62  Index Insertion      : 0.00
% 3.95/1.62  Index Deletion       : 0.00
% 3.95/1.62  Index Matching       : 0.00
% 3.95/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
