%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:21 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 166 expanded)
%              Number of leaves         :   40 (  76 expanded)
%              Depth                    :   10
%              Number of atoms          :  196 ( 608 expanded)
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

tff(f_139,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_97,axiom,(
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

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_113,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_51,axiom,(
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

tff(f_71,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_111,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(c_40,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_54,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_143,plain,(
    ! [A_60,B_61,C_62] :
      ( k1_relset_1(A_60,B_61,C_62) = k1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_154,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_143])).

tff(c_219,plain,(
    ! [B_74,A_75,C_76] :
      ( k1_xboole_0 = B_74
      | k1_relset_1(A_75,B_74,C_76) = A_75
      | ~ v1_funct_2(C_76,A_75,B_74)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_225,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_219])).

tff(c_233,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_154,c_225])).

tff(c_234,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_233])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_80,plain,(
    ! [B_48,A_49] :
      ( v1_relat_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_80])).

tff(c_95,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_86])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_89,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_80])).

tff(c_98,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_89])).

tff(c_62,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_46,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_50,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_111,plain,(
    ! [A_55,B_56,C_57] :
      ( k2_relset_1(A_55,B_56,C_57) = k2_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_120,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_111])).

tff(c_124,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_120])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_60,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_155,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_143])).

tff(c_228,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_219])).

tff(c_237,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_155,c_228])).

tff(c_238,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_237])).

tff(c_38,plain,(
    ! [A_41] : k6_relat_1(A_41) = k6_partfun1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_6,plain,(
    ! [A_6,B_8] :
      ( k2_funct_1(A_6) = B_8
      | k6_relat_1(k1_relat_1(A_6)) != k5_relat_1(A_6,B_8)
      | k2_relat_1(A_6) != k1_relat_1(B_8)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_987,plain,(
    ! [A_132,B_133] :
      ( k2_funct_1(A_132) = B_133
      | k6_partfun1(k1_relat_1(A_132)) != k5_relat_1(A_132,B_133)
      | k2_relat_1(A_132) != k1_relat_1(B_133)
      | ~ v2_funct_1(A_132)
      | ~ v1_funct_1(B_133)
      | ~ v1_relat_1(B_133)
      | ~ v1_funct_1(A_132)
      | ~ v1_relat_1(A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6])).

tff(c_989,plain,(
    ! [B_133] :
      ( k2_funct_1('#skF_3') = B_133
      | k5_relat_1('#skF_3',B_133) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_133)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_133)
      | ~ v1_relat_1(B_133)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_987])).

tff(c_996,plain,(
    ! [B_134] :
      ( k2_funct_1('#skF_3') = B_134
      | k5_relat_1('#skF_3',B_134) != k6_partfun1('#skF_1')
      | k1_relat_1(B_134) != '#skF_2'
      | ~ v1_funct_1(B_134)
      | ~ v1_relat_1(B_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_62,c_46,c_124,c_989])).

tff(c_1005,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_95,c_996])).

tff(c_1015,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_234,c_1005])).

tff(c_1016,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1015])).

tff(c_287,plain,(
    ! [A_82,F_85,C_84,E_87,D_83,B_86] :
      ( k4_relset_1(A_82,B_86,C_84,D_83,E_87,F_85) = k5_relat_1(E_87,F_85)
      | ~ m1_subset_1(F_85,k1_zfmisc_1(k2_zfmisc_1(C_84,D_83)))
      | ~ m1_subset_1(E_87,k1_zfmisc_1(k2_zfmisc_1(A_82,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_297,plain,(
    ! [A_88,B_89,E_90] :
      ( k4_relset_1(A_88,B_89,'#skF_2','#skF_1',E_90,'#skF_4') = k5_relat_1(E_90,'#skF_4')
      | ~ m1_subset_1(E_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(resolution,[status(thm)],[c_52,c_287])).

tff(c_309,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_297])).

tff(c_390,plain,(
    ! [E_104,C_102,D_103,A_105,B_101,F_100] :
      ( m1_subset_1(k4_relset_1(A_105,B_101,C_102,D_103,E_104,F_100),k1_zfmisc_1(k2_zfmisc_1(A_105,D_103)))
      | ~ m1_subset_1(F_100,k1_zfmisc_1(k2_zfmisc_1(C_102,D_103)))
      | ~ m1_subset_1(E_104,k1_zfmisc_1(k2_zfmisc_1(A_105,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_442,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_390])).

tff(c_469,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_442])).

tff(c_645,plain,(
    ! [B_111,C_108,A_106,F_107,E_109,D_110] :
      ( k1_partfun1(A_106,B_111,C_108,D_110,E_109,F_107) = k5_relat_1(E_109,F_107)
      | ~ m1_subset_1(F_107,k1_zfmisc_1(k2_zfmisc_1(C_108,D_110)))
      | ~ v1_funct_1(F_107)
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_106,B_111)))
      | ~ v1_funct_1(E_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_659,plain,(
    ! [A_106,B_111,E_109] :
      ( k1_partfun1(A_106,B_111,'#skF_2','#skF_1',E_109,'#skF_4') = k5_relat_1(E_109,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_106,B_111)))
      | ~ v1_funct_1(E_109) ) ),
    inference(resolution,[status(thm)],[c_52,c_645])).

tff(c_884,plain,(
    ! [A_119,B_120,E_121] :
      ( k1_partfun1(A_119,B_120,'#skF_2','#skF_1',E_121,'#skF_4') = k5_relat_1(E_121,'#skF_4')
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ v1_funct_1(E_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_659])).

tff(c_914,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_884])).

tff(c_928,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_914])).

tff(c_34,plain,(
    ! [A_34] : m1_subset_1(k6_partfun1(A_34),k1_zfmisc_1(k2_zfmisc_1(A_34,A_34))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_48,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_253,plain,(
    ! [D_77,C_78,A_79,B_80] :
      ( D_77 = C_78
      | ~ r2_relset_1(A_79,B_80,C_78,D_77)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_261,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_48,c_253])).

tff(c_276,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_261])).

tff(c_286,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_933,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_286])).

tff(c_937,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_933])).

tff(c_938,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_1305,plain,(
    ! [C_148,E_149,D_150,A_146,B_151,F_147] :
      ( k1_partfun1(A_146,B_151,C_148,D_150,E_149,F_147) = k5_relat_1(E_149,F_147)
      | ~ m1_subset_1(F_147,k1_zfmisc_1(k2_zfmisc_1(C_148,D_150)))
      | ~ v1_funct_1(F_147)
      | ~ m1_subset_1(E_149,k1_zfmisc_1(k2_zfmisc_1(A_146,B_151)))
      | ~ v1_funct_1(E_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1319,plain,(
    ! [A_146,B_151,E_149] :
      ( k1_partfun1(A_146,B_151,'#skF_2','#skF_1',E_149,'#skF_4') = k5_relat_1(E_149,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_149,k1_zfmisc_1(k2_zfmisc_1(A_146,B_151)))
      | ~ v1_funct_1(E_149) ) ),
    inference(resolution,[status(thm)],[c_52,c_1305])).

tff(c_1544,plain,(
    ! [A_159,B_160,E_161] :
      ( k1_partfun1(A_159,B_160,'#skF_2','#skF_1',E_161,'#skF_4') = k5_relat_1(E_161,'#skF_4')
      | ~ m1_subset_1(E_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160)))
      | ~ v1_funct_1(E_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1319])).

tff(c_1574,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1544])).

tff(c_1588,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_938,c_1574])).

tff(c_1590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1016,c_1588])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.75  
% 3.81/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.75  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.81/1.75  
% 3.81/1.75  %Foreground sorts:
% 3.81/1.75  
% 3.81/1.75  
% 3.81/1.75  %Background operators:
% 3.81/1.75  
% 3.81/1.75  
% 3.81/1.75  %Foreground operators:
% 3.81/1.75  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.81/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.81/1.75  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.81/1.75  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.81/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.81/1.75  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.81/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.81/1.75  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.81/1.75  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.81/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.81/1.75  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.81/1.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.81/1.75  tff('#skF_2', type, '#skF_2': $i).
% 3.81/1.75  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.81/1.75  tff('#skF_3', type, '#skF_3': $i).
% 3.81/1.75  tff('#skF_1', type, '#skF_1': $i).
% 3.81/1.75  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.81/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.81/1.75  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.81/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.81/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.81/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.81/1.75  tff('#skF_4', type, '#skF_4': $i).
% 3.81/1.75  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.81/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.81/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.81/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.81/1.75  
% 3.90/1.77  tff(f_139, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 3.90/1.77  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.90/1.77  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.90/1.77  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.90/1.77  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.90/1.77  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.90/1.77  tff(f_113, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.90/1.77  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 3.90/1.77  tff(f_71, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.90/1.77  tff(f_57, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 3.90/1.77  tff(f_111, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.90/1.77  tff(f_101, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.90/1.77  tff(f_79, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.90/1.77  tff(c_40, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.90/1.77  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.90/1.77  tff(c_44, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.90/1.77  tff(c_54, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.90/1.77  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.90/1.77  tff(c_143, plain, (![A_60, B_61, C_62]: (k1_relset_1(A_60, B_61, C_62)=k1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.90/1.77  tff(c_154, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_143])).
% 3.90/1.77  tff(c_219, plain, (![B_74, A_75, C_76]: (k1_xboole_0=B_74 | k1_relset_1(A_75, B_74, C_76)=A_75 | ~v1_funct_2(C_76, A_75, B_74) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.90/1.77  tff(c_225, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_219])).
% 3.90/1.77  tff(c_233, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_154, c_225])).
% 3.90/1.77  tff(c_234, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_44, c_233])).
% 3.90/1.77  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.90/1.77  tff(c_80, plain, (![B_48, A_49]: (v1_relat_1(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.90/1.77  tff(c_86, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_80])).
% 3.90/1.77  tff(c_95, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_86])).
% 3.90/1.77  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.90/1.77  tff(c_89, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_80])).
% 3.90/1.77  tff(c_98, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_89])).
% 3.90/1.77  tff(c_62, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.90/1.77  tff(c_46, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.90/1.77  tff(c_50, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.90/1.77  tff(c_111, plain, (![A_55, B_56, C_57]: (k2_relset_1(A_55, B_56, C_57)=k2_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.90/1.77  tff(c_120, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_111])).
% 3.90/1.77  tff(c_124, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_120])).
% 3.90/1.77  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.90/1.77  tff(c_60, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.90/1.77  tff(c_155, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_143])).
% 3.90/1.77  tff(c_228, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_219])).
% 3.90/1.77  tff(c_237, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_155, c_228])).
% 3.90/1.77  tff(c_238, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_42, c_237])).
% 3.90/1.77  tff(c_38, plain, (![A_41]: (k6_relat_1(A_41)=k6_partfun1(A_41))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.90/1.77  tff(c_6, plain, (![A_6, B_8]: (k2_funct_1(A_6)=B_8 | k6_relat_1(k1_relat_1(A_6))!=k5_relat_1(A_6, B_8) | k2_relat_1(A_6)!=k1_relat_1(B_8) | ~v2_funct_1(A_6) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.90/1.77  tff(c_987, plain, (![A_132, B_133]: (k2_funct_1(A_132)=B_133 | k6_partfun1(k1_relat_1(A_132))!=k5_relat_1(A_132, B_133) | k2_relat_1(A_132)!=k1_relat_1(B_133) | ~v2_funct_1(A_132) | ~v1_funct_1(B_133) | ~v1_relat_1(B_133) | ~v1_funct_1(A_132) | ~v1_relat_1(A_132))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_6])).
% 3.90/1.77  tff(c_989, plain, (![B_133]: (k2_funct_1('#skF_3')=B_133 | k5_relat_1('#skF_3', B_133)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_133) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_133) | ~v1_relat_1(B_133) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_238, c_987])).
% 3.90/1.77  tff(c_996, plain, (![B_134]: (k2_funct_1('#skF_3')=B_134 | k5_relat_1('#skF_3', B_134)!=k6_partfun1('#skF_1') | k1_relat_1(B_134)!='#skF_2' | ~v1_funct_1(B_134) | ~v1_relat_1(B_134))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_62, c_46, c_124, c_989])).
% 3.90/1.77  tff(c_1005, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_95, c_996])).
% 3.90/1.77  tff(c_1015, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_234, c_1005])).
% 3.90/1.77  tff(c_1016, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_1015])).
% 3.90/1.77  tff(c_287, plain, (![A_82, F_85, C_84, E_87, D_83, B_86]: (k4_relset_1(A_82, B_86, C_84, D_83, E_87, F_85)=k5_relat_1(E_87, F_85) | ~m1_subset_1(F_85, k1_zfmisc_1(k2_zfmisc_1(C_84, D_83))) | ~m1_subset_1(E_87, k1_zfmisc_1(k2_zfmisc_1(A_82, B_86))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.90/1.77  tff(c_297, plain, (![A_88, B_89, E_90]: (k4_relset_1(A_88, B_89, '#skF_2', '#skF_1', E_90, '#skF_4')=k5_relat_1(E_90, '#skF_4') | ~m1_subset_1(E_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(resolution, [status(thm)], [c_52, c_287])).
% 3.90/1.77  tff(c_309, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_297])).
% 3.90/1.77  tff(c_390, plain, (![E_104, C_102, D_103, A_105, B_101, F_100]: (m1_subset_1(k4_relset_1(A_105, B_101, C_102, D_103, E_104, F_100), k1_zfmisc_1(k2_zfmisc_1(A_105, D_103))) | ~m1_subset_1(F_100, k1_zfmisc_1(k2_zfmisc_1(C_102, D_103))) | ~m1_subset_1(E_104, k1_zfmisc_1(k2_zfmisc_1(A_105, B_101))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.90/1.77  tff(c_442, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_309, c_390])).
% 3.90/1.77  tff(c_469, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52, c_442])).
% 3.90/1.77  tff(c_645, plain, (![B_111, C_108, A_106, F_107, E_109, D_110]: (k1_partfun1(A_106, B_111, C_108, D_110, E_109, F_107)=k5_relat_1(E_109, F_107) | ~m1_subset_1(F_107, k1_zfmisc_1(k2_zfmisc_1(C_108, D_110))) | ~v1_funct_1(F_107) | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_106, B_111))) | ~v1_funct_1(E_109))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.90/1.77  tff(c_659, plain, (![A_106, B_111, E_109]: (k1_partfun1(A_106, B_111, '#skF_2', '#skF_1', E_109, '#skF_4')=k5_relat_1(E_109, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_106, B_111))) | ~v1_funct_1(E_109))), inference(resolution, [status(thm)], [c_52, c_645])).
% 3.90/1.77  tff(c_884, plain, (![A_119, B_120, E_121]: (k1_partfun1(A_119, B_120, '#skF_2', '#skF_1', E_121, '#skF_4')=k5_relat_1(E_121, '#skF_4') | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~v1_funct_1(E_121))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_659])).
% 3.90/1.77  tff(c_914, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_884])).
% 3.90/1.77  tff(c_928, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_914])).
% 3.90/1.77  tff(c_34, plain, (![A_34]: (m1_subset_1(k6_partfun1(A_34), k1_zfmisc_1(k2_zfmisc_1(A_34, A_34))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.90/1.77  tff(c_48, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.90/1.77  tff(c_253, plain, (![D_77, C_78, A_79, B_80]: (D_77=C_78 | ~r2_relset_1(A_79, B_80, C_78, D_77) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.90/1.77  tff(c_261, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_48, c_253])).
% 3.90/1.77  tff(c_276, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_261])).
% 3.90/1.77  tff(c_286, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_276])).
% 3.90/1.77  tff(c_933, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_928, c_286])).
% 3.90/1.77  tff(c_937, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_469, c_933])).
% 3.90/1.77  tff(c_938, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_276])).
% 3.90/1.77  tff(c_1305, plain, (![C_148, E_149, D_150, A_146, B_151, F_147]: (k1_partfun1(A_146, B_151, C_148, D_150, E_149, F_147)=k5_relat_1(E_149, F_147) | ~m1_subset_1(F_147, k1_zfmisc_1(k2_zfmisc_1(C_148, D_150))) | ~v1_funct_1(F_147) | ~m1_subset_1(E_149, k1_zfmisc_1(k2_zfmisc_1(A_146, B_151))) | ~v1_funct_1(E_149))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.90/1.77  tff(c_1319, plain, (![A_146, B_151, E_149]: (k1_partfun1(A_146, B_151, '#skF_2', '#skF_1', E_149, '#skF_4')=k5_relat_1(E_149, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_149, k1_zfmisc_1(k2_zfmisc_1(A_146, B_151))) | ~v1_funct_1(E_149))), inference(resolution, [status(thm)], [c_52, c_1305])).
% 3.90/1.77  tff(c_1544, plain, (![A_159, B_160, E_161]: (k1_partfun1(A_159, B_160, '#skF_2', '#skF_1', E_161, '#skF_4')=k5_relat_1(E_161, '#skF_4') | ~m1_subset_1(E_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))) | ~v1_funct_1(E_161))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1319])).
% 3.90/1.77  tff(c_1574, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_1544])).
% 3.90/1.77  tff(c_1588, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_938, c_1574])).
% 3.90/1.77  tff(c_1590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1016, c_1588])).
% 3.90/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.77  
% 3.90/1.77  Inference rules
% 3.90/1.77  ----------------------
% 3.90/1.77  #Ref     : 0
% 3.90/1.77  #Sup     : 357
% 3.90/1.77  #Fact    : 0
% 3.90/1.77  #Define  : 0
% 3.90/1.77  #Split   : 10
% 3.90/1.77  #Chain   : 0
% 3.90/1.77  #Close   : 0
% 3.90/1.77  
% 3.90/1.77  Ordering : KBO
% 3.90/1.77  
% 3.90/1.77  Simplification rules
% 3.90/1.77  ----------------------
% 3.90/1.77  #Subsume      : 1
% 3.90/1.77  #Demod        : 111
% 3.90/1.77  #Tautology    : 85
% 3.90/1.77  #SimpNegUnit  : 32
% 3.90/1.77  #BackRed      : 7
% 3.90/1.77  
% 3.90/1.77  #Partial instantiations: 0
% 3.90/1.77  #Strategies tried      : 1
% 3.90/1.77  
% 3.90/1.77  Timing (in seconds)
% 3.90/1.77  ----------------------
% 3.90/1.78  Preprocessing        : 0.33
% 3.90/1.78  Parsing              : 0.17
% 3.90/1.78  CNF conversion       : 0.02
% 3.90/1.78  Main loop            : 0.52
% 3.90/1.78  Inferencing          : 0.17
% 3.90/1.78  Reduction            : 0.18
% 3.90/1.78  Demodulation         : 0.12
% 3.90/1.78  BG Simplification    : 0.03
% 3.90/1.78  Subsumption          : 0.08
% 3.90/1.78  Abstraction          : 0.03
% 3.90/1.78  MUC search           : 0.00
% 3.90/1.78  Cooper               : 0.00
% 3.90/1.78  Total                : 0.89
% 3.90/1.78  Index Insertion      : 0.00
% 3.90/1.78  Index Deletion       : 0.00
% 3.90/1.78  Index Matching       : 0.00
% 3.90/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
