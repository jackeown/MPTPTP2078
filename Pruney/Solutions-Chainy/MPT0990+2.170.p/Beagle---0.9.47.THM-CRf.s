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
% DateTime   : Thu Dec  3 10:13:21 EST 2020

% Result     : Theorem 9.25s
% Output     : CNFRefutation 9.25s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 233 expanded)
%              Number of leaves         :   43 ( 103 expanded)
%              Depth                    :   11
%              Number of atoms          :  294 ( 940 expanded)
%              Number of equality atoms :   95 ( 293 expanded)
%              Maximal formula depth    :   16 (   5 average)
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

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_180,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_138,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_122,axiom,(
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

tff(f_96,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_136,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_126,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_154,axiom,(
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

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ! [D] :
              ( ( v1_relat_1(D)
                & v1_funct_1(D) )
             => ( ( k2_relat_1(B) = A
                  & k5_relat_1(B,C) = k6_relat_1(k1_relat_1(D))
                  & k5_relat_1(C,D) = k6_relat_1(A) )
               => D = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l72_funct_1)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_96,plain,(
    ! [B_58,A_59] :
      ( v1_relat_1(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_102,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_96])).

tff(c_111,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_102])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_60,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_176,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_182,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_176])).

tff(c_188,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_182])).

tff(c_46,plain,(
    ! [A_48] : k6_relat_1(A_48) = k6_partfun1(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_12,plain,(
    ! [A_15] :
      ( k5_relat_1(k2_funct_1(A_15),A_15) = k6_relat_1(k2_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_78,plain,(
    ! [A_15] :
      ( k5_relat_1(k2_funct_1(A_15),A_15) = k6_partfun1(k2_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12])).

tff(c_54,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_105,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_96])).

tff(c_114,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_105])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_145,plain,(
    ! [A_67,B_68,C_69] :
      ( k1_relset_1(A_67,B_68,C_69) = k1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_157,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_145])).

tff(c_271,plain,(
    ! [B_88,A_89,C_90] :
      ( k1_xboole_0 = B_88
      | k1_relset_1(A_89,B_88,C_90) = A_89
      | ~ v1_funct_2(C_90,A_89,B_88)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_280,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_271])).

tff(c_289,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_157,c_280])).

tff(c_290,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_289])).

tff(c_339,plain,(
    ! [C_99,A_98,F_96,D_101,B_100,E_97] :
      ( k4_relset_1(A_98,B_100,C_99,D_101,E_97,F_96) = k5_relat_1(E_97,F_96)
      | ~ m1_subset_1(F_96,k1_zfmisc_1(k2_zfmisc_1(C_99,D_101)))
      | ~ m1_subset_1(E_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_368,plain,(
    ! [A_105,B_106,E_107] :
      ( k4_relset_1(A_105,B_106,'#skF_2','#skF_1',E_107,'#skF_4') = k5_relat_1(E_107,'#skF_4')
      | ~ m1_subset_1(E_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(resolution,[status(thm)],[c_66,c_339])).

tff(c_379,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_368])).

tff(c_415,plain,(
    ! [D_116,F_112,A_115,B_113,C_117,E_114] :
      ( m1_subset_1(k4_relset_1(A_115,B_113,C_117,D_116,E_114,F_112),k1_zfmisc_1(k2_zfmisc_1(A_115,D_116)))
      | ~ m1_subset_1(F_112,k1_zfmisc_1(k2_zfmisc_1(C_117,D_116)))
      | ~ m1_subset_1(E_114,k1_zfmisc_1(k2_zfmisc_1(A_115,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_467,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_415])).

tff(c_490,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_66,c_467])).

tff(c_1003,plain,(
    ! [B_137,C_140,A_138,F_139,D_136,E_135] :
      ( k1_partfun1(A_138,B_137,C_140,D_136,E_135,F_139) = k5_relat_1(E_135,F_139)
      | ~ m1_subset_1(F_139,k1_zfmisc_1(k2_zfmisc_1(C_140,D_136)))
      | ~ v1_funct_1(F_139)
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137)))
      | ~ v1_funct_1(E_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1025,plain,(
    ! [A_138,B_137,E_135] :
      ( k1_partfun1(A_138,B_137,'#skF_2','#skF_1',E_135,'#skF_4') = k5_relat_1(E_135,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137)))
      | ~ v1_funct_1(E_135) ) ),
    inference(resolution,[status(thm)],[c_66,c_1003])).

tff(c_1279,plain,(
    ! [A_157,B_158,E_159] :
      ( k1_partfun1(A_157,B_158,'#skF_2','#skF_1',E_159,'#skF_4') = k5_relat_1(E_159,'#skF_4')
      | ~ m1_subset_1(E_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158)))
      | ~ v1_funct_1(E_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1025])).

tff(c_1315,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1279])).

tff(c_1332,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1315])).

tff(c_42,plain,(
    ! [A_41] : m1_subset_1(k6_partfun1(A_41),k1_zfmisc_1(k2_zfmisc_1(A_41,A_41))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_62,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_314,plain,(
    ! [D_92,C_93,A_94,B_95] :
      ( D_92 = C_93
      | ~ r2_relset_1(A_94,B_95,C_93,D_92)
      | ~ m1_subset_1(D_92,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_322,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_62,c_314])).

tff(c_337,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_322])).

tff(c_338,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_337])).

tff(c_1336,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1332,c_338])).

tff(c_1340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_1336])).

tff(c_1341,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_337])).

tff(c_2120,plain,(
    ! [A_206,D_204,B_205,F_207,E_203,C_208] :
      ( k1_partfun1(A_206,B_205,C_208,D_204,E_203,F_207) = k5_relat_1(E_203,F_207)
      | ~ m1_subset_1(F_207,k1_zfmisc_1(k2_zfmisc_1(C_208,D_204)))
      | ~ v1_funct_1(F_207)
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(A_206,B_205)))
      | ~ v1_funct_1(E_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2146,plain,(
    ! [A_206,B_205,E_203] :
      ( k1_partfun1(A_206,B_205,'#skF_2','#skF_1',E_203,'#skF_4') = k5_relat_1(E_203,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(A_206,B_205)))
      | ~ v1_funct_1(E_203) ) ),
    inference(resolution,[status(thm)],[c_66,c_2120])).

tff(c_2360,plain,(
    ! [A_225,B_226,E_227] :
      ( k1_partfun1(A_225,B_226,'#skF_2','#skF_1',E_227,'#skF_4') = k5_relat_1(E_227,'#skF_4')
      | ~ m1_subset_1(E_227,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226)))
      | ~ v1_funct_1(E_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2146])).

tff(c_2396,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_2360])).

tff(c_2413,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1341,c_2396])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_1975,plain,(
    ! [C_197,B_198,A_199] :
      ( m1_subset_1(k2_funct_1(C_197),k1_zfmisc_1(k2_zfmisc_1(B_198,A_199)))
      | k2_relset_1(A_199,B_198,C_197) != B_198
      | ~ v2_funct_1(C_197)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_199,B_198)))
      | ~ v1_funct_2(C_197,A_199,B_198)
      | ~ v1_funct_1(C_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2020,plain,(
    ! [C_197,B_198,A_199] :
      ( v1_relat_1(k2_funct_1(C_197))
      | ~ v1_relat_1(k2_zfmisc_1(B_198,A_199))
      | k2_relset_1(A_199,B_198,C_197) != B_198
      | ~ v2_funct_1(C_197)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_199,B_198)))
      | ~ v1_funct_2(C_197,A_199,B_198)
      | ~ v1_funct_1(C_197) ) ),
    inference(resolution,[status(thm)],[c_1975,c_2])).

tff(c_2840,plain,(
    ! [C_264,A_265,B_266] :
      ( v1_relat_1(k2_funct_1(C_264))
      | k2_relset_1(A_265,B_266,C_264) != B_266
      | ~ v2_funct_1(C_264)
      | ~ m1_subset_1(C_264,k1_zfmisc_1(k2_zfmisc_1(A_265,B_266)))
      | ~ v1_funct_2(C_264,A_265,B_266)
      | ~ v1_funct_1(C_264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2020])).

tff(c_2879,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_2840])).

tff(c_2906,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_60,c_64,c_2879])).

tff(c_1403,plain,(
    ! [C_173,A_174,B_175] :
      ( v1_funct_1(k2_funct_1(C_173))
      | k2_relset_1(A_174,B_175,C_173) != B_175
      | ~ v2_funct_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175)))
      | ~ v1_funct_2(C_173,A_174,B_175)
      | ~ v1_funct_1(C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1409,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1403])).

tff(c_1417,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_60,c_64,c_1409])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_156,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_145])).

tff(c_277,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_271])).

tff(c_285,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_156,c_277])).

tff(c_286,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_285])).

tff(c_8,plain,(
    ! [A_14] :
      ( k2_relat_1(k2_funct_1(A_14)) = k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [D_13,B_7,C_11] :
      ( D_13 = B_7
      | k6_relat_1(k2_relat_1(B_7)) != k5_relat_1(C_11,D_13)
      | k6_relat_1(k1_relat_1(D_13)) != k5_relat_1(B_7,C_11)
      | ~ v1_funct_1(D_13)
      | ~ v1_relat_1(D_13)
      | ~ v1_funct_1(C_11)
      | ~ v1_relat_1(C_11)
      | ~ v1_funct_1(B_7)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2194,plain,(
    ! [D_209,B_210,C_211] :
      ( D_209 = B_210
      | k6_partfun1(k2_relat_1(B_210)) != k5_relat_1(C_211,D_209)
      | k6_partfun1(k1_relat_1(D_209)) != k5_relat_1(B_210,C_211)
      | ~ v1_funct_1(D_209)
      | ~ v1_relat_1(D_209)
      | ~ v1_funct_1(C_211)
      | ~ v1_relat_1(C_211)
      | ~ v1_funct_1(B_210)
      | ~ v1_relat_1(B_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_6])).

tff(c_5140,plain,(
    ! [A_414,D_415,C_416] :
      ( k2_funct_1(A_414) = D_415
      | k6_partfun1(k1_relat_1(A_414)) != k5_relat_1(C_416,D_415)
      | k6_partfun1(k1_relat_1(D_415)) != k5_relat_1(k2_funct_1(A_414),C_416)
      | ~ v1_funct_1(D_415)
      | ~ v1_relat_1(D_415)
      | ~ v1_funct_1(C_416)
      | ~ v1_relat_1(C_416)
      | ~ v1_funct_1(k2_funct_1(A_414))
      | ~ v1_relat_1(k2_funct_1(A_414))
      | ~ v2_funct_1(A_414)
      | ~ v1_funct_1(A_414)
      | ~ v1_relat_1(A_414) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2194])).

tff(c_5146,plain,(
    ! [D_415,C_416] :
      ( k2_funct_1('#skF_3') = D_415
      | k5_relat_1(C_416,D_415) != k6_partfun1('#skF_1')
      | k6_partfun1(k1_relat_1(D_415)) != k5_relat_1(k2_funct_1('#skF_3'),C_416)
      | ~ v1_funct_1(D_415)
      | ~ v1_relat_1(D_415)
      | ~ v1_funct_1(C_416)
      | ~ v1_relat_1(C_416)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_5140])).

tff(c_6902,plain,(
    ! [D_558,C_559] :
      ( k2_funct_1('#skF_3') = D_558
      | k5_relat_1(C_559,D_558) != k6_partfun1('#skF_1')
      | k6_partfun1(k1_relat_1(D_558)) != k5_relat_1(k2_funct_1('#skF_3'),C_559)
      | ~ v1_funct_1(D_558)
      | ~ v1_relat_1(D_558)
      | ~ v1_funct_1(C_559)
      | ~ v1_relat_1(C_559) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_76,c_60,c_2906,c_1417,c_5146])).

tff(c_6904,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2413,c_6902])).

tff(c_6911,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_76,c_114,c_70,c_290,c_6904])).

tff(c_6912,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_6911])).

tff(c_6915,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) != k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_6912])).

tff(c_6918,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_76,c_60,c_188,c_6915])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.25/3.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.25/3.53  
% 9.25/3.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.25/3.53  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.25/3.53  
% 9.25/3.53  %Foreground sorts:
% 9.25/3.53  
% 9.25/3.53  
% 9.25/3.53  %Background operators:
% 9.25/3.53  
% 9.25/3.53  
% 9.25/3.53  %Foreground operators:
% 9.25/3.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.25/3.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.25/3.53  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.25/3.53  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.25/3.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.25/3.53  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.25/3.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.25/3.53  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.25/3.53  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.25/3.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.25/3.53  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.25/3.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.25/3.53  tff('#skF_2', type, '#skF_2': $i).
% 9.25/3.53  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.25/3.53  tff('#skF_3', type, '#skF_3': $i).
% 9.25/3.53  tff('#skF_1', type, '#skF_1': $i).
% 9.25/3.53  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.25/3.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.25/3.53  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.25/3.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.25/3.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.25/3.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.25/3.53  tff('#skF_4', type, '#skF_4': $i).
% 9.25/3.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.25/3.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.25/3.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.25/3.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.25/3.53  
% 9.25/3.55  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.25/3.55  tff(f_180, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 9.25/3.55  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.25/3.55  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.25/3.55  tff(f_138, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.25/3.55  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 9.25/3.55  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.25/3.55  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.25/3.55  tff(f_96, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 9.25/3.55  tff(f_82, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 9.25/3.55  tff(f_136, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.25/3.55  tff(f_126, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 9.25/3.55  tff(f_104, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.25/3.55  tff(f_154, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 9.25/3.55  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 9.25/3.55  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (![D]: ((v1_relat_1(D) & v1_funct_1(D)) => ((((k2_relat_1(B) = A) & (k5_relat_1(B, C) = k6_relat_1(k1_relat_1(D)))) & (k5_relat_1(C, D) = k6_relat_1(A))) => (D = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l72_funct_1)).
% 9.25/3.55  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.25/3.55  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.25/3.55  tff(c_96, plain, (![B_58, A_59]: (v1_relat_1(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.25/3.55  tff(c_102, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_96])).
% 9.25/3.55  tff(c_111, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_102])).
% 9.25/3.55  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.25/3.55  tff(c_60, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.25/3.55  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.25/3.55  tff(c_176, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 9.25/3.55  tff(c_182, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_176])).
% 9.25/3.55  tff(c_188, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_182])).
% 9.25/3.55  tff(c_46, plain, (![A_48]: (k6_relat_1(A_48)=k6_partfun1(A_48))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.25/3.55  tff(c_12, plain, (![A_15]: (k5_relat_1(k2_funct_1(A_15), A_15)=k6_relat_1(k2_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.25/3.55  tff(c_78, plain, (![A_15]: (k5_relat_1(k2_funct_1(A_15), A_15)=k6_partfun1(k2_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12])).
% 9.25/3.55  tff(c_54, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.25/3.55  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.25/3.55  tff(c_105, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_66, c_96])).
% 9.25/3.55  tff(c_114, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_105])).
% 9.25/3.55  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.25/3.55  tff(c_58, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.25/3.55  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.25/3.55  tff(c_145, plain, (![A_67, B_68, C_69]: (k1_relset_1(A_67, B_68, C_69)=k1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.25/3.55  tff(c_157, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_145])).
% 9.25/3.55  tff(c_271, plain, (![B_88, A_89, C_90]: (k1_xboole_0=B_88 | k1_relset_1(A_89, B_88, C_90)=A_89 | ~v1_funct_2(C_90, A_89, B_88) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.25/3.55  tff(c_280, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_271])).
% 9.25/3.55  tff(c_289, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_157, c_280])).
% 9.25/3.55  tff(c_290, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_58, c_289])).
% 9.25/3.55  tff(c_339, plain, (![C_99, A_98, F_96, D_101, B_100, E_97]: (k4_relset_1(A_98, B_100, C_99, D_101, E_97, F_96)=k5_relat_1(E_97, F_96) | ~m1_subset_1(F_96, k1_zfmisc_1(k2_zfmisc_1(C_99, D_101))) | ~m1_subset_1(E_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_100))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.25/3.55  tff(c_368, plain, (![A_105, B_106, E_107]: (k4_relset_1(A_105, B_106, '#skF_2', '#skF_1', E_107, '#skF_4')=k5_relat_1(E_107, '#skF_4') | ~m1_subset_1(E_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(resolution, [status(thm)], [c_66, c_339])).
% 9.25/3.55  tff(c_379, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_368])).
% 9.25/3.55  tff(c_415, plain, (![D_116, F_112, A_115, B_113, C_117, E_114]: (m1_subset_1(k4_relset_1(A_115, B_113, C_117, D_116, E_114, F_112), k1_zfmisc_1(k2_zfmisc_1(A_115, D_116))) | ~m1_subset_1(F_112, k1_zfmisc_1(k2_zfmisc_1(C_117, D_116))) | ~m1_subset_1(E_114, k1_zfmisc_1(k2_zfmisc_1(A_115, B_113))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.25/3.55  tff(c_467, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_379, c_415])).
% 9.25/3.55  tff(c_490, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_66, c_467])).
% 9.25/3.55  tff(c_1003, plain, (![B_137, C_140, A_138, F_139, D_136, E_135]: (k1_partfun1(A_138, B_137, C_140, D_136, E_135, F_139)=k5_relat_1(E_135, F_139) | ~m1_subset_1(F_139, k1_zfmisc_1(k2_zfmisc_1(C_140, D_136))) | ~v1_funct_1(F_139) | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))) | ~v1_funct_1(E_135))), inference(cnfTransformation, [status(thm)], [f_136])).
% 9.25/3.55  tff(c_1025, plain, (![A_138, B_137, E_135]: (k1_partfun1(A_138, B_137, '#skF_2', '#skF_1', E_135, '#skF_4')=k5_relat_1(E_135, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))) | ~v1_funct_1(E_135))), inference(resolution, [status(thm)], [c_66, c_1003])).
% 9.25/3.55  tff(c_1279, plain, (![A_157, B_158, E_159]: (k1_partfun1(A_157, B_158, '#skF_2', '#skF_1', E_159, '#skF_4')=k5_relat_1(E_159, '#skF_4') | ~m1_subset_1(E_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))) | ~v1_funct_1(E_159))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1025])).
% 9.25/3.55  tff(c_1315, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1279])).
% 9.25/3.55  tff(c_1332, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1315])).
% 9.25/3.55  tff(c_42, plain, (![A_41]: (m1_subset_1(k6_partfun1(A_41), k1_zfmisc_1(k2_zfmisc_1(A_41, A_41))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 9.25/3.55  tff(c_62, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.25/3.55  tff(c_314, plain, (![D_92, C_93, A_94, B_95]: (D_92=C_93 | ~r2_relset_1(A_94, B_95, C_93, D_92) | ~m1_subset_1(D_92, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.25/3.55  tff(c_322, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_62, c_314])).
% 9.25/3.55  tff(c_337, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_322])).
% 9.25/3.55  tff(c_338, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_337])).
% 9.25/3.55  tff(c_1336, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1332, c_338])).
% 9.25/3.55  tff(c_1340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_490, c_1336])).
% 9.25/3.55  tff(c_1341, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_337])).
% 9.25/3.55  tff(c_2120, plain, (![A_206, D_204, B_205, F_207, E_203, C_208]: (k1_partfun1(A_206, B_205, C_208, D_204, E_203, F_207)=k5_relat_1(E_203, F_207) | ~m1_subset_1(F_207, k1_zfmisc_1(k2_zfmisc_1(C_208, D_204))) | ~v1_funct_1(F_207) | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(A_206, B_205))) | ~v1_funct_1(E_203))), inference(cnfTransformation, [status(thm)], [f_136])).
% 9.25/3.55  tff(c_2146, plain, (![A_206, B_205, E_203]: (k1_partfun1(A_206, B_205, '#skF_2', '#skF_1', E_203, '#skF_4')=k5_relat_1(E_203, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(A_206, B_205))) | ~v1_funct_1(E_203))), inference(resolution, [status(thm)], [c_66, c_2120])).
% 9.25/3.55  tff(c_2360, plain, (![A_225, B_226, E_227]: (k1_partfun1(A_225, B_226, '#skF_2', '#skF_1', E_227, '#skF_4')=k5_relat_1(E_227, '#skF_4') | ~m1_subset_1(E_227, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))) | ~v1_funct_1(E_227))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2146])).
% 9.25/3.55  tff(c_2396, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_2360])).
% 9.25/3.55  tff(c_2413, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1341, c_2396])).
% 9.25/3.55  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.25/3.55  tff(c_1975, plain, (![C_197, B_198, A_199]: (m1_subset_1(k2_funct_1(C_197), k1_zfmisc_1(k2_zfmisc_1(B_198, A_199))) | k2_relset_1(A_199, B_198, C_197)!=B_198 | ~v2_funct_1(C_197) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_199, B_198))) | ~v1_funct_2(C_197, A_199, B_198) | ~v1_funct_1(C_197))), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.25/3.55  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.25/3.55  tff(c_2020, plain, (![C_197, B_198, A_199]: (v1_relat_1(k2_funct_1(C_197)) | ~v1_relat_1(k2_zfmisc_1(B_198, A_199)) | k2_relset_1(A_199, B_198, C_197)!=B_198 | ~v2_funct_1(C_197) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_199, B_198))) | ~v1_funct_2(C_197, A_199, B_198) | ~v1_funct_1(C_197))), inference(resolution, [status(thm)], [c_1975, c_2])).
% 9.25/3.55  tff(c_2840, plain, (![C_264, A_265, B_266]: (v1_relat_1(k2_funct_1(C_264)) | k2_relset_1(A_265, B_266, C_264)!=B_266 | ~v2_funct_1(C_264) | ~m1_subset_1(C_264, k1_zfmisc_1(k2_zfmisc_1(A_265, B_266))) | ~v1_funct_2(C_264, A_265, B_266) | ~v1_funct_1(C_264))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2020])).
% 9.25/3.55  tff(c_2879, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_2840])).
% 9.25/3.55  tff(c_2906, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_60, c_64, c_2879])).
% 9.25/3.55  tff(c_1403, plain, (![C_173, A_174, B_175]: (v1_funct_1(k2_funct_1(C_173)) | k2_relset_1(A_174, B_175, C_173)!=B_175 | ~v2_funct_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))) | ~v1_funct_2(C_173, A_174, B_175) | ~v1_funct_1(C_173))), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.25/3.55  tff(c_1409, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1403])).
% 9.25/3.55  tff(c_1417, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_60, c_64, c_1409])).
% 9.25/3.55  tff(c_56, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_180])).
% 9.25/3.55  tff(c_156, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_145])).
% 9.25/3.55  tff(c_277, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_271])).
% 9.25/3.55  tff(c_285, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_156, c_277])).
% 9.25/3.55  tff(c_286, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_56, c_285])).
% 9.25/3.55  tff(c_8, plain, (![A_14]: (k2_relat_1(k2_funct_1(A_14))=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.25/3.55  tff(c_6, plain, (![D_13, B_7, C_11]: (D_13=B_7 | k6_relat_1(k2_relat_1(B_7))!=k5_relat_1(C_11, D_13) | k6_relat_1(k1_relat_1(D_13))!=k5_relat_1(B_7, C_11) | ~v1_funct_1(D_13) | ~v1_relat_1(D_13) | ~v1_funct_1(C_11) | ~v1_relat_1(C_11) | ~v1_funct_1(B_7) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.25/3.55  tff(c_2194, plain, (![D_209, B_210, C_211]: (D_209=B_210 | k6_partfun1(k2_relat_1(B_210))!=k5_relat_1(C_211, D_209) | k6_partfun1(k1_relat_1(D_209))!=k5_relat_1(B_210, C_211) | ~v1_funct_1(D_209) | ~v1_relat_1(D_209) | ~v1_funct_1(C_211) | ~v1_relat_1(C_211) | ~v1_funct_1(B_210) | ~v1_relat_1(B_210))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_6])).
% 9.25/3.55  tff(c_5140, plain, (![A_414, D_415, C_416]: (k2_funct_1(A_414)=D_415 | k6_partfun1(k1_relat_1(A_414))!=k5_relat_1(C_416, D_415) | k6_partfun1(k1_relat_1(D_415))!=k5_relat_1(k2_funct_1(A_414), C_416) | ~v1_funct_1(D_415) | ~v1_relat_1(D_415) | ~v1_funct_1(C_416) | ~v1_relat_1(C_416) | ~v1_funct_1(k2_funct_1(A_414)) | ~v1_relat_1(k2_funct_1(A_414)) | ~v2_funct_1(A_414) | ~v1_funct_1(A_414) | ~v1_relat_1(A_414))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2194])).
% 9.25/3.55  tff(c_5146, plain, (![D_415, C_416]: (k2_funct_1('#skF_3')=D_415 | k5_relat_1(C_416, D_415)!=k6_partfun1('#skF_1') | k6_partfun1(k1_relat_1(D_415))!=k5_relat_1(k2_funct_1('#skF_3'), C_416) | ~v1_funct_1(D_415) | ~v1_relat_1(D_415) | ~v1_funct_1(C_416) | ~v1_relat_1(C_416) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_286, c_5140])).
% 9.25/3.55  tff(c_6902, plain, (![D_558, C_559]: (k2_funct_1('#skF_3')=D_558 | k5_relat_1(C_559, D_558)!=k6_partfun1('#skF_1') | k6_partfun1(k1_relat_1(D_558))!=k5_relat_1(k2_funct_1('#skF_3'), C_559) | ~v1_funct_1(D_558) | ~v1_relat_1(D_558) | ~v1_funct_1(C_559) | ~v1_relat_1(C_559))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_76, c_60, c_2906, c_1417, c_5146])).
% 9.25/3.55  tff(c_6904, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2413, c_6902])).
% 9.25/3.55  tff(c_6911, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_76, c_114, c_70, c_290, c_6904])).
% 9.25/3.55  tff(c_6912, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_6911])).
% 9.25/3.55  tff(c_6915, plain, (k6_partfun1(k2_relat_1('#skF_3'))!=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_78, c_6912])).
% 9.25/3.55  tff(c_6918, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_76, c_60, c_188, c_6915])).
% 9.25/3.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.25/3.55  
% 9.25/3.55  Inference rules
% 9.25/3.55  ----------------------
% 9.25/3.55  #Ref     : 0
% 9.25/3.55  #Sup     : 1611
% 9.25/3.55  #Fact    : 0
% 9.25/3.55  #Define  : 0
% 9.25/3.55  #Split   : 24
% 9.25/3.55  #Chain   : 0
% 9.25/3.55  #Close   : 0
% 9.25/3.55  
% 9.25/3.55  Ordering : KBO
% 9.25/3.55  
% 9.25/3.55  Simplification rules
% 9.25/3.55  ----------------------
% 9.25/3.55  #Subsume      : 91
% 9.25/3.55  #Demod        : 1156
% 9.25/3.55  #Tautology    : 329
% 9.25/3.55  #SimpNegUnit  : 138
% 9.25/3.55  #BackRed      : 29
% 9.25/3.55  
% 9.25/3.55  #Partial instantiations: 0
% 9.25/3.55  #Strategies tried      : 1
% 9.25/3.55  
% 9.25/3.55  Timing (in seconds)
% 9.25/3.55  ----------------------
% 9.25/3.56  Preprocessing        : 0.37
% 9.25/3.56  Parsing              : 0.20
% 9.25/3.56  CNF conversion       : 0.03
% 9.25/3.56  Main loop            : 2.43
% 9.25/3.56  Inferencing          : 0.66
% 9.25/3.56  Reduction            : 1.11
% 9.25/3.56  Demodulation         : 0.87
% 9.25/3.56  BG Simplification    : 0.07
% 9.25/3.56  Subsumption          : 0.42
% 9.25/3.56  Abstraction          : 0.11
% 9.25/3.56  MUC search           : 0.00
% 9.25/3.56  Cooper               : 0.00
% 9.25/3.56  Total                : 2.84
% 9.25/3.56  Index Insertion      : 0.00
% 9.25/3.56  Index Deletion       : 0.00
% 9.25/3.56  Index Matching       : 0.00
% 9.25/3.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
