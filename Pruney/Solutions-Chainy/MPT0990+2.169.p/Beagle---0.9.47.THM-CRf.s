%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:21 EST 2020

% Result     : Theorem 7.74s
% Output     : CNFRefutation 7.74s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 291 expanded)
%              Number of leaves         :   43 ( 123 expanded)
%              Depth                    :   13
%              Number of atoms          :  268 (1199 expanded)
%              Number of equality atoms :   88 ( 387 expanded)
%              Maximal formula depth    :   16 (   4 average)
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

tff(f_176,negated_conjecture,(
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

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_150,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_134,axiom,(
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

tff(f_108,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_138,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_148,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_116,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_68,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_96,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
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
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_60,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_179,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_185,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_179])).

tff(c_191,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_185])).

tff(c_52,plain,(
    ! [A_49] : k6_relat_1(A_49) = k6_partfun1(A_49) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_18,plain,(
    ! [A_16] :
      ( k5_relat_1(k2_funct_1(A_16),A_16) = k6_relat_1(k2_relat_1(A_16))
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_78,plain,(
    ! [A_16] :
      ( k5_relat_1(k2_funct_1(A_16),A_16) = k6_partfun1(k2_relat_1(A_16))
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_18])).

tff(c_54,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_105,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_96])).

tff(c_114,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_105])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_149,plain,(
    ! [A_69,B_70,C_71] :
      ( k1_relset_1(A_69,B_70,C_71) = k1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_161,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_149])).

tff(c_274,plain,(
    ! [B_89,A_90,C_91] :
      ( k1_xboole_0 = B_89
      | k1_relset_1(A_90,B_89,C_91) = A_90
      | ~ v1_funct_2(C_91,A_90,B_89)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_283,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_274])).

tff(c_292,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_161,c_283])).

tff(c_293,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_292])).

tff(c_341,plain,(
    ! [B_98,C_102,A_99,D_97,F_100,E_101] :
      ( k4_relset_1(A_99,B_98,C_102,D_97,E_101,F_100) = k5_relat_1(E_101,F_100)
      | ~ m1_subset_1(F_100,k1_zfmisc_1(k2_zfmisc_1(C_102,D_97)))
      | ~ m1_subset_1(E_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_372,plain,(
    ! [A_106,B_107,E_108] :
      ( k4_relset_1(A_106,B_107,'#skF_2','#skF_1',E_108,'#skF_4') = k5_relat_1(E_108,'#skF_4')
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(resolution,[status(thm)],[c_66,c_341])).

tff(c_383,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_372])).

tff(c_421,plain,(
    ! [C_115,A_116,F_118,D_119,E_120,B_117] :
      ( m1_subset_1(k4_relset_1(A_116,B_117,C_115,D_119,E_120,F_118),k1_zfmisc_1(k2_zfmisc_1(A_116,D_119)))
      | ~ m1_subset_1(F_118,k1_zfmisc_1(k2_zfmisc_1(C_115,D_119)))
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_472,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_421])).

tff(c_501,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_66,c_472])).

tff(c_48,plain,(
    ! [A_42] : m1_subset_1(k6_partfun1(A_42),k1_zfmisc_1(k2_zfmisc_1(A_42,A_42))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_923,plain,(
    ! [A_137,B_138,C_134,D_135,E_139,F_136] :
      ( k1_partfun1(A_137,B_138,C_134,D_135,E_139,F_136) = k5_relat_1(E_139,F_136)
      | ~ m1_subset_1(F_136,k1_zfmisc_1(k2_zfmisc_1(C_134,D_135)))
      | ~ v1_funct_1(F_136)
      | ~ m1_subset_1(E_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138)))
      | ~ v1_funct_1(E_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_947,plain,(
    ! [A_137,B_138,E_139] :
      ( k1_partfun1(A_137,B_138,'#skF_2','#skF_1',E_139,'#skF_4') = k5_relat_1(E_139,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138)))
      | ~ v1_funct_1(E_139) ) ),
    inference(resolution,[status(thm)],[c_66,c_923])).

tff(c_1001,plain,(
    ! [A_140,B_141,E_142] :
      ( k1_partfun1(A_140,B_141,'#skF_2','#skF_1',E_142,'#skF_4') = k5_relat_1(E_142,'#skF_4')
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141)))
      | ~ v1_funct_1(E_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_947])).

tff(c_1034,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1001])).

tff(c_1050,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1034])).

tff(c_62,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1054,plain,(
    r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_62])).

tff(c_32,plain,(
    ! [D_38,C_37,A_35,B_36] :
      ( D_38 = C_37
      | ~ r2_relset_1(A_35,B_36,C_37,D_38)
      | ~ m1_subset_1(D_38,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1060,plain,
    ( k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1054,c_32])).

tff(c_1063,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_48,c_1060])).

tff(c_8,plain,(
    ! [A_6] :
      ( v1_funct_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_6] :
      ( v1_relat_1(k2_funct_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_160,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_149])).

tff(c_280,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_274])).

tff(c_288,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_160,c_280])).

tff(c_289,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_288])).

tff(c_14,plain,(
    ! [A_15] :
      ( k2_relat_1(k2_funct_1(A_15)) = k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [D_14,B_8,C_12] :
      ( D_14 = B_8
      | k6_relat_1(k2_relat_1(B_8)) != k5_relat_1(C_12,D_14)
      | k6_relat_1(k1_relat_1(D_14)) != k5_relat_1(B_8,C_12)
      | ~ v1_funct_1(D_14)
      | ~ v1_relat_1(D_14)
      | ~ v1_funct_1(C_12)
      | ~ v1_relat_1(C_12)
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_692,plain,(
    ! [D_122,B_123,C_124] :
      ( D_122 = B_123
      | k6_partfun1(k2_relat_1(B_123)) != k5_relat_1(C_124,D_122)
      | k6_partfun1(k1_relat_1(D_122)) != k5_relat_1(B_123,C_124)
      | ~ v1_funct_1(D_122)
      | ~ v1_relat_1(D_122)
      | ~ v1_funct_1(C_124)
      | ~ v1_relat_1(C_124)
      | ~ v1_funct_1(B_123)
      | ~ v1_relat_1(B_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_12])).

tff(c_2613,plain,(
    ! [A_251,D_252,C_253] :
      ( k2_funct_1(A_251) = D_252
      | k6_partfun1(k1_relat_1(A_251)) != k5_relat_1(C_253,D_252)
      | k6_partfun1(k1_relat_1(D_252)) != k5_relat_1(k2_funct_1(A_251),C_253)
      | ~ v1_funct_1(D_252)
      | ~ v1_relat_1(D_252)
      | ~ v1_funct_1(C_253)
      | ~ v1_relat_1(C_253)
      | ~ v1_funct_1(k2_funct_1(A_251))
      | ~ v1_relat_1(k2_funct_1(A_251))
      | ~ v2_funct_1(A_251)
      | ~ v1_funct_1(A_251)
      | ~ v1_relat_1(A_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_692])).

tff(c_2617,plain,(
    ! [D_252,C_253] :
      ( k2_funct_1('#skF_3') = D_252
      | k5_relat_1(C_253,D_252) != k6_partfun1('#skF_1')
      | k6_partfun1(k1_relat_1(D_252)) != k5_relat_1(k2_funct_1('#skF_3'),C_253)
      | ~ v1_funct_1(D_252)
      | ~ v1_relat_1(D_252)
      | ~ v1_funct_1(C_253)
      | ~ v1_relat_1(C_253)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_2613])).

tff(c_2627,plain,(
    ! [D_252,C_253] :
      ( k2_funct_1('#skF_3') = D_252
      | k5_relat_1(C_253,D_252) != k6_partfun1('#skF_1')
      | k6_partfun1(k1_relat_1(D_252)) != k5_relat_1(k2_funct_1('#skF_3'),C_253)
      | ~ v1_funct_1(D_252)
      | ~ v1_relat_1(D_252)
      | ~ v1_funct_1(C_253)
      | ~ v1_relat_1(C_253)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_76,c_60,c_2617])).

tff(c_4492,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2627])).

tff(c_4495,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_4492])).

tff(c_4499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_76,c_60,c_4495])).

tff(c_4500,plain,(
    ! [D_252,C_253] :
      ( ~ v1_funct_1(k2_funct_1('#skF_3'))
      | k2_funct_1('#skF_3') = D_252
      | k5_relat_1(C_253,D_252) != k6_partfun1('#skF_1')
      | k6_partfun1(k1_relat_1(D_252)) != k5_relat_1(k2_funct_1('#skF_3'),C_253)
      | ~ v1_funct_1(D_252)
      | ~ v1_relat_1(D_252)
      | ~ v1_funct_1(C_253)
      | ~ v1_relat_1(C_253) ) ),
    inference(splitRight,[status(thm)],[c_2627])).

tff(c_4515,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4500])).

tff(c_4518,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_4515])).

tff(c_4522,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_76,c_60,c_4518])).

tff(c_4687,plain,(
    ! [D_414,C_415] :
      ( k2_funct_1('#skF_3') = D_414
      | k5_relat_1(C_415,D_414) != k6_partfun1('#skF_1')
      | k6_partfun1(k1_relat_1(D_414)) != k5_relat_1(k2_funct_1('#skF_3'),C_415)
      | ~ v1_funct_1(D_414)
      | ~ v1_relat_1(D_414)
      | ~ v1_funct_1(C_415)
      | ~ v1_relat_1(C_415) ) ),
    inference(splitRight,[status(thm)],[c_4500])).

tff(c_4689,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1(k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1063,c_4687])).

tff(c_4696,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_76,c_114,c_70,c_293,c_4689])).

tff(c_4697,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_4696])).

tff(c_4700,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) != k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_4697])).

tff(c_4703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_76,c_60,c_191,c_4700])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:20:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.74/2.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.74/2.81  
% 7.74/2.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.74/2.81  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.74/2.81  
% 7.74/2.81  %Foreground sorts:
% 7.74/2.81  
% 7.74/2.81  
% 7.74/2.81  %Background operators:
% 7.74/2.81  
% 7.74/2.81  
% 7.74/2.81  %Foreground operators:
% 7.74/2.81  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.74/2.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.74/2.81  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.74/2.81  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.74/2.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.74/2.81  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.74/2.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.74/2.81  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.74/2.81  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.74/2.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.74/2.81  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.74/2.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.74/2.81  tff('#skF_2', type, '#skF_2': $i).
% 7.74/2.81  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.74/2.81  tff('#skF_3', type, '#skF_3': $i).
% 7.74/2.81  tff('#skF_1', type, '#skF_1': $i).
% 7.74/2.81  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.74/2.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.74/2.81  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.74/2.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.74/2.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.74/2.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.74/2.81  tff('#skF_4', type, '#skF_4': $i).
% 7.74/2.81  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.74/2.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.74/2.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.74/2.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.74/2.81  
% 7.74/2.83  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.74/2.83  tff(f_176, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 7.74/2.83  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.74/2.83  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.74/2.83  tff(f_150, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.74/2.83  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 7.74/2.83  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.74/2.83  tff(f_134, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.74/2.83  tff(f_108, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 7.74/2.83  tff(f_94, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 7.74/2.83  tff(f_138, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.74/2.83  tff(f_148, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.74/2.83  tff(f_116, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.74/2.83  tff(f_46, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 7.74/2.83  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 7.74/2.83  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (![D]: ((v1_relat_1(D) & v1_funct_1(D)) => ((((k2_relat_1(B) = A) & (k5_relat_1(B, C) = k6_relat_1(k1_relat_1(D)))) & (k5_relat_1(C, D) = k6_relat_1(A))) => (D = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l72_funct_1)).
% 7.74/2.83  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.74/2.83  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 7.74/2.83  tff(c_96, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.74/2.83  tff(c_102, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_96])).
% 7.74/2.83  tff(c_111, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_102])).
% 7.74/2.83  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 7.74/2.83  tff(c_60, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 7.74/2.83  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_176])).
% 7.74/2.83  tff(c_179, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.74/2.83  tff(c_185, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_179])).
% 7.74/2.83  tff(c_191, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_185])).
% 7.74/2.83  tff(c_52, plain, (![A_49]: (k6_relat_1(A_49)=k6_partfun1(A_49))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.74/2.83  tff(c_18, plain, (![A_16]: (k5_relat_1(k2_funct_1(A_16), A_16)=k6_relat_1(k2_relat_1(A_16)) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.74/2.83  tff(c_78, plain, (![A_16]: (k5_relat_1(k2_funct_1(A_16), A_16)=k6_partfun1(k2_relat_1(A_16)) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_18])).
% 7.74/2.83  tff(c_54, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_176])).
% 7.74/2.83  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 7.74/2.83  tff(c_105, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_66, c_96])).
% 7.74/2.83  tff(c_114, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_105])).
% 7.74/2.83  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_176])).
% 7.74/2.83  tff(c_58, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_176])).
% 7.74/2.83  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_176])).
% 7.74/2.83  tff(c_149, plain, (![A_69, B_70, C_71]: (k1_relset_1(A_69, B_70, C_71)=k1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.74/2.83  tff(c_161, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_149])).
% 7.74/2.83  tff(c_274, plain, (![B_89, A_90, C_91]: (k1_xboole_0=B_89 | k1_relset_1(A_90, B_89, C_91)=A_90 | ~v1_funct_2(C_91, A_90, B_89) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.74/2.83  tff(c_283, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_274])).
% 7.74/2.83  tff(c_292, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_161, c_283])).
% 7.74/2.83  tff(c_293, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_58, c_292])).
% 7.74/2.83  tff(c_341, plain, (![B_98, C_102, A_99, D_97, F_100, E_101]: (k4_relset_1(A_99, B_98, C_102, D_97, E_101, F_100)=k5_relat_1(E_101, F_100) | ~m1_subset_1(F_100, k1_zfmisc_1(k2_zfmisc_1(C_102, D_97))) | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.74/2.83  tff(c_372, plain, (![A_106, B_107, E_108]: (k4_relset_1(A_106, B_107, '#skF_2', '#skF_1', E_108, '#skF_4')=k5_relat_1(E_108, '#skF_4') | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(resolution, [status(thm)], [c_66, c_341])).
% 7.74/2.83  tff(c_383, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_372])).
% 7.74/2.83  tff(c_421, plain, (![C_115, A_116, F_118, D_119, E_120, B_117]: (m1_subset_1(k4_relset_1(A_116, B_117, C_115, D_119, E_120, F_118), k1_zfmisc_1(k2_zfmisc_1(A_116, D_119))) | ~m1_subset_1(F_118, k1_zfmisc_1(k2_zfmisc_1(C_115, D_119))) | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.74/2.83  tff(c_472, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_383, c_421])).
% 7.74/2.83  tff(c_501, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_66, c_472])).
% 7.74/2.83  tff(c_48, plain, (![A_42]: (m1_subset_1(k6_partfun1(A_42), k1_zfmisc_1(k2_zfmisc_1(A_42, A_42))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.74/2.83  tff(c_923, plain, (![A_137, B_138, C_134, D_135, E_139, F_136]: (k1_partfun1(A_137, B_138, C_134, D_135, E_139, F_136)=k5_relat_1(E_139, F_136) | ~m1_subset_1(F_136, k1_zfmisc_1(k2_zfmisc_1(C_134, D_135))) | ~v1_funct_1(F_136) | ~m1_subset_1(E_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))) | ~v1_funct_1(E_139))), inference(cnfTransformation, [status(thm)], [f_148])).
% 7.74/2.83  tff(c_947, plain, (![A_137, B_138, E_139]: (k1_partfun1(A_137, B_138, '#skF_2', '#skF_1', E_139, '#skF_4')=k5_relat_1(E_139, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))) | ~v1_funct_1(E_139))), inference(resolution, [status(thm)], [c_66, c_923])).
% 7.74/2.83  tff(c_1001, plain, (![A_140, B_141, E_142]: (k1_partfun1(A_140, B_141, '#skF_2', '#skF_1', E_142, '#skF_4')=k5_relat_1(E_142, '#skF_4') | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))) | ~v1_funct_1(E_142))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_947])).
% 7.74/2.83  tff(c_1034, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1001])).
% 7.74/2.83  tff(c_1050, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1034])).
% 7.74/2.83  tff(c_62, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 7.74/2.83  tff(c_1054, plain, (r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1050, c_62])).
% 7.74/2.83  tff(c_32, plain, (![D_38, C_37, A_35, B_36]: (D_38=C_37 | ~r2_relset_1(A_35, B_36, C_37, D_38) | ~m1_subset_1(D_38, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.74/2.83  tff(c_1060, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_1054, c_32])).
% 7.74/2.83  tff(c_1063, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_501, c_48, c_1060])).
% 7.74/2.83  tff(c_8, plain, (![A_6]: (v1_funct_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.74/2.83  tff(c_10, plain, (![A_6]: (v1_relat_1(k2_funct_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.74/2.83  tff(c_56, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_176])).
% 7.74/2.83  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 7.74/2.83  tff(c_160, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_149])).
% 7.74/2.83  tff(c_280, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_274])).
% 7.74/2.83  tff(c_288, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_160, c_280])).
% 7.74/2.83  tff(c_289, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_56, c_288])).
% 7.74/2.83  tff(c_14, plain, (![A_15]: (k2_relat_1(k2_funct_1(A_15))=k1_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.74/2.83  tff(c_12, plain, (![D_14, B_8, C_12]: (D_14=B_8 | k6_relat_1(k2_relat_1(B_8))!=k5_relat_1(C_12, D_14) | k6_relat_1(k1_relat_1(D_14))!=k5_relat_1(B_8, C_12) | ~v1_funct_1(D_14) | ~v1_relat_1(D_14) | ~v1_funct_1(C_12) | ~v1_relat_1(C_12) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.74/2.83  tff(c_692, plain, (![D_122, B_123, C_124]: (D_122=B_123 | k6_partfun1(k2_relat_1(B_123))!=k5_relat_1(C_124, D_122) | k6_partfun1(k1_relat_1(D_122))!=k5_relat_1(B_123, C_124) | ~v1_funct_1(D_122) | ~v1_relat_1(D_122) | ~v1_funct_1(C_124) | ~v1_relat_1(C_124) | ~v1_funct_1(B_123) | ~v1_relat_1(B_123))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_12])).
% 7.74/2.83  tff(c_2613, plain, (![A_251, D_252, C_253]: (k2_funct_1(A_251)=D_252 | k6_partfun1(k1_relat_1(A_251))!=k5_relat_1(C_253, D_252) | k6_partfun1(k1_relat_1(D_252))!=k5_relat_1(k2_funct_1(A_251), C_253) | ~v1_funct_1(D_252) | ~v1_relat_1(D_252) | ~v1_funct_1(C_253) | ~v1_relat_1(C_253) | ~v1_funct_1(k2_funct_1(A_251)) | ~v1_relat_1(k2_funct_1(A_251)) | ~v2_funct_1(A_251) | ~v1_funct_1(A_251) | ~v1_relat_1(A_251))), inference(superposition, [status(thm), theory('equality')], [c_14, c_692])).
% 7.74/2.83  tff(c_2617, plain, (![D_252, C_253]: (k2_funct_1('#skF_3')=D_252 | k5_relat_1(C_253, D_252)!=k6_partfun1('#skF_1') | k6_partfun1(k1_relat_1(D_252))!=k5_relat_1(k2_funct_1('#skF_3'), C_253) | ~v1_funct_1(D_252) | ~v1_relat_1(D_252) | ~v1_funct_1(C_253) | ~v1_relat_1(C_253) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_289, c_2613])).
% 7.74/2.83  tff(c_2627, plain, (![D_252, C_253]: (k2_funct_1('#skF_3')=D_252 | k5_relat_1(C_253, D_252)!=k6_partfun1('#skF_1') | k6_partfun1(k1_relat_1(D_252))!=k5_relat_1(k2_funct_1('#skF_3'), C_253) | ~v1_funct_1(D_252) | ~v1_relat_1(D_252) | ~v1_funct_1(C_253) | ~v1_relat_1(C_253) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_76, c_60, c_2617])).
% 7.74/2.83  tff(c_4492, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2627])).
% 7.74/2.83  tff(c_4495, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_4492])).
% 7.74/2.83  tff(c_4499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_76, c_60, c_4495])).
% 7.74/2.83  tff(c_4500, plain, (![D_252, C_253]: (~v1_funct_1(k2_funct_1('#skF_3')) | k2_funct_1('#skF_3')=D_252 | k5_relat_1(C_253, D_252)!=k6_partfun1('#skF_1') | k6_partfun1(k1_relat_1(D_252))!=k5_relat_1(k2_funct_1('#skF_3'), C_253) | ~v1_funct_1(D_252) | ~v1_relat_1(D_252) | ~v1_funct_1(C_253) | ~v1_relat_1(C_253))), inference(splitRight, [status(thm)], [c_2627])).
% 7.74/2.83  tff(c_4515, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_4500])).
% 7.74/2.83  tff(c_4518, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_4515])).
% 7.74/2.83  tff(c_4522, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_76, c_60, c_4518])).
% 7.74/2.83  tff(c_4687, plain, (![D_414, C_415]: (k2_funct_1('#skF_3')=D_414 | k5_relat_1(C_415, D_414)!=k6_partfun1('#skF_1') | k6_partfun1(k1_relat_1(D_414))!=k5_relat_1(k2_funct_1('#skF_3'), C_415) | ~v1_funct_1(D_414) | ~v1_relat_1(D_414) | ~v1_funct_1(C_415) | ~v1_relat_1(C_415))), inference(splitRight, [status(thm)], [c_4500])).
% 7.74/2.83  tff(c_4689, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1(k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1063, c_4687])).
% 7.74/2.83  tff(c_4696, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_76, c_114, c_70, c_293, c_4689])).
% 7.74/2.83  tff(c_4697, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_4696])).
% 7.74/2.83  tff(c_4700, plain, (k6_partfun1(k2_relat_1('#skF_3'))!=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_78, c_4697])).
% 7.74/2.83  tff(c_4703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111, c_76, c_60, c_191, c_4700])).
% 7.74/2.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.74/2.83  
% 7.74/2.83  Inference rules
% 7.74/2.83  ----------------------
% 7.74/2.83  #Ref     : 0
% 7.74/2.83  #Sup     : 1131
% 7.74/2.83  #Fact    : 0
% 7.74/2.83  #Define  : 0
% 7.74/2.83  #Split   : 17
% 7.74/2.83  #Chain   : 0
% 7.74/2.83  #Close   : 0
% 7.74/2.83  
% 7.74/2.83  Ordering : KBO
% 7.74/2.83  
% 7.74/2.83  Simplification rules
% 7.74/2.83  ----------------------
% 7.74/2.83  #Subsume      : 39
% 7.74/2.83  #Demod        : 756
% 7.74/2.83  #Tautology    : 279
% 7.74/2.83  #SimpNegUnit  : 104
% 7.74/2.83  #BackRed      : 21
% 7.74/2.83  
% 7.74/2.83  #Partial instantiations: 0
% 7.74/2.83  #Strategies tried      : 1
% 7.74/2.83  
% 7.74/2.83  Timing (in seconds)
% 7.74/2.83  ----------------------
% 7.74/2.84  Preprocessing        : 0.35
% 7.74/2.84  Parsing              : 0.19
% 8.04/2.84  CNF conversion       : 0.02
% 8.04/2.84  Main loop            : 1.65
% 8.04/2.84  Inferencing          : 0.48
% 8.04/2.84  Reduction            : 0.68
% 8.04/2.84  Demodulation         : 0.52
% 8.04/2.84  BG Simplification    : 0.05
% 8.04/2.84  Subsumption          : 0.32
% 8.04/2.84  Abstraction          : 0.07
% 8.04/2.84  MUC search           : 0.00
% 8.04/2.84  Cooper               : 0.00
% 8.04/2.84  Total                : 2.05
% 8.04/2.84  Index Insertion      : 0.00
% 8.04/2.84  Index Deletion       : 0.00
% 8.04/2.84  Index Matching       : 0.00
% 8.04/2.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
