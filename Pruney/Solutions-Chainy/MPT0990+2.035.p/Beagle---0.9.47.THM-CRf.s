%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:00 EST 2020

% Result     : Theorem 4.12s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 687 expanded)
%              Number of leaves         :   41 ( 263 expanded)
%              Depth                    :   18
%              Number of atoms          :  302 (3003 expanded)
%              Number of equality atoms :  111 (1121 expanded)
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

tff(f_182,negated_conjecture,(
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

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_111,axiom,(
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

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_139,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_73,axiom,(
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

tff(f_127,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_123,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_156,axiom,(
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

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_137,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_46,axiom,(
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

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(c_52,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_97,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_110,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_97])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_109,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_97])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_154,plain,(
    ! [A_62,B_63,C_64] :
      ( k1_relset_1(A_62,B_63,C_64) = k1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_165,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_154])).

tff(c_225,plain,(
    ! [B_74,A_75,C_76] :
      ( k1_xboole_0 = B_74
      | k1_relset_1(A_75,B_74,C_76) = A_75
      | ~ v1_funct_2(C_76,A_75,B_74)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_231,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_225])).

tff(c_239,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_165,c_231])).

tff(c_240,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_239])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_123,plain,(
    ! [A_58,B_59,C_60] :
      ( k2_relset_1(A_58,B_59,C_60) = k2_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_129,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_123])).

tff(c_135,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_129])).

tff(c_48,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_14,plain,(
    ! [A_6,B_8] :
      ( k2_funct_1(A_6) = B_8
      | k6_relat_1(k2_relat_1(A_6)) != k5_relat_1(B_8,A_6)
      | k2_relat_1(B_8) != k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_526,plain,(
    ! [A_125,B_126] :
      ( k2_funct_1(A_125) = B_126
      | k6_partfun1(k2_relat_1(A_125)) != k5_relat_1(B_126,A_125)
      | k2_relat_1(B_126) != k1_relat_1(A_125)
      | ~ v2_funct_1(A_125)
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126)
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_14])).

tff(c_532,plain,(
    ! [B_126] :
      ( k2_funct_1('#skF_3') = B_126
      | k5_relat_1(B_126,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_126) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_526])).

tff(c_537,plain,(
    ! [B_127] :
      ( k2_funct_1('#skF_3') = B_127
      | k5_relat_1(B_127,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_127) != '#skF_1'
      | ~ v1_funct_1(B_127)
      | ~ v1_relat_1(B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_74,c_58,c_240,c_532])).

tff(c_540,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_110,c_537])).

tff(c_549,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_540])).

tff(c_550,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_549])).

tff(c_555,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_550])).

tff(c_66,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_44,plain,(
    ! [A_31] : m1_subset_1(k6_partfun1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_111,plain,(
    ! [A_53,B_54,D_55] :
      ( r2_relset_1(A_53,B_54,D_55,D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_118,plain,(
    ! [A_31] : r2_relset_1(A_31,A_31,k6_partfun1(A_31),k6_partfun1(A_31)) ),
    inference(resolution,[status(thm)],[c_44,c_111])).

tff(c_136,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_123])).

tff(c_459,plain,(
    ! [C_121,D_119,A_120,E_124,F_122,B_123] :
      ( m1_subset_1(k1_partfun1(A_120,B_123,C_121,D_119,E_124,F_122),k1_zfmisc_1(k2_zfmisc_1(A_120,D_119)))
      | ~ m1_subset_1(F_122,k1_zfmisc_1(k2_zfmisc_1(C_121,D_119)))
      | ~ v1_funct_1(F_122)
      | ~ m1_subset_1(E_124,k1_zfmisc_1(k2_zfmisc_1(A_120,B_123)))
      | ~ v1_funct_1(E_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_314,plain,(
    ! [D_86,C_87,A_88,B_89] :
      ( D_86 = C_87
      | ~ r2_relset_1(A_88,B_89,C_87,D_86)
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_322,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_314])).

tff(c_337,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_322])).

tff(c_340,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_337])).

tff(c_475,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_459,c_340])).

tff(c_516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_475])).

tff(c_517,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_337])).

tff(c_881,plain,(
    ! [A_159,B_160,C_161,D_162] :
      ( k2_relset_1(A_159,B_160,C_161) = B_160
      | ~ r2_relset_1(B_160,B_160,k1_partfun1(B_160,A_159,A_159,B_160,D_162,C_161),k6_partfun1(B_160))
      | ~ m1_subset_1(D_162,k1_zfmisc_1(k2_zfmisc_1(B_160,A_159)))
      | ~ v1_funct_2(D_162,B_160,A_159)
      | ~ v1_funct_1(D_162)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160)))
      | ~ v1_funct_2(C_161,A_159,B_160)
      | ~ v1_funct_1(C_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_884,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_881])).

tff(c_886,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_74,c_72,c_70,c_118,c_136,c_884])).

tff(c_888,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_555,c_886])).

tff(c_889,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_550])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_166,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_154])).

tff(c_234,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_225])).

tff(c_243,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_166,c_234])).

tff(c_244,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_243])).

tff(c_890,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_550])).

tff(c_75,plain,(
    ! [A_6,B_8] :
      ( k2_funct_1(A_6) = B_8
      | k6_partfun1(k2_relat_1(A_6)) != k5_relat_1(B_8,A_6)
      | k2_relat_1(B_8) != k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_14])).

tff(c_894,plain,(
    ! [B_8] :
      ( k2_funct_1('#skF_4') = B_8
      | k5_relat_1(B_8,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_8) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_890,c_75])).

tff(c_898,plain,(
    ! [B_8] :
      ( k2_funct_1('#skF_4') = B_8
      | k5_relat_1(B_8,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_8) != '#skF_2'
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_68,c_244,c_894])).

tff(c_906,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_898])).

tff(c_4,plain,(
    ! [A_1] : v2_funct_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    ! [A_1] : v2_funct_1(k6_partfun1(A_1)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4])).

tff(c_921,plain,(
    ! [A_174,E_170,C_173,D_175,B_171,F_172] :
      ( k1_partfun1(A_174,B_171,C_173,D_175,E_170,F_172) = k5_relat_1(E_170,F_172)
      | ~ m1_subset_1(F_172,k1_zfmisc_1(k2_zfmisc_1(C_173,D_175)))
      | ~ v1_funct_1(F_172)
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(A_174,B_171)))
      | ~ v1_funct_1(E_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_927,plain,(
    ! [A_174,B_171,E_170] :
      ( k1_partfun1(A_174,B_171,'#skF_2','#skF_1',E_170,'#skF_4') = k5_relat_1(E_170,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_170,k1_zfmisc_1(k2_zfmisc_1(A_174,B_171)))
      | ~ v1_funct_1(E_170) ) ),
    inference(resolution,[status(thm)],[c_64,c_921])).

tff(c_1233,plain,(
    ! [A_197,B_198,E_199] :
      ( k1_partfun1(A_197,B_198,'#skF_2','#skF_1',E_199,'#skF_4') = k5_relat_1(E_199,'#skF_4')
      | ~ m1_subset_1(E_199,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198)))
      | ~ v1_funct_1(E_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_927])).

tff(c_1248,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1233])).

tff(c_1262,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_517,c_1248])).

tff(c_6,plain,(
    ! [A_2,B_4] :
      ( v2_funct_1(A_2)
      | k2_relat_1(B_4) != k1_relat_1(A_2)
      | ~ v2_funct_1(k5_relat_1(B_4,A_2))
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1272,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1262,c_6])).

tff(c_1278,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_68,c_109,c_74,c_78,c_135,c_244,c_1272])).

tff(c_1280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_906,c_1278])).

tff(c_1282,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_898])).

tff(c_1283,plain,(
    ! [B_200] :
      ( k2_funct_1('#skF_4') = B_200
      | k5_relat_1(B_200,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_200) != '#skF_2'
      | ~ v1_funct_1(B_200)
      | ~ v1_relat_1(B_200) ) ),
    inference(splitRight,[status(thm)],[c_898])).

tff(c_1289,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_109,c_1283])).

tff(c_1298,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_135,c_1289])).

tff(c_1300,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1298])).

tff(c_1333,plain,(
    ! [B_212,E_211,D_216,F_213,A_215,C_214] :
      ( k1_partfun1(A_215,B_212,C_214,D_216,E_211,F_213) = k5_relat_1(E_211,F_213)
      | ~ m1_subset_1(F_213,k1_zfmisc_1(k2_zfmisc_1(C_214,D_216)))
      | ~ v1_funct_1(F_213)
      | ~ m1_subset_1(E_211,k1_zfmisc_1(k2_zfmisc_1(A_215,B_212)))
      | ~ v1_funct_1(E_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1339,plain,(
    ! [A_215,B_212,E_211] :
      ( k1_partfun1(A_215,B_212,'#skF_2','#skF_1',E_211,'#skF_4') = k5_relat_1(E_211,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_211,k1_zfmisc_1(k2_zfmisc_1(A_215,B_212)))
      | ~ v1_funct_1(E_211) ) ),
    inference(resolution,[status(thm)],[c_64,c_1333])).

tff(c_1641,plain,(
    ! [A_235,B_236,E_237] :
      ( k1_partfun1(A_235,B_236,'#skF_2','#skF_1',E_237,'#skF_4') = k5_relat_1(E_237,'#skF_4')
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236)))
      | ~ v1_funct_1(E_237) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1339])).

tff(c_1656,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1641])).

tff(c_1670,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_517,c_1656])).

tff(c_1672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1300,c_1670])).

tff(c_1673,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1298])).

tff(c_12,plain,(
    ! [A_5] :
      ( k5_relat_1(A_5,k2_funct_1(A_5)) = k6_relat_1(k1_relat_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_76,plain,(
    ! [A_5] :
      ( k5_relat_1(A_5,k2_funct_1(A_5)) = k6_partfun1(k1_relat_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_12])).

tff(c_1685,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k5_relat_1('#skF_4','#skF_3')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1673,c_76])).

tff(c_1696,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_68,c_1282,c_244,c_1685])).

tff(c_1698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_889,c_1696])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:42:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.12/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.77  
% 4.12/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.77  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.12/1.77  
% 4.12/1.77  %Foreground sorts:
% 4.12/1.77  
% 4.12/1.77  
% 4.12/1.77  %Background operators:
% 4.12/1.77  
% 4.12/1.77  
% 4.12/1.77  %Foreground operators:
% 4.12/1.77  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.12/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.12/1.77  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.12/1.77  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.12/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.12/1.77  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.12/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.12/1.77  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.12/1.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.12/1.77  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.12/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.12/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.12/1.77  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.12/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.12/1.77  tff('#skF_1', type, '#skF_1': $i).
% 4.12/1.77  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.12/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.12/1.77  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.12/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.12/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.12/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.12/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.12/1.77  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.12/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.12/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.12/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.12/1.77  
% 4.51/1.79  tff(f_182, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 4.51/1.79  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.51/1.79  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.51/1.79  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.51/1.79  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.51/1.79  tff(f_139, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.51/1.79  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 4.51/1.79  tff(f_127, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.51/1.79  tff(f_93, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.51/1.79  tff(f_123, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.51/1.79  tff(f_156, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.51/1.79  tff(f_29, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.51/1.79  tff(f_137, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.51/1.79  tff(f_46, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 4.51/1.79  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 4.51/1.79  tff(c_52, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_182])).
% 4.51/1.79  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_182])).
% 4.51/1.79  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 4.51/1.79  tff(c_97, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.51/1.79  tff(c_110, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_97])).
% 4.51/1.79  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 4.51/1.79  tff(c_109, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_97])).
% 4.51/1.79  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 4.51/1.79  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 4.51/1.79  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_182])).
% 4.51/1.79  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 4.51/1.79  tff(c_154, plain, (![A_62, B_63, C_64]: (k1_relset_1(A_62, B_63, C_64)=k1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.51/1.79  tff(c_165, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_154])).
% 4.51/1.79  tff(c_225, plain, (![B_74, A_75, C_76]: (k1_xboole_0=B_74 | k1_relset_1(A_75, B_74, C_76)=A_75 | ~v1_funct_2(C_76, A_75, B_74) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.51/1.79  tff(c_231, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_225])).
% 4.51/1.79  tff(c_239, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_165, c_231])).
% 4.51/1.79  tff(c_240, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_54, c_239])).
% 4.51/1.79  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_182])).
% 4.51/1.79  tff(c_123, plain, (![A_58, B_59, C_60]: (k2_relset_1(A_58, B_59, C_60)=k2_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.51/1.79  tff(c_129, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_123])).
% 4.51/1.79  tff(c_135, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_129])).
% 4.51/1.79  tff(c_48, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.51/1.79  tff(c_14, plain, (![A_6, B_8]: (k2_funct_1(A_6)=B_8 | k6_relat_1(k2_relat_1(A_6))!=k5_relat_1(B_8, A_6) | k2_relat_1(B_8)!=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.51/1.79  tff(c_526, plain, (![A_125, B_126]: (k2_funct_1(A_125)=B_126 | k6_partfun1(k2_relat_1(A_125))!=k5_relat_1(B_126, A_125) | k2_relat_1(B_126)!=k1_relat_1(A_125) | ~v2_funct_1(A_125) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_14])).
% 4.51/1.79  tff(c_532, plain, (![B_126]: (k2_funct_1('#skF_3')=B_126 | k5_relat_1(B_126, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_126)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_126) | ~v1_relat_1(B_126) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_526])).
% 4.51/1.79  tff(c_537, plain, (![B_127]: (k2_funct_1('#skF_3')=B_127 | k5_relat_1(B_127, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_127)!='#skF_1' | ~v1_funct_1(B_127) | ~v1_relat_1(B_127))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_74, c_58, c_240, c_532])).
% 4.51/1.79  tff(c_540, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_110, c_537])).
% 4.51/1.79  tff(c_549, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_540])).
% 4.51/1.79  tff(c_550, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_52, c_549])).
% 4.51/1.79  tff(c_555, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_550])).
% 4.51/1.79  tff(c_66, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 4.51/1.79  tff(c_44, plain, (![A_31]: (m1_subset_1(k6_partfun1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.51/1.79  tff(c_111, plain, (![A_53, B_54, D_55]: (r2_relset_1(A_53, B_54, D_55, D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.51/1.79  tff(c_118, plain, (![A_31]: (r2_relset_1(A_31, A_31, k6_partfun1(A_31), k6_partfun1(A_31)))), inference(resolution, [status(thm)], [c_44, c_111])).
% 4.51/1.79  tff(c_136, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_123])).
% 4.51/1.79  tff(c_459, plain, (![C_121, D_119, A_120, E_124, F_122, B_123]: (m1_subset_1(k1_partfun1(A_120, B_123, C_121, D_119, E_124, F_122), k1_zfmisc_1(k2_zfmisc_1(A_120, D_119))) | ~m1_subset_1(F_122, k1_zfmisc_1(k2_zfmisc_1(C_121, D_119))) | ~v1_funct_1(F_122) | ~m1_subset_1(E_124, k1_zfmisc_1(k2_zfmisc_1(A_120, B_123))) | ~v1_funct_1(E_124))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.51/1.79  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 4.51/1.79  tff(c_314, plain, (![D_86, C_87, A_88, B_89]: (D_86=C_87 | ~r2_relset_1(A_88, B_89, C_87, D_86) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.51/1.79  tff(c_322, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_314])).
% 4.51/1.79  tff(c_337, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_322])).
% 4.51/1.79  tff(c_340, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_337])).
% 4.51/1.79  tff(c_475, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_459, c_340])).
% 4.51/1.79  tff(c_516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_475])).
% 4.51/1.79  tff(c_517, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_337])).
% 4.51/1.79  tff(c_881, plain, (![A_159, B_160, C_161, D_162]: (k2_relset_1(A_159, B_160, C_161)=B_160 | ~r2_relset_1(B_160, B_160, k1_partfun1(B_160, A_159, A_159, B_160, D_162, C_161), k6_partfun1(B_160)) | ~m1_subset_1(D_162, k1_zfmisc_1(k2_zfmisc_1(B_160, A_159))) | ~v1_funct_2(D_162, B_160, A_159) | ~v1_funct_1(D_162) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))) | ~v1_funct_2(C_161, A_159, B_160) | ~v1_funct_1(C_161))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.51/1.79  tff(c_884, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_517, c_881])).
% 4.51/1.79  tff(c_886, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_74, c_72, c_70, c_118, c_136, c_884])).
% 4.51/1.79  tff(c_888, plain, $false, inference(negUnitSimplification, [status(thm)], [c_555, c_886])).
% 4.51/1.79  tff(c_889, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_550])).
% 4.51/1.79  tff(c_56, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_182])).
% 4.51/1.79  tff(c_166, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_154])).
% 4.51/1.79  tff(c_234, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_225])).
% 4.51/1.79  tff(c_243, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_166, c_234])).
% 4.51/1.79  tff(c_244, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_56, c_243])).
% 4.51/1.79  tff(c_890, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_550])).
% 4.51/1.79  tff(c_75, plain, (![A_6, B_8]: (k2_funct_1(A_6)=B_8 | k6_partfun1(k2_relat_1(A_6))!=k5_relat_1(B_8, A_6) | k2_relat_1(B_8)!=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_14])).
% 4.51/1.79  tff(c_894, plain, (![B_8]: (k2_funct_1('#skF_4')=B_8 | k5_relat_1(B_8, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_8)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_8) | ~v1_relat_1(B_8) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_890, c_75])).
% 4.51/1.79  tff(c_898, plain, (![B_8]: (k2_funct_1('#skF_4')=B_8 | k5_relat_1(B_8, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_8)!='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_8) | ~v1_relat_1(B_8))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_68, c_244, c_894])).
% 4.51/1.79  tff(c_906, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_898])).
% 4.51/1.79  tff(c_4, plain, (![A_1]: (v2_funct_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.51/1.79  tff(c_78, plain, (![A_1]: (v2_funct_1(k6_partfun1(A_1)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4])).
% 4.51/1.79  tff(c_921, plain, (![A_174, E_170, C_173, D_175, B_171, F_172]: (k1_partfun1(A_174, B_171, C_173, D_175, E_170, F_172)=k5_relat_1(E_170, F_172) | ~m1_subset_1(F_172, k1_zfmisc_1(k2_zfmisc_1(C_173, D_175))) | ~v1_funct_1(F_172) | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(A_174, B_171))) | ~v1_funct_1(E_170))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.51/1.79  tff(c_927, plain, (![A_174, B_171, E_170]: (k1_partfun1(A_174, B_171, '#skF_2', '#skF_1', E_170, '#skF_4')=k5_relat_1(E_170, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_170, k1_zfmisc_1(k2_zfmisc_1(A_174, B_171))) | ~v1_funct_1(E_170))), inference(resolution, [status(thm)], [c_64, c_921])).
% 4.51/1.79  tff(c_1233, plain, (![A_197, B_198, E_199]: (k1_partfun1(A_197, B_198, '#skF_2', '#skF_1', E_199, '#skF_4')=k5_relat_1(E_199, '#skF_4') | ~m1_subset_1(E_199, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))) | ~v1_funct_1(E_199))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_927])).
% 4.51/1.79  tff(c_1248, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_1233])).
% 4.51/1.79  tff(c_1262, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_517, c_1248])).
% 4.51/1.79  tff(c_6, plain, (![A_2, B_4]: (v2_funct_1(A_2) | k2_relat_1(B_4)!=k1_relat_1(A_2) | ~v2_funct_1(k5_relat_1(B_4, A_2)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.51/1.79  tff(c_1272, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1262, c_6])).
% 4.51/1.79  tff(c_1278, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_68, c_109, c_74, c_78, c_135, c_244, c_1272])).
% 4.51/1.79  tff(c_1280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_906, c_1278])).
% 4.51/1.79  tff(c_1282, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_898])).
% 4.51/1.79  tff(c_1283, plain, (![B_200]: (k2_funct_1('#skF_4')=B_200 | k5_relat_1(B_200, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_200)!='#skF_2' | ~v1_funct_1(B_200) | ~v1_relat_1(B_200))), inference(splitRight, [status(thm)], [c_898])).
% 4.51/1.79  tff(c_1289, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_109, c_1283])).
% 4.51/1.79  tff(c_1298, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_135, c_1289])).
% 4.51/1.79  tff(c_1300, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_1298])).
% 4.51/1.79  tff(c_1333, plain, (![B_212, E_211, D_216, F_213, A_215, C_214]: (k1_partfun1(A_215, B_212, C_214, D_216, E_211, F_213)=k5_relat_1(E_211, F_213) | ~m1_subset_1(F_213, k1_zfmisc_1(k2_zfmisc_1(C_214, D_216))) | ~v1_funct_1(F_213) | ~m1_subset_1(E_211, k1_zfmisc_1(k2_zfmisc_1(A_215, B_212))) | ~v1_funct_1(E_211))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.51/1.79  tff(c_1339, plain, (![A_215, B_212, E_211]: (k1_partfun1(A_215, B_212, '#skF_2', '#skF_1', E_211, '#skF_4')=k5_relat_1(E_211, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_211, k1_zfmisc_1(k2_zfmisc_1(A_215, B_212))) | ~v1_funct_1(E_211))), inference(resolution, [status(thm)], [c_64, c_1333])).
% 4.51/1.79  tff(c_1641, plain, (![A_235, B_236, E_237]: (k1_partfun1(A_235, B_236, '#skF_2', '#skF_1', E_237, '#skF_4')=k5_relat_1(E_237, '#skF_4') | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))) | ~v1_funct_1(E_237))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1339])).
% 4.51/1.79  tff(c_1656, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_1641])).
% 4.51/1.79  tff(c_1670, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_517, c_1656])).
% 4.51/1.79  tff(c_1672, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1300, c_1670])).
% 4.51/1.79  tff(c_1673, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1298])).
% 4.51/1.79  tff(c_12, plain, (![A_5]: (k5_relat_1(A_5, k2_funct_1(A_5))=k6_relat_1(k1_relat_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.51/1.79  tff(c_76, plain, (![A_5]: (k5_relat_1(A_5, k2_funct_1(A_5))=k6_partfun1(k1_relat_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_12])).
% 4.51/1.79  tff(c_1685, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k5_relat_1('#skF_4', '#skF_3') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1673, c_76])).
% 4.51/1.79  tff(c_1696, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_68, c_1282, c_244, c_1685])).
% 4.51/1.79  tff(c_1698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_889, c_1696])).
% 4.51/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.79  
% 4.51/1.79  Inference rules
% 4.51/1.79  ----------------------
% 4.51/1.79  #Ref     : 0
% 4.51/1.79  #Sup     : 350
% 4.51/1.79  #Fact    : 0
% 4.51/1.79  #Define  : 0
% 4.51/1.79  #Split   : 16
% 4.51/1.79  #Chain   : 0
% 4.51/1.79  #Close   : 0
% 4.51/1.79  
% 4.51/1.79  Ordering : KBO
% 4.51/1.79  
% 4.51/1.79  Simplification rules
% 4.51/1.79  ----------------------
% 4.51/1.79  #Subsume      : 2
% 4.51/1.79  #Demod        : 295
% 4.51/1.79  #Tautology    : 94
% 4.51/1.79  #SimpNegUnit  : 23
% 4.51/1.79  #BackRed      : 11
% 4.51/1.79  
% 4.51/1.79  #Partial instantiations: 0
% 4.51/1.79  #Strategies tried      : 1
% 4.51/1.79  
% 4.51/1.79  Timing (in seconds)
% 4.51/1.79  ----------------------
% 4.51/1.80  Preprocessing        : 0.37
% 4.51/1.80  Parsing              : 0.20
% 4.51/1.80  CNF conversion       : 0.03
% 4.51/1.80  Main loop            : 0.62
% 4.51/1.80  Inferencing          : 0.22
% 4.51/1.80  Reduction            : 0.21
% 4.51/1.80  Demodulation         : 0.14
% 4.51/1.80  BG Simplification    : 0.03
% 4.51/1.80  Subsumption          : 0.11
% 4.51/1.80  Abstraction          : 0.03
% 4.51/1.80  MUC search           : 0.00
% 4.51/1.80  Cooper               : 0.00
% 4.51/1.80  Total                : 1.04
% 4.51/1.80  Index Insertion      : 0.00
% 4.51/1.80  Index Deletion       : 0.00
% 4.51/1.80  Index Matching       : 0.00
% 4.51/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
