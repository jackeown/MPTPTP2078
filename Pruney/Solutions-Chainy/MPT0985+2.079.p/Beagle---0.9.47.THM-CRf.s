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
% DateTime   : Thu Dec  3 10:12:38 EST 2020

% Result     : Theorem 12.13s
% Output     : CNFRefutation 12.50s
% Verified   : 
% Statistics : Number of formulae       :  325 (3044 expanded)
%              Number of leaves         :   44 ( 945 expanded)
%              Depth                    :   15
%              Number of atoms          :  565 (8014 expanded)
%              Number of equality atoms :  194 (2967 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_115,axiom,(
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

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_131,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_119,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_121,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_84,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_192,plain,(
    ! [A_50] :
      ( v1_funct_1(k2_funct_1(A_50))
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_74,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_178,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_195,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_192,c_178])).

tff(c_198,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_195])).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_204,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_214,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_204])).

tff(c_228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_214])).

tff(c_229,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_300,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_322,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_343,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_322])).

tff(c_78,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_82,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_879,plain,(
    ! [A_134,B_135,C_136] :
      ( k1_relset_1(A_134,B_135,C_136) = k1_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_903,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_879])).

tff(c_5431,plain,(
    ! [B_412,A_413,C_414] :
      ( k1_xboole_0 = B_412
      | k1_relset_1(A_413,B_412,C_414) = A_413
      | ~ v1_funct_2(C_414,A_413,B_412)
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(A_413,B_412))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_5447,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_5431])).

tff(c_5464,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_903,c_5447])).

tff(c_5468,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5464])).

tff(c_1452,plain,(
    ! [B_194,A_195,C_196] :
      ( k1_xboole_0 = B_194
      | k1_relset_1(A_195,B_194,C_196) = A_195
      | ~ v1_funct_2(C_196,A_195,B_194)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_195,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1468,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_1452])).

tff(c_1488,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_903,c_1468])).

tff(c_1492,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1488])).

tff(c_36,plain,(
    ! [A_16] :
      ( k2_relat_1(k2_funct_1(A_16)) = k1_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_34,plain,(
    ! [A_15] :
      ( v1_relat_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_76,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_983,plain,(
    ! [A_153,B_154,C_155] :
      ( k2_relset_1(A_153,B_154,C_155) = k2_relat_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_993,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_983])).

tff(c_1008,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_993])).

tff(c_808,plain,(
    ! [A_130] :
      ( k1_relat_1(k2_funct_1(A_130)) = k2_relat_1(A_130)
      | ~ v2_funct_1(A_130)
      | ~ v1_funct_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_521,plain,(
    ! [B_93,A_94] :
      ( v4_relat_1(B_93,A_94)
      | ~ r1_tarski(k1_relat_1(B_93),A_94)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_540,plain,(
    ! [B_93] :
      ( v4_relat_1(B_93,k1_relat_1(B_93))
      | ~ v1_relat_1(B_93) ) ),
    inference(resolution,[status(thm)],[c_6,c_521])).

tff(c_3495,plain,(
    ! [A_324] :
      ( v4_relat_1(k2_funct_1(A_324),k2_relat_1(A_324))
      | ~ v1_relat_1(k2_funct_1(A_324))
      | ~ v2_funct_1(A_324)
      | ~ v1_funct_1(A_324)
      | ~ v1_relat_1(A_324) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_808,c_540])).

tff(c_3501,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1008,c_3495])).

tff(c_3514,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_84,c_78,c_3501])).

tff(c_3519,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3514])).

tff(c_3522,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_3519])).

tff(c_3526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_84,c_3522])).

tff(c_3528,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3514])).

tff(c_230,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_38,plain,(
    ! [A_16] :
      ( k1_relat_1(k2_funct_1(A_16)) = k2_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1055,plain,(
    ! [A_161] :
      ( m1_subset_1(A_161,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_161),k2_relat_1(A_161))))
      | ~ v1_funct_1(A_161)
      | ~ v1_relat_1(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4784,plain,(
    ! [A_392] :
      ( m1_subset_1(k2_funct_1(A_392),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_392),k2_relat_1(k2_funct_1(A_392)))))
      | ~ v1_funct_1(k2_funct_1(A_392))
      | ~ v1_relat_1(k2_funct_1(A_392))
      | ~ v2_funct_1(A_392)
      | ~ v1_funct_1(A_392)
      | ~ v1_relat_1(A_392) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1055])).

tff(c_4813,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1008,c_4784])).

tff(c_4836,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_84,c_78,c_3528,c_230,c_4813])).

tff(c_4920,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_4836])).

tff(c_4937,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_84,c_78,c_1492,c_4920])).

tff(c_4939,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_4937])).

tff(c_4940,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1488])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4985,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4940,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4982,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4940,c_4940,c_12])).

tff(c_1078,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1008,c_1055])).

tff(c_1105,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_84,c_1078])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1143,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_1105,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1165,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1143,c_2])).

tff(c_1292,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1165])).

tff(c_5289,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4982,c_1292])).

tff(c_5299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4985,c_5289])).

tff(c_5300,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1165])).

tff(c_5469,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5468,c_5300])).

tff(c_151,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_158,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_80,c_151])).

tff(c_250,plain,(
    ! [B_61,A_62] :
      ( B_61 = A_62
      | ~ r1_tarski(B_61,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_265,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_158,c_250])).

tff(c_349,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_5513,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5469,c_349])).

tff(c_5518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5513])).

tff(c_5519,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5464])).

tff(c_5563,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5519,c_8])).

tff(c_5560,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5519,c_5519,c_12])).

tff(c_5800,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5560,c_349])).

tff(c_5805,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5563,c_5800])).

tff(c_5806,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_5809,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5806,c_80])).

tff(c_6563,plain,(
    ! [A_511,B_512,C_513] :
      ( k1_relset_1(A_511,B_512,C_513) = k1_relat_1(C_513)
      | ~ m1_subset_1(C_513,k1_zfmisc_1(k2_zfmisc_1(A_511,B_512))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6741,plain,(
    ! [C_536] :
      ( k1_relset_1('#skF_1','#skF_2',C_536) = k1_relat_1(C_536)
      | ~ m1_subset_1(C_536,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5806,c_6563])).

tff(c_6753,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5809,c_6741])).

tff(c_7660,plain,(
    ! [B_603,A_604,C_605] :
      ( k1_xboole_0 = B_603
      | k1_relset_1(A_604,B_603,C_605) = A_604
      | ~ v1_funct_2(C_605,A_604,B_603)
      | ~ m1_subset_1(C_605,k1_zfmisc_1(k2_zfmisc_1(A_604,B_603))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_7669,plain,(
    ! [C_605] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_605) = '#skF_1'
      | ~ v1_funct_2(C_605,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_605,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5806,c_7660])).

tff(c_7756,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7669])).

tff(c_5865,plain,(
    ! [B_426,A_427] :
      ( k1_xboole_0 = B_426
      | k1_xboole_0 = A_427
      | k2_zfmisc_1(A_427,B_426) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5868,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_5806,c_5865])).

tff(c_5892,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5868])).

tff(c_7801,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7756,c_5892])).

tff(c_8135,plain,(
    ! [A_619] : k2_zfmisc_1(A_619,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7756,c_7756,c_12])).

tff(c_8211,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_8135,c_5806])).

tff(c_8239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7801,c_8211])).

tff(c_8689,plain,(
    ! [C_652] :
      ( k1_relset_1('#skF_1','#skF_2',C_652) = '#skF_1'
      | ~ v1_funct_2(C_652,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_652,k1_zfmisc_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_7669])).

tff(c_8692,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_5809,c_8689])).

tff(c_8703,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_6753,c_8692])).

tff(c_6681,plain,(
    ! [A_529,B_530,C_531] :
      ( k2_relset_1(A_529,B_530,C_531) = k2_relat_1(C_531)
      | ~ m1_subset_1(C_531,k1_zfmisc_1(k2_zfmisc_1(A_529,B_530))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6918,plain,(
    ! [C_549] :
      ( k2_relset_1('#skF_1','#skF_2',C_549) = k2_relat_1(C_549)
      | ~ m1_subset_1(C_549,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5806,c_6681])).

tff(c_6921,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5809,c_6918])).

tff(c_6931,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6921])).

tff(c_6142,plain,(
    ! [B_469,A_470] :
      ( r1_tarski(k1_relat_1(B_469),A_470)
      | ~ v4_relat_1(B_469,A_470)
      | ~ v1_relat_1(B_469) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5893,plain,(
    ! [C_429,B_430,A_431] :
      ( v5_relat_1(C_429,B_430)
      | ~ m1_subset_1(C_429,k1_zfmisc_1(k2_zfmisc_1(A_431,B_430))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5914,plain,(
    ! [A_7,B_430,A_431] :
      ( v5_relat_1(A_7,B_430)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_431,B_430)) ) ),
    inference(resolution,[status(thm)],[c_20,c_5893])).

tff(c_6528,plain,(
    ! [B_508,B_509,A_510] :
      ( v5_relat_1(k1_relat_1(B_508),B_509)
      | ~ v4_relat_1(B_508,k2_zfmisc_1(A_510,B_509))
      | ~ v1_relat_1(B_508) ) ),
    inference(resolution,[status(thm)],[c_6142,c_5914])).

tff(c_6727,plain,(
    ! [B_535] :
      ( v5_relat_1(k1_relat_1(B_535),'#skF_2')
      | ~ v4_relat_1(B_535,'#skF_3')
      | ~ v1_relat_1(B_535) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5806,c_6528])).

tff(c_7041,plain,(
    ! [A_553] :
      ( v5_relat_1(k2_relat_1(A_553),'#skF_2')
      | ~ v4_relat_1(k2_funct_1(A_553),'#skF_3')
      | ~ v1_relat_1(k2_funct_1(A_553))
      | ~ v2_funct_1(A_553)
      | ~ v1_funct_1(A_553)
      | ~ v1_relat_1(A_553) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_6727])).

tff(c_7044,plain,
    ( v5_relat_1('#skF_2','#skF_2')
    | ~ v4_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6931,c_7041])).

tff(c_7055,plain,
    ( v5_relat_1('#skF_2','#skF_2')
    | ~ v4_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_84,c_78,c_7044])).

tff(c_7130,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7055])).

tff(c_7133,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_7130])).

tff(c_7137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_84,c_7133])).

tff(c_7139,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7055])).

tff(c_6825,plain,(
    ! [A_543] :
      ( m1_subset_1(A_543,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_543),k2_relat_1(A_543))))
      | ~ v1_funct_1(A_543)
      | ~ v1_relat_1(A_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_10765,plain,(
    ! [A_727] :
      ( m1_subset_1(k2_funct_1(A_727),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_727),k2_relat_1(k2_funct_1(A_727)))))
      | ~ v1_funct_1(k2_funct_1(A_727))
      | ~ v1_relat_1(k2_funct_1(A_727))
      | ~ v2_funct_1(A_727)
      | ~ v1_funct_1(A_727)
      | ~ v1_relat_1(A_727) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_6825])).

tff(c_10794,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6931,c_10765])).

tff(c_10817,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_84,c_78,c_7139,c_230,c_10794])).

tff(c_10850,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_10817])).

tff(c_10865,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_84,c_78,c_8703,c_10850])).

tff(c_10867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_10865])).

tff(c_10869,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5868])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10881,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10869,c_10869,c_14])).

tff(c_10868,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5868])).

tff(c_10911,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10869,c_10869,c_10868])).

tff(c_10912,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_10911])).

tff(c_10915,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10912,c_300])).

tff(c_11145,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10881,c_10915])).

tff(c_161,plain,(
    ! [A_47] : m1_subset_1(k6_partfun1(A_47),k1_zfmisc_1(k2_zfmisc_1(A_47,A_47))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_168,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_161])).

tff(c_177,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_168,c_18])).

tff(c_254,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_177,c_250])).

tff(c_264,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_254])).

tff(c_10878,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10869,c_10869,c_264])).

tff(c_66,plain,(
    ! [A_33] : k6_relat_1(A_33) = k6_partfun1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_30,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_85,plain,(
    ! [A_14] : k2_relat_1(k6_partfun1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_30])).

tff(c_10900,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_10878,c_85])).

tff(c_11388,plain,(
    ! [A_788] :
      ( k1_relat_1(k2_funct_1(A_788)) = k2_relat_1(A_788)
      | ~ v2_funct_1(A_788)
      | ~ v1_funct_1(A_788)
      | ~ v1_relat_1(A_788) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_70,plain,(
    ! [A_34] :
      ( v1_funct_2(A_34,k1_relat_1(A_34),k2_relat_1(A_34))
      | ~ v1_funct_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_13481,plain,(
    ! [A_959] :
      ( v1_funct_2(k2_funct_1(A_959),k2_relat_1(A_959),k2_relat_1(k2_funct_1(A_959)))
      | ~ v1_funct_1(k2_funct_1(A_959))
      | ~ v1_relat_1(k2_funct_1(A_959))
      | ~ v2_funct_1(A_959)
      | ~ v1_funct_1(A_959)
      | ~ v1_relat_1(A_959) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11388,c_70])).

tff(c_13490,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10900,c_13481])).

tff(c_13495,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_84,c_78,c_230,c_13490])).

tff(c_13498,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_13495])).

tff(c_13501,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_13498])).

tff(c_13505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_84,c_13501])).

tff(c_13507,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_13495])).

tff(c_11800,plain,(
    ! [A_841] :
      ( m1_subset_1(A_841,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_841),k2_relat_1(A_841))))
      | ~ v1_funct_1(A_841)
      | ~ v1_relat_1(A_841) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_13826,plain,(
    ! [A_983] :
      ( m1_subset_1(k2_funct_1(A_983),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_983),k2_relat_1(k2_funct_1(A_983)))))
      | ~ v1_funct_1(k2_funct_1(A_983))
      | ~ v1_relat_1(k2_funct_1(A_983))
      | ~ v2_funct_1(A_983)
      | ~ v1_funct_1(A_983)
      | ~ v1_relat_1(A_983) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_11800])).

tff(c_13861,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10900,c_13826])).

tff(c_13875,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_84,c_78,c_13507,c_230,c_10881,c_13861])).

tff(c_13877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11145,c_13875])).

tff(c_13878,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10911])).

tff(c_13879,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10911])).

tff(c_13898,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13878,c_13879])).

tff(c_284,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_85])).

tff(c_10877,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10869,c_10869,c_284])).

tff(c_13940,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13878,c_13878,c_10877])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10882,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10869,c_16])).

tff(c_13994,plain,(
    ! [A_6] : m1_subset_1('#skF_1',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13878,c_10882])).

tff(c_14867,plain,(
    ! [A_1084,B_1085,C_1086] :
      ( k2_relset_1(A_1084,B_1085,C_1086) = k2_relat_1(C_1086)
      | ~ m1_subset_1(C_1086,k1_zfmisc_1(k2_zfmisc_1(A_1084,B_1085))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_14880,plain,(
    ! [A_1084,B_1085] : k2_relset_1(A_1084,B_1085,'#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_13994,c_14867])).

tff(c_14890,plain,(
    ! [A_1084,B_1085] : k2_relset_1(A_1084,B_1085,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13940,c_14880])).

tff(c_13890,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13878,c_76])).

tff(c_14894,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14890,c_13890])).

tff(c_14896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13898,c_14894])).

tff(c_14897,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_14934,plain,(
    ! [C_1090,A_1091,B_1092] :
      ( v1_relat_1(C_1090)
      | ~ m1_subset_1(C_1090,k1_zfmisc_1(k2_zfmisc_1(A_1091,B_1092))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_14959,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_14934])).

tff(c_15803,plain,(
    ! [A_1193,B_1194,C_1195] :
      ( k2_relset_1(A_1193,B_1194,C_1195) = k2_relat_1(C_1195)
      | ~ m1_subset_1(C_1195,k1_zfmisc_1(k2_zfmisc_1(A_1193,B_1194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_15816,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_15803])).

tff(c_15832,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_15816])).

tff(c_14898,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_15632,plain,(
    ! [A_1176,B_1177,C_1178] :
      ( k1_relset_1(A_1176,B_1177,C_1178) = k1_relat_1(C_1178)
      | ~ m1_subset_1(C_1178,k1_zfmisc_1(k2_zfmisc_1(A_1176,B_1177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_15656,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14898,c_15632])).

tff(c_16333,plain,(
    ! [B_1238,C_1239,A_1240] :
      ( k1_xboole_0 = B_1238
      | v1_funct_2(C_1239,A_1240,B_1238)
      | k1_relset_1(A_1240,B_1238,C_1239) != A_1240
      | ~ m1_subset_1(C_1239,k1_zfmisc_1(k2_zfmisc_1(A_1240,B_1238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_16342,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_14898,c_16333])).

tff(c_16368,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15656,c_16342])).

tff(c_16369,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_14897,c_16368])).

tff(c_16379,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_16369])).

tff(c_16382,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_16379])).

tff(c_16385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14959,c_84,c_78,c_15832,c_16382])).

tff(c_16386,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_16369])).

tff(c_16435,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16386,c_8])).

tff(c_16433,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16386,c_16386,c_14])).

tff(c_15057,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_16638,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16433,c_15057])).

tff(c_16643,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16435,c_16638])).

tff(c_16644,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_16647,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16644,c_80])).

tff(c_19544,plain,(
    ! [A_1497,B_1498,C_1499] :
      ( k1_relset_1(A_1497,B_1498,C_1499) = k1_relat_1(C_1499)
      | ~ m1_subset_1(C_1499,k1_zfmisc_1(k2_zfmisc_1(A_1497,B_1498))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_19607,plain,(
    ! [C_1504] :
      ( k1_relset_1('#skF_1','#skF_2',C_1504) = k1_relat_1(C_1504)
      | ~ m1_subset_1(C_1504,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16644,c_19544])).

tff(c_19619,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16647,c_19607])).

tff(c_20337,plain,(
    ! [B_1558,A_1559,C_1560] :
      ( k1_xboole_0 = B_1558
      | k1_relset_1(A_1559,B_1558,C_1560) = A_1559
      | ~ v1_funct_2(C_1560,A_1559,B_1558)
      | ~ m1_subset_1(C_1560,k1_zfmisc_1(k2_zfmisc_1(A_1559,B_1558))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_20349,plain,(
    ! [C_1560] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_1560) = '#skF_1'
      | ~ v1_funct_2(C_1560,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_1560,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16644,c_20337])).

tff(c_20651,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_20349])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16658,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_16644,c_10])).

tff(c_16704,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_16658])).

tff(c_20695,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20651,c_16704])).

tff(c_21184,plain,(
    ! [A_1590] : k2_zfmisc_1(A_1590,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20651,c_20651,c_12])).

tff(c_21269,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_21184,c_16644])).

tff(c_21305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20695,c_21269])).

tff(c_21603,plain,(
    ! [C_1612] :
      ( k1_relset_1('#skF_1','#skF_2',C_1612) = '#skF_1'
      | ~ v1_funct_2(C_1612,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_1612,k1_zfmisc_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_20349])).

tff(c_21606,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_16647,c_21603])).

tff(c_21617,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_19619,c_21606])).

tff(c_14956,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14898,c_14934])).

tff(c_19698,plain,(
    ! [A_1511,B_1512,C_1513] :
      ( k2_relset_1(A_1511,B_1512,C_1513) = k2_relat_1(C_1513)
      | ~ m1_subset_1(C_1513,k1_zfmisc_1(k2_zfmisc_1(A_1511,B_1512))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_19757,plain,(
    ! [C_1519] :
      ( k2_relset_1('#skF_1','#skF_2',C_1519) = k2_relat_1(C_1519)
      | ~ m1_subset_1(C_1519,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16644,c_19698])).

tff(c_19760,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16647,c_19757])).

tff(c_19770,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_19760])).

tff(c_19231,plain,(
    ! [A_1466] :
      ( k1_relat_1(k2_funct_1(A_1466)) = k2_relat_1(A_1466)
      | ~ v2_funct_1(A_1466)
      | ~ v1_funct_1(A_1466)
      | ~ v1_relat_1(A_1466) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_23527,plain,(
    ! [A_1682] :
      ( v1_funct_2(k2_funct_1(A_1682),k2_relat_1(A_1682),k2_relat_1(k2_funct_1(A_1682)))
      | ~ v1_funct_1(k2_funct_1(A_1682))
      | ~ v1_relat_1(k2_funct_1(A_1682))
      | ~ v2_funct_1(A_1682)
      | ~ v1_funct_1(A_1682)
      | ~ v1_relat_1(A_1682) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19231,c_70])).

tff(c_23530,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_19770,c_23527])).

tff(c_23544,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14959,c_84,c_78,c_14956,c_230,c_23530])).

tff(c_23551,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_23544])).

tff(c_23553,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14959,c_84,c_78,c_21617,c_23551])).

tff(c_23555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14897,c_23553])).

tff(c_23557,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_16658])).

tff(c_23566,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23557,c_23557,c_264])).

tff(c_28,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_86,plain,(
    ! [A_14] : k1_relat_1(k6_partfun1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_28])).

tff(c_23594,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_23566,c_86])).

tff(c_23570,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23557,c_16])).

tff(c_24878,plain,(
    ! [A_1785,B_1786,C_1787] :
      ( k1_relset_1(A_1785,B_1786,C_1787) = k1_relat_1(C_1787)
      | ~ m1_subset_1(C_1787,k1_zfmisc_1(k2_zfmisc_1(A_1785,B_1786))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24885,plain,(
    ! [A_1785,B_1786] : k1_relset_1(A_1785,B_1786,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_23570,c_24878])).

tff(c_24897,plain,(
    ! [A_1785,B_1786] : k1_relset_1(A_1785,B_1786,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23594,c_24885])).

tff(c_54,plain,(
    ! [C_31,B_30] :
      ( v1_funct_2(C_31,k1_xboole_0,B_30)
      | k1_relset_1(k1_xboole_0,B_30,C_31) != k1_xboole_0
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_90,plain,(
    ! [C_31,B_30] :
      ( v1_funct_2(C_31,k1_xboole_0,B_30)
      | k1_relset_1(k1_xboole_0,B_30,C_31) != k1_xboole_0
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_54])).

tff(c_25351,plain,(
    ! [C_1838,B_1839] :
      ( v1_funct_2(C_1838,'#skF_3',B_1839)
      | k1_relset_1('#skF_3',B_1839,C_1838) != '#skF_3'
      | ~ m1_subset_1(C_1838,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23557,c_23557,c_23557,c_23557,c_90])).

tff(c_25354,plain,(
    ! [B_1839] :
      ( v1_funct_2('#skF_3','#skF_3',B_1839)
      | k1_relset_1('#skF_3',B_1839,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_23570,c_25351])).

tff(c_25360,plain,(
    ! [B_1839] : v1_funct_2('#skF_3','#skF_3',B_1839) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24897,c_25354])).

tff(c_23569,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23557,c_23557,c_14])).

tff(c_23556,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_16658])).

tff(c_24386,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23557,c_23557,c_23556])).

tff(c_24387,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_24386])).

tff(c_23571,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23557,c_8])).

tff(c_23663,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23557,c_23557,c_23556])).

tff(c_23664,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_23663])).

tff(c_14919,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_14898,c_18])).

tff(c_14922,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14919,c_2])).

tff(c_23599,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_14922])).

tff(c_23909,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23571,c_23569,c_23664,c_23599])).

tff(c_23910,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_23663])).

tff(c_23911,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_23663])).

tff(c_23941,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23910,c_23911])).

tff(c_50,plain,(
    ! [A_29] :
      ( v1_funct_2(k1_xboole_0,A_29,k1_xboole_0)
      | k1_xboole_0 = A_29
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_29,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_88,plain,(
    ! [A_29] :
      ( v1_funct_2(k1_xboole_0,A_29,k1_xboole_0)
      | k1_xboole_0 = A_29 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_50])).

tff(c_23567,plain,(
    ! [A_29] :
      ( v1_funct_2('#skF_3',A_29,'#skF_3')
      | A_29 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23557,c_23557,c_23557,c_88])).

tff(c_24292,plain,(
    ! [A_1725] :
      ( v1_funct_2('#skF_1',A_1725,'#skF_1')
      | A_1725 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23910,c_23910,c_23910,c_23567])).

tff(c_23568,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23557,c_23557,c_12])).

tff(c_24046,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23910,c_23910,c_23568])).

tff(c_23930,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23910,c_14898])).

tff(c_24190,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24046,c_23930])).

tff(c_24197,plain,(
    r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_24190,c_18])).

tff(c_270,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_250])).

tff(c_23562,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'
      | ~ r1_tarski(A_3,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23557,c_23557,c_270])).

tff(c_24149,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23910,c_23910,c_23562])).

tff(c_24203,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24197,c_24149])).

tff(c_23931,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23910,c_14897])).

tff(c_24209,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24203,c_23931])).

tff(c_24295,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24292,c_24209])).

tff(c_24299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23941,c_24295])).

tff(c_24300,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_14922])).

tff(c_24525,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23569,c_24387,c_24300])).

tff(c_24394,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24387,c_14897])).

tff(c_24580,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24525,c_24394])).

tff(c_25365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25360,c_24580])).

tff(c_25366,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_24386])).

tff(c_25367,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24386])).

tff(c_25398,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25366,c_25367])).

tff(c_25777,plain,(
    ! [A_1859] :
      ( v1_funct_2('#skF_1',A_1859,'#skF_1')
      | A_1859 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25366,c_25366,c_25366,c_23567])).

tff(c_25562,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25366,c_25366,c_23568])).

tff(c_25661,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25562,c_25366,c_24300])).

tff(c_25388,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25366,c_14897])).

tff(c_25707,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25661,c_25388])).

tff(c_25780,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_25777,c_25707])).

tff(c_25784,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25398,c_25780])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.13/4.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.37/4.45  
% 12.37/4.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.37/4.46  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.37/4.46  
% 12.37/4.46  %Foreground sorts:
% 12.37/4.46  
% 12.37/4.46  
% 12.37/4.46  %Background operators:
% 12.37/4.46  
% 12.37/4.46  
% 12.37/4.46  %Foreground operators:
% 12.37/4.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.37/4.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.37/4.46  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 12.37/4.46  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 12.37/4.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.37/4.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.37/4.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.37/4.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.37/4.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.37/4.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.37/4.46  tff('#skF_2', type, '#skF_2': $i).
% 12.37/4.46  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 12.37/4.46  tff('#skF_3', type, '#skF_3': $i).
% 12.37/4.46  tff('#skF_1', type, '#skF_1': $i).
% 12.37/4.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.37/4.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.37/4.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.37/4.46  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 12.37/4.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.37/4.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.37/4.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.37/4.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 12.37/4.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.37/4.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.37/4.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.37/4.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.37/4.46  
% 12.50/4.49  tff(f_148, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 12.50/4.49  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 12.50/4.49  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.50/4.49  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.50/4.49  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.50/4.49  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 12.50/4.49  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 12.50/4.49  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.50/4.49  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 12.50/4.49  tff(f_131, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 12.50/4.49  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 12.50/4.49  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 12.50/4.49  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.50/4.49  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.50/4.49  tff(f_119, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 12.50/4.49  tff(f_121, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 12.50/4.49  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 12.50/4.49  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 12.50/4.49  tff(c_84, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 12.50/4.49  tff(c_192, plain, (![A_50]: (v1_funct_1(k2_funct_1(A_50)) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_69])).
% 12.50/4.49  tff(c_74, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 12.50/4.49  tff(c_178, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_74])).
% 12.50/4.49  tff(c_195, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_192, c_178])).
% 12.50/4.49  tff(c_198, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_195])).
% 12.50/4.49  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 12.50/4.49  tff(c_204, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.50/4.49  tff(c_214, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_204])).
% 12.50/4.49  tff(c_228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_198, c_214])).
% 12.50/4.49  tff(c_229, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_74])).
% 12.50/4.49  tff(c_300, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_229])).
% 12.50/4.49  tff(c_322, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.50/4.49  tff(c_343, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_322])).
% 12.50/4.49  tff(c_78, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 12.50/4.49  tff(c_82, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 12.50/4.49  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.50/4.49  tff(c_879, plain, (![A_134, B_135, C_136]: (k1_relset_1(A_134, B_135, C_136)=k1_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.50/4.49  tff(c_903, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_879])).
% 12.50/4.49  tff(c_5431, plain, (![B_412, A_413, C_414]: (k1_xboole_0=B_412 | k1_relset_1(A_413, B_412, C_414)=A_413 | ~v1_funct_2(C_414, A_413, B_412) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(A_413, B_412))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.50/4.49  tff(c_5447, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_80, c_5431])).
% 12.50/4.49  tff(c_5464, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_903, c_5447])).
% 12.50/4.49  tff(c_5468, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_5464])).
% 12.50/4.49  tff(c_1452, plain, (![B_194, A_195, C_196]: (k1_xboole_0=B_194 | k1_relset_1(A_195, B_194, C_196)=A_195 | ~v1_funct_2(C_196, A_195, B_194) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_195, B_194))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.50/4.49  tff(c_1468, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_80, c_1452])).
% 12.50/4.49  tff(c_1488, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_903, c_1468])).
% 12.50/4.49  tff(c_1492, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1488])).
% 12.50/4.49  tff(c_36, plain, (![A_16]: (k2_relat_1(k2_funct_1(A_16))=k1_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.50/4.49  tff(c_34, plain, (![A_15]: (v1_relat_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 12.50/4.49  tff(c_76, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_148])).
% 12.50/4.49  tff(c_983, plain, (![A_153, B_154, C_155]: (k2_relset_1(A_153, B_154, C_155)=k2_relat_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.50/4.49  tff(c_993, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_983])).
% 12.50/4.49  tff(c_1008, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_993])).
% 12.50/4.49  tff(c_808, plain, (![A_130]: (k1_relat_1(k2_funct_1(A_130))=k2_relat_1(A_130) | ~v2_funct_1(A_130) | ~v1_funct_1(A_130) | ~v1_relat_1(A_130))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.50/4.49  tff(c_521, plain, (![B_93, A_94]: (v4_relat_1(B_93, A_94) | ~r1_tarski(k1_relat_1(B_93), A_94) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.50/4.49  tff(c_540, plain, (![B_93]: (v4_relat_1(B_93, k1_relat_1(B_93)) | ~v1_relat_1(B_93))), inference(resolution, [status(thm)], [c_6, c_521])).
% 12.50/4.49  tff(c_3495, plain, (![A_324]: (v4_relat_1(k2_funct_1(A_324), k2_relat_1(A_324)) | ~v1_relat_1(k2_funct_1(A_324)) | ~v2_funct_1(A_324) | ~v1_funct_1(A_324) | ~v1_relat_1(A_324))), inference(superposition, [status(thm), theory('equality')], [c_808, c_540])).
% 12.50/4.49  tff(c_3501, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1008, c_3495])).
% 12.50/4.49  tff(c_3514, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_84, c_78, c_3501])).
% 12.50/4.49  tff(c_3519, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3514])).
% 12.50/4.49  tff(c_3522, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_3519])).
% 12.50/4.49  tff(c_3526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_343, c_84, c_3522])).
% 12.50/4.49  tff(c_3528, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3514])).
% 12.50/4.49  tff(c_230, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_74])).
% 12.50/4.49  tff(c_38, plain, (![A_16]: (k1_relat_1(k2_funct_1(A_16))=k2_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.50/4.49  tff(c_1055, plain, (![A_161]: (m1_subset_1(A_161, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_161), k2_relat_1(A_161)))) | ~v1_funct_1(A_161) | ~v1_relat_1(A_161))), inference(cnfTransformation, [status(thm)], [f_131])).
% 12.50/4.49  tff(c_4784, plain, (![A_392]: (m1_subset_1(k2_funct_1(A_392), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_392), k2_relat_1(k2_funct_1(A_392))))) | ~v1_funct_1(k2_funct_1(A_392)) | ~v1_relat_1(k2_funct_1(A_392)) | ~v2_funct_1(A_392) | ~v1_funct_1(A_392) | ~v1_relat_1(A_392))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1055])).
% 12.50/4.49  tff(c_4813, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1008, c_4784])).
% 12.50/4.49  tff(c_4836, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_84, c_78, c_3528, c_230, c_4813])).
% 12.50/4.49  tff(c_4920, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_4836])).
% 12.50/4.49  tff(c_4937, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_84, c_78, c_1492, c_4920])).
% 12.50/4.49  tff(c_4939, plain, $false, inference(negUnitSimplification, [status(thm)], [c_300, c_4937])).
% 12.50/4.49  tff(c_4940, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1488])).
% 12.50/4.49  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.50/4.49  tff(c_4985, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4940, c_8])).
% 12.50/4.49  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.50/4.49  tff(c_4982, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4940, c_4940, c_12])).
% 12.50/4.49  tff(c_1078, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1008, c_1055])).
% 12.50/4.49  tff(c_1105, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_84, c_1078])).
% 12.50/4.49  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.50/4.49  tff(c_1143, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_1105, c_18])).
% 12.50/4.49  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.50/4.49  tff(c_1165, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_1143, c_2])).
% 12.50/4.49  tff(c_1292, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1165])).
% 12.50/4.49  tff(c_5289, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4982, c_1292])).
% 12.50/4.49  tff(c_5299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4985, c_5289])).
% 12.50/4.49  tff(c_5300, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_1165])).
% 12.50/4.49  tff(c_5469, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5468, c_5300])).
% 12.50/4.49  tff(c_151, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.50/4.49  tff(c_158, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_80, c_151])).
% 12.50/4.49  tff(c_250, plain, (![B_61, A_62]: (B_61=A_62 | ~r1_tarski(B_61, A_62) | ~r1_tarski(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.50/4.49  tff(c_265, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_158, c_250])).
% 12.50/4.49  tff(c_349, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_265])).
% 12.50/4.49  tff(c_5513, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5469, c_349])).
% 12.50/4.49  tff(c_5518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5513])).
% 12.50/4.49  tff(c_5519, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_5464])).
% 12.50/4.49  tff(c_5563, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_5519, c_8])).
% 12.50/4.49  tff(c_5560, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5519, c_5519, c_12])).
% 12.50/4.49  tff(c_5800, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5560, c_349])).
% 12.50/4.49  tff(c_5805, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5563, c_5800])).
% 12.50/4.49  tff(c_5806, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_265])).
% 12.50/4.49  tff(c_5809, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5806, c_80])).
% 12.50/4.49  tff(c_6563, plain, (![A_511, B_512, C_513]: (k1_relset_1(A_511, B_512, C_513)=k1_relat_1(C_513) | ~m1_subset_1(C_513, k1_zfmisc_1(k2_zfmisc_1(A_511, B_512))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.50/4.49  tff(c_6741, plain, (![C_536]: (k1_relset_1('#skF_1', '#skF_2', C_536)=k1_relat_1(C_536) | ~m1_subset_1(C_536, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5806, c_6563])).
% 12.50/4.49  tff(c_6753, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5809, c_6741])).
% 12.50/4.49  tff(c_7660, plain, (![B_603, A_604, C_605]: (k1_xboole_0=B_603 | k1_relset_1(A_604, B_603, C_605)=A_604 | ~v1_funct_2(C_605, A_604, B_603) | ~m1_subset_1(C_605, k1_zfmisc_1(k2_zfmisc_1(A_604, B_603))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.50/4.49  tff(c_7669, plain, (![C_605]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_605)='#skF_1' | ~v1_funct_2(C_605, '#skF_1', '#skF_2') | ~m1_subset_1(C_605, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5806, c_7660])).
% 12.50/4.49  tff(c_7756, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_7669])).
% 12.50/4.49  tff(c_5865, plain, (![B_426, A_427]: (k1_xboole_0=B_426 | k1_xboole_0=A_427 | k2_zfmisc_1(A_427, B_426)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.50/4.49  tff(c_5868, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_5806, c_5865])).
% 12.50/4.49  tff(c_5892, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_5868])).
% 12.50/4.49  tff(c_7801, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7756, c_5892])).
% 12.50/4.49  tff(c_8135, plain, (![A_619]: (k2_zfmisc_1(A_619, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7756, c_7756, c_12])).
% 12.50/4.49  tff(c_8211, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_8135, c_5806])).
% 12.50/4.49  tff(c_8239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7801, c_8211])).
% 12.50/4.49  tff(c_8689, plain, (![C_652]: (k1_relset_1('#skF_1', '#skF_2', C_652)='#skF_1' | ~v1_funct_2(C_652, '#skF_1', '#skF_2') | ~m1_subset_1(C_652, k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_7669])).
% 12.50/4.49  tff(c_8692, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_5809, c_8689])).
% 12.50/4.49  tff(c_8703, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_6753, c_8692])).
% 12.50/4.49  tff(c_6681, plain, (![A_529, B_530, C_531]: (k2_relset_1(A_529, B_530, C_531)=k2_relat_1(C_531) | ~m1_subset_1(C_531, k1_zfmisc_1(k2_zfmisc_1(A_529, B_530))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.50/4.49  tff(c_6918, plain, (![C_549]: (k2_relset_1('#skF_1', '#skF_2', C_549)=k2_relat_1(C_549) | ~m1_subset_1(C_549, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5806, c_6681])).
% 12.50/4.49  tff(c_6921, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5809, c_6918])).
% 12.50/4.49  tff(c_6931, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_6921])).
% 12.50/4.49  tff(c_6142, plain, (![B_469, A_470]: (r1_tarski(k1_relat_1(B_469), A_470) | ~v4_relat_1(B_469, A_470) | ~v1_relat_1(B_469))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.50/4.49  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.50/4.49  tff(c_5893, plain, (![C_429, B_430, A_431]: (v5_relat_1(C_429, B_430) | ~m1_subset_1(C_429, k1_zfmisc_1(k2_zfmisc_1(A_431, B_430))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 12.50/4.49  tff(c_5914, plain, (![A_7, B_430, A_431]: (v5_relat_1(A_7, B_430) | ~r1_tarski(A_7, k2_zfmisc_1(A_431, B_430)))), inference(resolution, [status(thm)], [c_20, c_5893])).
% 12.50/4.49  tff(c_6528, plain, (![B_508, B_509, A_510]: (v5_relat_1(k1_relat_1(B_508), B_509) | ~v4_relat_1(B_508, k2_zfmisc_1(A_510, B_509)) | ~v1_relat_1(B_508))), inference(resolution, [status(thm)], [c_6142, c_5914])).
% 12.50/4.49  tff(c_6727, plain, (![B_535]: (v5_relat_1(k1_relat_1(B_535), '#skF_2') | ~v4_relat_1(B_535, '#skF_3') | ~v1_relat_1(B_535))), inference(superposition, [status(thm), theory('equality')], [c_5806, c_6528])).
% 12.50/4.49  tff(c_7041, plain, (![A_553]: (v5_relat_1(k2_relat_1(A_553), '#skF_2') | ~v4_relat_1(k2_funct_1(A_553), '#skF_3') | ~v1_relat_1(k2_funct_1(A_553)) | ~v2_funct_1(A_553) | ~v1_funct_1(A_553) | ~v1_relat_1(A_553))), inference(superposition, [status(thm), theory('equality')], [c_38, c_6727])).
% 12.50/4.49  tff(c_7044, plain, (v5_relat_1('#skF_2', '#skF_2') | ~v4_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6931, c_7041])).
% 12.50/4.49  tff(c_7055, plain, (v5_relat_1('#skF_2', '#skF_2') | ~v4_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_84, c_78, c_7044])).
% 12.50/4.49  tff(c_7130, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_7055])).
% 12.50/4.49  tff(c_7133, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_7130])).
% 12.50/4.49  tff(c_7137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_343, c_84, c_7133])).
% 12.50/4.49  tff(c_7139, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_7055])).
% 12.50/4.49  tff(c_6825, plain, (![A_543]: (m1_subset_1(A_543, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_543), k2_relat_1(A_543)))) | ~v1_funct_1(A_543) | ~v1_relat_1(A_543))), inference(cnfTransformation, [status(thm)], [f_131])).
% 12.50/4.49  tff(c_10765, plain, (![A_727]: (m1_subset_1(k2_funct_1(A_727), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_727), k2_relat_1(k2_funct_1(A_727))))) | ~v1_funct_1(k2_funct_1(A_727)) | ~v1_relat_1(k2_funct_1(A_727)) | ~v2_funct_1(A_727) | ~v1_funct_1(A_727) | ~v1_relat_1(A_727))), inference(superposition, [status(thm), theory('equality')], [c_38, c_6825])).
% 12.50/4.49  tff(c_10794, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6931, c_10765])).
% 12.50/4.49  tff(c_10817, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_84, c_78, c_7139, c_230, c_10794])).
% 12.50/4.49  tff(c_10850, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_10817])).
% 12.50/4.49  tff(c_10865, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_84, c_78, c_8703, c_10850])).
% 12.50/4.49  tff(c_10867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_300, c_10865])).
% 12.50/4.49  tff(c_10869, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_5868])).
% 12.50/4.49  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.50/4.49  tff(c_10881, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10869, c_10869, c_14])).
% 12.50/4.49  tff(c_10868, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_5868])).
% 12.50/4.49  tff(c_10911, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10869, c_10869, c_10868])).
% 12.50/4.49  tff(c_10912, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_10911])).
% 12.50/4.49  tff(c_10915, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_10912, c_300])).
% 12.50/4.49  tff(c_11145, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10881, c_10915])).
% 12.50/4.49  tff(c_161, plain, (![A_47]: (m1_subset_1(k6_partfun1(A_47), k1_zfmisc_1(k2_zfmisc_1(A_47, A_47))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 12.50/4.49  tff(c_168, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_161])).
% 12.50/4.49  tff(c_177, plain, (r1_tarski(k6_partfun1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_168, c_18])).
% 12.50/4.49  tff(c_254, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_177, c_250])).
% 12.50/4.49  tff(c_264, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_254])).
% 12.50/4.49  tff(c_10878, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10869, c_10869, c_264])).
% 12.50/4.49  tff(c_66, plain, (![A_33]: (k6_relat_1(A_33)=k6_partfun1(A_33))), inference(cnfTransformation, [status(thm)], [f_121])).
% 12.50/4.49  tff(c_30, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.50/4.49  tff(c_85, plain, (![A_14]: (k2_relat_1(k6_partfun1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_30])).
% 12.50/4.49  tff(c_10900, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_10878, c_85])).
% 12.50/4.49  tff(c_11388, plain, (![A_788]: (k1_relat_1(k2_funct_1(A_788))=k2_relat_1(A_788) | ~v2_funct_1(A_788) | ~v1_funct_1(A_788) | ~v1_relat_1(A_788))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.50/4.49  tff(c_70, plain, (![A_34]: (v1_funct_2(A_34, k1_relat_1(A_34), k2_relat_1(A_34)) | ~v1_funct_1(A_34) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_131])).
% 12.50/4.49  tff(c_13481, plain, (![A_959]: (v1_funct_2(k2_funct_1(A_959), k2_relat_1(A_959), k2_relat_1(k2_funct_1(A_959))) | ~v1_funct_1(k2_funct_1(A_959)) | ~v1_relat_1(k2_funct_1(A_959)) | ~v2_funct_1(A_959) | ~v1_funct_1(A_959) | ~v1_relat_1(A_959))), inference(superposition, [status(thm), theory('equality')], [c_11388, c_70])).
% 12.50/4.49  tff(c_13490, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10900, c_13481])).
% 12.50/4.49  tff(c_13495, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_84, c_78, c_230, c_13490])).
% 12.50/4.49  tff(c_13498, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_13495])).
% 12.50/4.49  tff(c_13501, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_13498])).
% 12.50/4.49  tff(c_13505, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_343, c_84, c_13501])).
% 12.50/4.49  tff(c_13507, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_13495])).
% 12.50/4.49  tff(c_11800, plain, (![A_841]: (m1_subset_1(A_841, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_841), k2_relat_1(A_841)))) | ~v1_funct_1(A_841) | ~v1_relat_1(A_841))), inference(cnfTransformation, [status(thm)], [f_131])).
% 12.50/4.49  tff(c_13826, plain, (![A_983]: (m1_subset_1(k2_funct_1(A_983), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_983), k2_relat_1(k2_funct_1(A_983))))) | ~v1_funct_1(k2_funct_1(A_983)) | ~v1_relat_1(k2_funct_1(A_983)) | ~v2_funct_1(A_983) | ~v1_funct_1(A_983) | ~v1_relat_1(A_983))), inference(superposition, [status(thm), theory('equality')], [c_38, c_11800])).
% 12.50/4.49  tff(c_13861, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10900, c_13826])).
% 12.50/4.49  tff(c_13875, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_84, c_78, c_13507, c_230, c_10881, c_13861])).
% 12.50/4.49  tff(c_13877, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11145, c_13875])).
% 12.50/4.49  tff(c_13878, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_10911])).
% 12.50/4.49  tff(c_13879, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_10911])).
% 12.50/4.49  tff(c_13898, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13878, c_13879])).
% 12.50/4.49  tff(c_284, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_264, c_85])).
% 12.50/4.49  tff(c_10877, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10869, c_10869, c_284])).
% 12.50/4.49  tff(c_13940, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13878, c_13878, c_10877])).
% 12.50/4.49  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.50/4.49  tff(c_10882, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_10869, c_16])).
% 12.50/4.49  tff(c_13994, plain, (![A_6]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_13878, c_10882])).
% 12.50/4.49  tff(c_14867, plain, (![A_1084, B_1085, C_1086]: (k2_relset_1(A_1084, B_1085, C_1086)=k2_relat_1(C_1086) | ~m1_subset_1(C_1086, k1_zfmisc_1(k2_zfmisc_1(A_1084, B_1085))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.50/4.49  tff(c_14880, plain, (![A_1084, B_1085]: (k2_relset_1(A_1084, B_1085, '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_13994, c_14867])).
% 12.50/4.49  tff(c_14890, plain, (![A_1084, B_1085]: (k2_relset_1(A_1084, B_1085, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13940, c_14880])).
% 12.50/4.49  tff(c_13890, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_13878, c_76])).
% 12.50/4.49  tff(c_14894, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14890, c_13890])).
% 12.50/4.49  tff(c_14896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13898, c_14894])).
% 12.50/4.49  tff(c_14897, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_229])).
% 12.50/4.49  tff(c_14934, plain, (![C_1090, A_1091, B_1092]: (v1_relat_1(C_1090) | ~m1_subset_1(C_1090, k1_zfmisc_1(k2_zfmisc_1(A_1091, B_1092))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.50/4.49  tff(c_14959, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_14934])).
% 12.50/4.49  tff(c_15803, plain, (![A_1193, B_1194, C_1195]: (k2_relset_1(A_1193, B_1194, C_1195)=k2_relat_1(C_1195) | ~m1_subset_1(C_1195, k1_zfmisc_1(k2_zfmisc_1(A_1193, B_1194))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.50/4.49  tff(c_15816, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_15803])).
% 12.50/4.49  tff(c_15832, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_15816])).
% 12.50/4.49  tff(c_14898, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_229])).
% 12.50/4.49  tff(c_15632, plain, (![A_1176, B_1177, C_1178]: (k1_relset_1(A_1176, B_1177, C_1178)=k1_relat_1(C_1178) | ~m1_subset_1(C_1178, k1_zfmisc_1(k2_zfmisc_1(A_1176, B_1177))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.50/4.49  tff(c_15656, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_14898, c_15632])).
% 12.50/4.49  tff(c_16333, plain, (![B_1238, C_1239, A_1240]: (k1_xboole_0=B_1238 | v1_funct_2(C_1239, A_1240, B_1238) | k1_relset_1(A_1240, B_1238, C_1239)!=A_1240 | ~m1_subset_1(C_1239, k1_zfmisc_1(k2_zfmisc_1(A_1240, B_1238))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.50/4.49  tff(c_16342, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_14898, c_16333])).
% 12.50/4.49  tff(c_16368, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_15656, c_16342])).
% 12.50/4.49  tff(c_16369, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_14897, c_16368])).
% 12.50/4.49  tff(c_16379, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_16369])).
% 12.50/4.49  tff(c_16382, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_16379])).
% 12.50/4.49  tff(c_16385, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14959, c_84, c_78, c_15832, c_16382])).
% 12.50/4.49  tff(c_16386, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_16369])).
% 12.50/4.49  tff(c_16435, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_16386, c_8])).
% 12.50/4.49  tff(c_16433, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16386, c_16386, c_14])).
% 12.50/4.49  tff(c_15057, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_265])).
% 12.50/4.49  tff(c_16638, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16433, c_15057])).
% 12.50/4.49  tff(c_16643, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16435, c_16638])).
% 12.50/4.49  tff(c_16644, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_265])).
% 12.50/4.49  tff(c_16647, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16644, c_80])).
% 12.50/4.49  tff(c_19544, plain, (![A_1497, B_1498, C_1499]: (k1_relset_1(A_1497, B_1498, C_1499)=k1_relat_1(C_1499) | ~m1_subset_1(C_1499, k1_zfmisc_1(k2_zfmisc_1(A_1497, B_1498))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.50/4.49  tff(c_19607, plain, (![C_1504]: (k1_relset_1('#skF_1', '#skF_2', C_1504)=k1_relat_1(C_1504) | ~m1_subset_1(C_1504, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_16644, c_19544])).
% 12.50/4.49  tff(c_19619, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16647, c_19607])).
% 12.50/4.49  tff(c_20337, plain, (![B_1558, A_1559, C_1560]: (k1_xboole_0=B_1558 | k1_relset_1(A_1559, B_1558, C_1560)=A_1559 | ~v1_funct_2(C_1560, A_1559, B_1558) | ~m1_subset_1(C_1560, k1_zfmisc_1(k2_zfmisc_1(A_1559, B_1558))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.50/4.49  tff(c_20349, plain, (![C_1560]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_1560)='#skF_1' | ~v1_funct_2(C_1560, '#skF_1', '#skF_2') | ~m1_subset_1(C_1560, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_16644, c_20337])).
% 12.50/4.49  tff(c_20651, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_20349])).
% 12.50/4.49  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.50/4.49  tff(c_16658, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_16644, c_10])).
% 12.50/4.49  tff(c_16704, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_16658])).
% 12.50/4.49  tff(c_20695, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20651, c_16704])).
% 12.50/4.49  tff(c_21184, plain, (![A_1590]: (k2_zfmisc_1(A_1590, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20651, c_20651, c_12])).
% 12.50/4.49  tff(c_21269, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_21184, c_16644])).
% 12.50/4.49  tff(c_21305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20695, c_21269])).
% 12.50/4.49  tff(c_21603, plain, (![C_1612]: (k1_relset_1('#skF_1', '#skF_2', C_1612)='#skF_1' | ~v1_funct_2(C_1612, '#skF_1', '#skF_2') | ~m1_subset_1(C_1612, k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_20349])).
% 12.50/4.49  tff(c_21606, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_16647, c_21603])).
% 12.50/4.49  tff(c_21617, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_19619, c_21606])).
% 12.50/4.49  tff(c_14956, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_14898, c_14934])).
% 12.50/4.49  tff(c_19698, plain, (![A_1511, B_1512, C_1513]: (k2_relset_1(A_1511, B_1512, C_1513)=k2_relat_1(C_1513) | ~m1_subset_1(C_1513, k1_zfmisc_1(k2_zfmisc_1(A_1511, B_1512))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 12.50/4.49  tff(c_19757, plain, (![C_1519]: (k2_relset_1('#skF_1', '#skF_2', C_1519)=k2_relat_1(C_1519) | ~m1_subset_1(C_1519, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_16644, c_19698])).
% 12.50/4.49  tff(c_19760, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16647, c_19757])).
% 12.50/4.49  tff(c_19770, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_19760])).
% 12.50/4.49  tff(c_19231, plain, (![A_1466]: (k1_relat_1(k2_funct_1(A_1466))=k2_relat_1(A_1466) | ~v2_funct_1(A_1466) | ~v1_funct_1(A_1466) | ~v1_relat_1(A_1466))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.50/4.49  tff(c_23527, plain, (![A_1682]: (v1_funct_2(k2_funct_1(A_1682), k2_relat_1(A_1682), k2_relat_1(k2_funct_1(A_1682))) | ~v1_funct_1(k2_funct_1(A_1682)) | ~v1_relat_1(k2_funct_1(A_1682)) | ~v2_funct_1(A_1682) | ~v1_funct_1(A_1682) | ~v1_relat_1(A_1682))), inference(superposition, [status(thm), theory('equality')], [c_19231, c_70])).
% 12.50/4.49  tff(c_23530, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_19770, c_23527])).
% 12.50/4.49  tff(c_23544, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_14959, c_84, c_78, c_14956, c_230, c_23530])).
% 12.50/4.49  tff(c_23551, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_23544])).
% 12.50/4.49  tff(c_23553, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14959, c_84, c_78, c_21617, c_23551])).
% 12.50/4.49  tff(c_23555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14897, c_23553])).
% 12.50/4.49  tff(c_23557, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_16658])).
% 12.50/4.49  tff(c_23566, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_23557, c_23557, c_264])).
% 12.50/4.49  tff(c_28, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.50/4.49  tff(c_86, plain, (![A_14]: (k1_relat_1(k6_partfun1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_28])).
% 12.50/4.49  tff(c_23594, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_23566, c_86])).
% 12.50/4.49  tff(c_23570, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_23557, c_16])).
% 12.50/4.49  tff(c_24878, plain, (![A_1785, B_1786, C_1787]: (k1_relset_1(A_1785, B_1786, C_1787)=k1_relat_1(C_1787) | ~m1_subset_1(C_1787, k1_zfmisc_1(k2_zfmisc_1(A_1785, B_1786))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.50/4.49  tff(c_24885, plain, (![A_1785, B_1786]: (k1_relset_1(A_1785, B_1786, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_23570, c_24878])).
% 12.50/4.49  tff(c_24897, plain, (![A_1785, B_1786]: (k1_relset_1(A_1785, B_1786, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_23594, c_24885])).
% 12.50/4.49  tff(c_54, plain, (![C_31, B_30]: (v1_funct_2(C_31, k1_xboole_0, B_30) | k1_relset_1(k1_xboole_0, B_30, C_31)!=k1_xboole_0 | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_30))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.50/4.49  tff(c_90, plain, (![C_31, B_30]: (v1_funct_2(C_31, k1_xboole_0, B_30) | k1_relset_1(k1_xboole_0, B_30, C_31)!=k1_xboole_0 | ~m1_subset_1(C_31, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_54])).
% 12.50/4.49  tff(c_25351, plain, (![C_1838, B_1839]: (v1_funct_2(C_1838, '#skF_3', B_1839) | k1_relset_1('#skF_3', B_1839, C_1838)!='#skF_3' | ~m1_subset_1(C_1838, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_23557, c_23557, c_23557, c_23557, c_90])).
% 12.50/4.49  tff(c_25354, plain, (![B_1839]: (v1_funct_2('#skF_3', '#skF_3', B_1839) | k1_relset_1('#skF_3', B_1839, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_23570, c_25351])).
% 12.50/4.49  tff(c_25360, plain, (![B_1839]: (v1_funct_2('#skF_3', '#skF_3', B_1839))), inference(demodulation, [status(thm), theory('equality')], [c_24897, c_25354])).
% 12.50/4.49  tff(c_23569, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_23557, c_23557, c_14])).
% 12.50/4.49  tff(c_23556, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_16658])).
% 12.50/4.49  tff(c_24386, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_23557, c_23557, c_23556])).
% 12.50/4.49  tff(c_24387, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_24386])).
% 12.50/4.49  tff(c_23571, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_23557, c_8])).
% 12.50/4.49  tff(c_23663, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_23557, c_23557, c_23556])).
% 12.50/4.49  tff(c_23664, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_23663])).
% 12.50/4.49  tff(c_14919, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_14898, c_18])).
% 12.50/4.49  tff(c_14922, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_14919, c_2])).
% 12.50/4.49  tff(c_23599, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_14922])).
% 12.50/4.49  tff(c_23909, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23571, c_23569, c_23664, c_23599])).
% 12.50/4.49  tff(c_23910, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_23663])).
% 12.50/4.49  tff(c_23911, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_23663])).
% 12.50/4.49  tff(c_23941, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_23910, c_23911])).
% 12.50/4.49  tff(c_50, plain, (![A_29]: (v1_funct_2(k1_xboole_0, A_29, k1_xboole_0) | k1_xboole_0=A_29 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_29, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.50/4.49  tff(c_88, plain, (![A_29]: (v1_funct_2(k1_xboole_0, A_29, k1_xboole_0) | k1_xboole_0=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_50])).
% 12.50/4.49  tff(c_23567, plain, (![A_29]: (v1_funct_2('#skF_3', A_29, '#skF_3') | A_29='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_23557, c_23557, c_23557, c_88])).
% 12.50/4.49  tff(c_24292, plain, (![A_1725]: (v1_funct_2('#skF_1', A_1725, '#skF_1') | A_1725='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_23910, c_23910, c_23910, c_23567])).
% 12.50/4.49  tff(c_23568, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_23557, c_23557, c_12])).
% 12.50/4.49  tff(c_24046, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_23910, c_23910, c_23568])).
% 12.50/4.49  tff(c_23930, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_23910, c_14898])).
% 12.50/4.49  tff(c_24190, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24046, c_23930])).
% 12.50/4.49  tff(c_24197, plain, (r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_24190, c_18])).
% 12.50/4.49  tff(c_270, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_250])).
% 12.50/4.49  tff(c_23562, plain, (![A_3]: (A_3='#skF_3' | ~r1_tarski(A_3, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_23557, c_23557, c_270])).
% 12.50/4.49  tff(c_24149, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_23910, c_23910, c_23562])).
% 12.50/4.49  tff(c_24203, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_24197, c_24149])).
% 12.50/4.49  tff(c_23931, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_23910, c_14897])).
% 12.50/4.49  tff(c_24209, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24203, c_23931])).
% 12.50/4.49  tff(c_24295, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_24292, c_24209])).
% 12.50/4.49  tff(c_24299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23941, c_24295])).
% 12.50/4.49  tff(c_24300, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_14922])).
% 12.50/4.49  tff(c_24525, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_23569, c_24387, c_24300])).
% 12.50/4.49  tff(c_24394, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24387, c_14897])).
% 12.50/4.49  tff(c_24580, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24525, c_24394])).
% 12.50/4.49  tff(c_25365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25360, c_24580])).
% 12.50/4.49  tff(c_25366, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_24386])).
% 12.50/4.49  tff(c_25367, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_24386])).
% 12.50/4.49  tff(c_25398, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_25366, c_25367])).
% 12.50/4.49  tff(c_25777, plain, (![A_1859]: (v1_funct_2('#skF_1', A_1859, '#skF_1') | A_1859='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25366, c_25366, c_25366, c_23567])).
% 12.50/4.49  tff(c_25562, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25366, c_25366, c_23568])).
% 12.50/4.49  tff(c_25661, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_25562, c_25366, c_24300])).
% 12.50/4.49  tff(c_25388, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25366, c_14897])).
% 12.50/4.49  tff(c_25707, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_25661, c_25388])).
% 12.50/4.49  tff(c_25780, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_25777, c_25707])).
% 12.50/4.49  tff(c_25784, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25398, c_25780])).
% 12.50/4.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.50/4.49  
% 12.50/4.49  Inference rules
% 12.50/4.49  ----------------------
% 12.50/4.49  #Ref     : 0
% 12.50/4.49  #Sup     : 5387
% 12.50/4.49  #Fact    : 0
% 12.50/4.49  #Define  : 0
% 12.50/4.49  #Split   : 49
% 12.50/4.49  #Chain   : 0
% 12.50/4.49  #Close   : 0
% 12.50/4.49  
% 12.50/4.49  Ordering : KBO
% 12.50/4.49  
% 12.50/4.49  Simplification rules
% 12.50/4.49  ----------------------
% 12.50/4.49  #Subsume      : 848
% 12.50/4.49  #Demod        : 7206
% 12.50/4.49  #Tautology    : 2739
% 12.50/4.49  #SimpNegUnit  : 40
% 12.50/4.49  #BackRed      : 550
% 12.50/4.49  
% 12.50/4.49  #Partial instantiations: 0
% 12.50/4.49  #Strategies tried      : 1
% 12.50/4.49  
% 12.50/4.49  Timing (in seconds)
% 12.50/4.49  ----------------------
% 12.50/4.49  Preprocessing        : 0.37
% 12.50/4.49  Parsing              : 0.20
% 12.50/4.50  CNF conversion       : 0.02
% 12.50/4.50  Main loop            : 3.29
% 12.50/4.50  Inferencing          : 0.99
% 12.50/4.50  Reduction            : 1.31
% 12.50/4.50  Demodulation         : 0.97
% 12.50/4.50  BG Simplification    : 0.08
% 12.50/4.50  Subsumption          : 0.67
% 12.50/4.50  Abstraction          : 0.11
% 12.50/4.50  MUC search           : 0.00
% 12.50/4.50  Cooper               : 0.00
% 12.50/4.50  Total                : 3.76
% 12.50/4.50  Index Insertion      : 0.00
% 12.50/4.50  Index Deletion       : 0.00
% 12.50/4.50  Index Matching       : 0.00
% 12.50/4.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
