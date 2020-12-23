%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:25 EST 2020

% Result     : Theorem 5.80s
% Output     : CNFRefutation 5.96s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 558 expanded)
%              Number of leaves         :   38 ( 202 expanded)
%              Depth                    :   13
%              Number of atoms          :  297 (1679 expanded)
%              Number of equality atoms :   68 ( 310 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_172,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_145,axiom,(
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

tff(f_155,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_127,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_207,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_215,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_207])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_70,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_229,plain,(
    ! [A_65] :
      ( k4_relat_1(A_65) = k2_funct_1(A_65)
      | ~ v2_funct_1(A_65)
      | ~ v1_funct_1(A_65)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_235,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_229])).

tff(c_239,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_76,c_235])).

tff(c_14,plain,(
    ! [A_7] :
      ( v1_xboole_0(k4_relat_1(A_7))
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_249,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_14])).

tff(c_257,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_68,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_385,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_relset_1(A_78,B_79,C_80) = k2_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_388,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_385])).

tff(c_394,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_388])).

tff(c_16,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k2_relat_1(A_8))
      | ~ v1_relat_1(A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_403,plain,
    ( ~ v1_xboole_0('#skF_2')
    | ~ v1_relat_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_16])).

tff(c_409,plain,
    ( ~ v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_403])).

tff(c_410,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_257,c_409])).

tff(c_180,plain,(
    ! [A_45] :
      ( v1_funct_1(k2_funct_1(A_45))
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_178,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_183,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_180,c_178])).

tff(c_186,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_183])).

tff(c_189,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_192,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_189])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_192])).

tff(c_201,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_204,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_34,plain,(
    ! [A_13] :
      ( k1_relat_1(k2_funct_1(A_13)) = k2_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    ! [A_12] :
      ( v1_relat_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_202,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_364,plain,(
    ! [A_73,B_74,C_75] :
      ( k1_relset_1(A_73,B_74,C_75) = k1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_372,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_364])).

tff(c_920,plain,(
    ! [B_116,A_117,C_118] :
      ( k1_xboole_0 = B_116
      | k1_relset_1(A_117,B_116,C_118) = A_117
      | ~ v1_funct_2(C_118,A_117,B_116)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_117,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_929,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_920])).

tff(c_940,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_372,c_929])).

tff(c_943,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_940])).

tff(c_258,plain,(
    ! [A_66] :
      ( k2_relat_1(k2_funct_1(A_66)) = k1_relat_1(A_66)
      | ~ v2_funct_1(A_66)
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_62,plain,(
    ! [A_33] :
      ( v1_funct_2(A_33,k1_relat_1(A_33),k2_relat_1(A_33))
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1630,plain,(
    ! [A_136] :
      ( v1_funct_2(k2_funct_1(A_136),k1_relat_1(k2_funct_1(A_136)),k1_relat_1(A_136))
      | ~ v1_funct_1(k2_funct_1(A_136))
      | ~ v1_relat_1(k2_funct_1(A_136))
      | ~ v2_funct_1(A_136)
      | ~ v1_funct_1(A_136)
      | ~ v1_relat_1(A_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_62])).

tff(c_1657,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_943,c_1630])).

tff(c_1678,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_76,c_70,c_202,c_1657])).

tff(c_1685,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1678])).

tff(c_1688,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1685])).

tff(c_1692,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_76,c_1688])).

tff(c_1694,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1678])).

tff(c_32,plain,(
    ! [A_13] :
      ( k2_relat_1(k2_funct_1(A_13)) = k1_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_412,plain,(
    ! [A_81] :
      ( m1_subset_1(A_81,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_81),k2_relat_1(A_81))))
      | ~ v1_funct_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2136,plain,(
    ! [A_146] :
      ( m1_subset_1(k2_funct_1(A_146),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_146)),k1_relat_1(A_146))))
      | ~ v1_funct_1(k2_funct_1(A_146))
      | ~ v1_relat_1(k2_funct_1(A_146))
      | ~ v2_funct_1(A_146)
      | ~ v1_funct_1(A_146)
      | ~ v1_relat_1(A_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_412])).

tff(c_2180,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_943,c_2136])).

tff(c_2211,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_76,c_70,c_1694,c_202,c_2180])).

tff(c_2243,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2211])).

tff(c_2259,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_76,c_70,c_394,c_2243])).

tff(c_2261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_2259])).

tff(c_2262,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_940])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2288,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2262,c_2])).

tff(c_2290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_410,c_2288])).

tff(c_2292,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2310,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2292,c_4])).

tff(c_6,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2319,plain,(
    ! [A_2] : m1_subset_1('#skF_3',k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2310,c_6])).

tff(c_101,plain,(
    ! [A_39] :
      ( v1_xboole_0(k4_relat_1(A_39))
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_113,plain,(
    ! [A_39] :
      ( k4_relat_1(A_39) = k1_xboole_0
      | ~ v1_xboole_0(A_39) ) ),
    inference(resolution,[status(thm)],[c_101,c_4])).

tff(c_2305,plain,(
    k4_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2292,c_113])).

tff(c_2340,plain,(
    k4_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2310,c_2305])).

tff(c_2341,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2340,c_239])).

tff(c_2364,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2341,c_204])).

tff(c_2499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2319,c_2364])).

tff(c_2500,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_2504,plain,(
    ! [C_161,A_162,B_163] :
      ( v1_relat_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2516,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_2504])).

tff(c_3576,plain,(
    ! [A_240,B_241,C_242] :
      ( k2_relset_1(A_240,B_241,C_242) = k2_relat_1(C_242)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_3586,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_3576])).

tff(c_3591,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3586])).

tff(c_2501,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_2515,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2501,c_2504])).

tff(c_2575,plain,(
    ! [C_175,A_176,B_177] :
      ( v1_partfun1(C_175,A_176)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177)))
      | ~ v1_xboole_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2587,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_2575])).

tff(c_2604,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2587])).

tff(c_2731,plain,(
    ! [A_187,B_188,C_189] :
      ( k2_relset_1(A_187,B_188,C_189) = k2_relat_1(C_189)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_187,B_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2740,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_2731])).

tff(c_2748,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2740])).

tff(c_2698,plain,(
    ! [A_182,B_183,C_184] :
      ( k1_relset_1(A_182,B_183,C_184) = k1_relat_1(C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2713,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2501,c_2698])).

tff(c_3243,plain,(
    ! [B_222,C_223,A_224] :
      ( k1_xboole_0 = B_222
      | v1_funct_2(C_223,A_224,B_222)
      | k1_relset_1(A_224,B_222,C_223) != A_224
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_224,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_3252,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_2501,c_3243])).

tff(c_3265,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2713,c_3252])).

tff(c_3266,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_2500,c_3265])).

tff(c_3292,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3266])).

tff(c_3295,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3292])).

tff(c_3298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2516,c_76,c_70,c_2748,c_3295])).

tff(c_3299,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3266])).

tff(c_3352,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3299,c_2])).

tff(c_3354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2604,c_3352])).

tff(c_3356,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2587])).

tff(c_3673,plain,(
    ! [A_246,B_247,C_248] :
      ( k1_relset_1(A_246,B_247,C_248) = k1_relat_1(C_248)
      | ~ m1_subset_1(C_248,k1_zfmisc_1(k2_zfmisc_1(A_246,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3694,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_3673])).

tff(c_3376,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3356,c_4])).

tff(c_56,plain,(
    ! [B_31,C_32] :
      ( k1_relset_1(k1_xboole_0,B_31,C_32) = k1_xboole_0
      | ~ v1_funct_2(C_32,k1_xboole_0,B_31)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_3983,plain,(
    ! [B_268,C_269] :
      ( k1_relset_1('#skF_1',B_268,C_269) = '#skF_1'
      | ~ v1_funct_2(C_269,'#skF_1',B_268)
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_268))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3376,c_3376,c_3376,c_3376,c_56])).

tff(c_3990,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_3983])).

tff(c_3995,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3694,c_3990])).

tff(c_3620,plain,(
    ! [A_245] :
      ( m1_subset_1(A_245,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_245),k2_relat_1(A_245))))
      | ~ v1_funct_1(A_245)
      | ~ v1_relat_1(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_3634,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3591,c_3620])).

tff(c_3649,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2516,c_76,c_3634])).

tff(c_46,plain,(
    ! [C_29,A_26,B_27] :
      ( v1_partfun1(C_29,A_26)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3665,plain,
    ( v1_partfun1('#skF_3',k1_relat_1('#skF_3'))
    | ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3649,c_46])).

tff(c_3706,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3665])).

tff(c_3998,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3995,c_3706])).

tff(c_4005,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3356,c_3998])).

tff(c_4007,plain,(
    v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3665])).

tff(c_3387,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3376,c_4])).

tff(c_4024,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4007,c_3387])).

tff(c_3431,plain,(
    ! [A_230] :
      ( k2_relat_1(k2_funct_1(A_230)) = k1_relat_1(A_230)
      | ~ v2_funct_1(A_230)
      | ~ v1_funct_1(A_230)
      | ~ v1_relat_1(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4772,plain,(
    ! [A_310] :
      ( v1_funct_2(k2_funct_1(A_310),k1_relat_1(k2_funct_1(A_310)),k1_relat_1(A_310))
      | ~ v1_funct_1(k2_funct_1(A_310))
      | ~ v1_relat_1(k2_funct_1(A_310))
      | ~ v2_funct_1(A_310)
      | ~ v1_funct_1(A_310)
      | ~ v1_relat_1(A_310) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3431,c_62])).

tff(c_4790,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4024,c_4772])).

tff(c_4808,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2516,c_76,c_70,c_2515,c_202,c_4790])).

tff(c_4815,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4808])).

tff(c_4817,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2516,c_76,c_70,c_3591,c_4815])).

tff(c_4819,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2500,c_4817])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:05:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.80/2.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.96/2.16  
% 5.96/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.96/2.16  %$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.96/2.16  
% 5.96/2.16  %Foreground sorts:
% 5.96/2.16  
% 5.96/2.16  
% 5.96/2.16  %Background operators:
% 5.96/2.16  
% 5.96/2.16  
% 5.96/2.16  %Foreground operators:
% 5.96/2.16  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.96/2.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.96/2.16  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.96/2.16  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.96/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.96/2.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.96/2.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.96/2.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.96/2.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.96/2.16  tff('#skF_2', type, '#skF_2': $i).
% 5.96/2.16  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 5.96/2.16  tff('#skF_3', type, '#skF_3': $i).
% 5.96/2.16  tff('#skF_1', type, '#skF_1': $i).
% 5.96/2.16  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.96/2.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.96/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.96/2.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.96/2.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.96/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.96/2.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.96/2.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.96/2.16  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 5.96/2.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.96/2.16  
% 5.96/2.18  tff(f_172, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 5.96/2.18  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.96/2.18  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 5.96/2.18  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_relat_1)).
% 5.96/2.18  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.96/2.18  tff(f_56, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 5.96/2.18  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.96/2.18  tff(f_98, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 5.96/2.18  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.96/2.18  tff(f_145, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.96/2.18  tff(f_155, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 5.96/2.18  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.96/2.18  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.96/2.18  tff(f_32, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.96/2.18  tff(f_127, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 5.96/2.18  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.96/2.18  tff(c_207, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.96/2.18  tff(c_215, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_207])).
% 5.96/2.18  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.96/2.18  tff(c_70, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.96/2.18  tff(c_229, plain, (![A_65]: (k4_relat_1(A_65)=k2_funct_1(A_65) | ~v2_funct_1(A_65) | ~v1_funct_1(A_65) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.96/2.18  tff(c_235, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_229])).
% 5.96/2.18  tff(c_239, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_76, c_235])).
% 5.96/2.18  tff(c_14, plain, (![A_7]: (v1_xboole_0(k4_relat_1(A_7)) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.96/2.18  tff(c_249, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_239, c_14])).
% 5.96/2.18  tff(c_257, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_249])).
% 5.96/2.18  tff(c_68, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.96/2.18  tff(c_385, plain, (![A_78, B_79, C_80]: (k2_relset_1(A_78, B_79, C_80)=k2_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.96/2.18  tff(c_388, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_385])).
% 5.96/2.18  tff(c_394, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_388])).
% 5.96/2.18  tff(c_16, plain, (![A_8]: (~v1_xboole_0(k2_relat_1(A_8)) | ~v1_relat_1(A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.96/2.18  tff(c_403, plain, (~v1_xboole_0('#skF_2') | ~v1_relat_1('#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_394, c_16])).
% 5.96/2.18  tff(c_409, plain, (~v1_xboole_0('#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_403])).
% 5.96/2.18  tff(c_410, plain, (~v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_257, c_409])).
% 5.96/2.18  tff(c_180, plain, (![A_45]: (v1_funct_1(k2_funct_1(A_45)) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.96/2.18  tff(c_66, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.96/2.18  tff(c_178, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_66])).
% 5.96/2.18  tff(c_183, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_180, c_178])).
% 5.96/2.18  tff(c_186, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_183])).
% 5.96/2.18  tff(c_189, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.96/2.18  tff(c_192, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_189])).
% 5.96/2.18  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_192])).
% 5.96/2.18  tff(c_201, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_66])).
% 5.96/2.18  tff(c_204, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_201])).
% 5.96/2.18  tff(c_34, plain, (![A_13]: (k1_relat_1(k2_funct_1(A_13))=k2_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.96/2.18  tff(c_30, plain, (![A_12]: (v1_relat_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.96/2.18  tff(c_202, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_66])).
% 5.96/2.18  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_172])).
% 5.96/2.18  tff(c_364, plain, (![A_73, B_74, C_75]: (k1_relset_1(A_73, B_74, C_75)=k1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.96/2.18  tff(c_372, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_364])).
% 5.96/2.19  tff(c_920, plain, (![B_116, A_117, C_118]: (k1_xboole_0=B_116 | k1_relset_1(A_117, B_116, C_118)=A_117 | ~v1_funct_2(C_118, A_117, B_116) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_117, B_116))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.96/2.19  tff(c_929, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_920])).
% 5.96/2.19  tff(c_940, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_372, c_929])).
% 5.96/2.19  tff(c_943, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_940])).
% 5.96/2.19  tff(c_258, plain, (![A_66]: (k2_relat_1(k2_funct_1(A_66))=k1_relat_1(A_66) | ~v2_funct_1(A_66) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.96/2.19  tff(c_62, plain, (![A_33]: (v1_funct_2(A_33, k1_relat_1(A_33), k2_relat_1(A_33)) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.96/2.19  tff(c_1630, plain, (![A_136]: (v1_funct_2(k2_funct_1(A_136), k1_relat_1(k2_funct_1(A_136)), k1_relat_1(A_136)) | ~v1_funct_1(k2_funct_1(A_136)) | ~v1_relat_1(k2_funct_1(A_136)) | ~v2_funct_1(A_136) | ~v1_funct_1(A_136) | ~v1_relat_1(A_136))), inference(superposition, [status(thm), theory('equality')], [c_258, c_62])).
% 5.96/2.19  tff(c_1657, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_943, c_1630])).
% 5.96/2.19  tff(c_1678, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_76, c_70, c_202, c_1657])).
% 5.96/2.19  tff(c_1685, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1678])).
% 5.96/2.19  tff(c_1688, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_1685])).
% 5.96/2.19  tff(c_1692, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_215, c_76, c_1688])).
% 5.96/2.19  tff(c_1694, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1678])).
% 5.96/2.19  tff(c_32, plain, (![A_13]: (k2_relat_1(k2_funct_1(A_13))=k1_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.96/2.19  tff(c_412, plain, (![A_81]: (m1_subset_1(A_81, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_81), k2_relat_1(A_81)))) | ~v1_funct_1(A_81) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.96/2.19  tff(c_2136, plain, (![A_146]: (m1_subset_1(k2_funct_1(A_146), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_146)), k1_relat_1(A_146)))) | ~v1_funct_1(k2_funct_1(A_146)) | ~v1_relat_1(k2_funct_1(A_146)) | ~v2_funct_1(A_146) | ~v1_funct_1(A_146) | ~v1_relat_1(A_146))), inference(superposition, [status(thm), theory('equality')], [c_32, c_412])).
% 5.96/2.19  tff(c_2180, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_943, c_2136])).
% 5.96/2.19  tff(c_2211, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_76, c_70, c_1694, c_202, c_2180])).
% 5.96/2.19  tff(c_2243, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_2211])).
% 5.96/2.19  tff(c_2259, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_76, c_70, c_394, c_2243])).
% 5.96/2.19  tff(c_2261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_204, c_2259])).
% 5.96/2.19  tff(c_2262, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_940])).
% 5.96/2.19  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.96/2.19  tff(c_2288, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2262, c_2])).
% 5.96/2.19  tff(c_2290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_410, c_2288])).
% 5.96/2.19  tff(c_2292, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_249])).
% 5.96/2.19  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.96/2.19  tff(c_2310, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2292, c_4])).
% 5.96/2.19  tff(c_6, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.96/2.19  tff(c_2319, plain, (![A_2]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2310, c_6])).
% 5.96/2.19  tff(c_101, plain, (![A_39]: (v1_xboole_0(k4_relat_1(A_39)) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.96/2.19  tff(c_113, plain, (![A_39]: (k4_relat_1(A_39)=k1_xboole_0 | ~v1_xboole_0(A_39))), inference(resolution, [status(thm)], [c_101, c_4])).
% 5.96/2.19  tff(c_2305, plain, (k4_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_2292, c_113])).
% 5.96/2.19  tff(c_2340, plain, (k4_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2310, c_2305])).
% 5.96/2.19  tff(c_2341, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2340, c_239])).
% 5.96/2.19  tff(c_2364, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2341, c_204])).
% 5.96/2.19  tff(c_2499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2319, c_2364])).
% 5.96/2.19  tff(c_2500, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_201])).
% 5.96/2.19  tff(c_2504, plain, (![C_161, A_162, B_163]: (v1_relat_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.96/2.19  tff(c_2516, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_2504])).
% 5.96/2.19  tff(c_3576, plain, (![A_240, B_241, C_242]: (k2_relset_1(A_240, B_241, C_242)=k2_relat_1(C_242) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.96/2.19  tff(c_3586, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_3576])).
% 5.96/2.19  tff(c_3591, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3586])).
% 5.96/2.19  tff(c_2501, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_201])).
% 5.96/2.19  tff(c_2515, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2501, c_2504])).
% 5.96/2.19  tff(c_2575, plain, (![C_175, A_176, B_177]: (v1_partfun1(C_175, A_176) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))) | ~v1_xboole_0(A_176))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.96/2.19  tff(c_2587, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_72, c_2575])).
% 5.96/2.19  tff(c_2604, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_2587])).
% 5.96/2.19  tff(c_2731, plain, (![A_187, B_188, C_189]: (k2_relset_1(A_187, B_188, C_189)=k2_relat_1(C_189) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_187, B_188))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.96/2.19  tff(c_2740, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_2731])).
% 5.96/2.19  tff(c_2748, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2740])).
% 5.96/2.19  tff(c_2698, plain, (![A_182, B_183, C_184]: (k1_relset_1(A_182, B_183, C_184)=k1_relat_1(C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.96/2.19  tff(c_2713, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2501, c_2698])).
% 5.96/2.19  tff(c_3243, plain, (![B_222, C_223, A_224]: (k1_xboole_0=B_222 | v1_funct_2(C_223, A_224, B_222) | k1_relset_1(A_224, B_222, C_223)!=A_224 | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_224, B_222))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.96/2.19  tff(c_3252, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_2501, c_3243])).
% 5.96/2.19  tff(c_3265, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2713, c_3252])).
% 5.96/2.19  tff(c_3266, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_2500, c_3265])).
% 5.96/2.19  tff(c_3292, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_3266])).
% 5.96/2.19  tff(c_3295, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_3292])).
% 5.96/2.19  tff(c_3298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2516, c_76, c_70, c_2748, c_3295])).
% 5.96/2.19  tff(c_3299, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_3266])).
% 5.96/2.19  tff(c_3352, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3299, c_2])).
% 5.96/2.19  tff(c_3354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2604, c_3352])).
% 5.96/2.19  tff(c_3356, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_2587])).
% 5.96/2.19  tff(c_3673, plain, (![A_246, B_247, C_248]: (k1_relset_1(A_246, B_247, C_248)=k1_relat_1(C_248) | ~m1_subset_1(C_248, k1_zfmisc_1(k2_zfmisc_1(A_246, B_247))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.96/2.19  tff(c_3694, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_3673])).
% 5.96/2.19  tff(c_3376, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_3356, c_4])).
% 5.96/2.19  tff(c_56, plain, (![B_31, C_32]: (k1_relset_1(k1_xboole_0, B_31, C_32)=k1_xboole_0 | ~v1_funct_2(C_32, k1_xboole_0, B_31) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_31))))), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.96/2.19  tff(c_3983, plain, (![B_268, C_269]: (k1_relset_1('#skF_1', B_268, C_269)='#skF_1' | ~v1_funct_2(C_269, '#skF_1', B_268) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_268))))), inference(demodulation, [status(thm), theory('equality')], [c_3376, c_3376, c_3376, c_3376, c_56])).
% 5.96/2.19  tff(c_3990, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_3983])).
% 5.96/2.19  tff(c_3995, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3694, c_3990])).
% 5.96/2.19  tff(c_3620, plain, (![A_245]: (m1_subset_1(A_245, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_245), k2_relat_1(A_245)))) | ~v1_funct_1(A_245) | ~v1_relat_1(A_245))), inference(cnfTransformation, [status(thm)], [f_155])).
% 5.96/2.19  tff(c_3634, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3591, c_3620])).
% 5.96/2.19  tff(c_3649, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2516, c_76, c_3634])).
% 5.96/2.19  tff(c_46, plain, (![C_29, A_26, B_27]: (v1_partfun1(C_29, A_26) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.96/2.19  tff(c_3665, plain, (v1_partfun1('#skF_3', k1_relat_1('#skF_3')) | ~v1_xboole_0(k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_3649, c_46])).
% 5.96/2.19  tff(c_3706, plain, (~v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3665])).
% 5.96/2.19  tff(c_3998, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3995, c_3706])).
% 5.96/2.19  tff(c_4005, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3356, c_3998])).
% 5.96/2.19  tff(c_4007, plain, (v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3665])).
% 5.96/2.19  tff(c_3387, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_3376, c_4])).
% 5.96/2.19  tff(c_4024, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_4007, c_3387])).
% 5.96/2.19  tff(c_3431, plain, (![A_230]: (k2_relat_1(k2_funct_1(A_230))=k1_relat_1(A_230) | ~v2_funct_1(A_230) | ~v1_funct_1(A_230) | ~v1_relat_1(A_230))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.96/2.19  tff(c_4772, plain, (![A_310]: (v1_funct_2(k2_funct_1(A_310), k1_relat_1(k2_funct_1(A_310)), k1_relat_1(A_310)) | ~v1_funct_1(k2_funct_1(A_310)) | ~v1_relat_1(k2_funct_1(A_310)) | ~v2_funct_1(A_310) | ~v1_funct_1(A_310) | ~v1_relat_1(A_310))), inference(superposition, [status(thm), theory('equality')], [c_3431, c_62])).
% 5.96/2.19  tff(c_4790, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4024, c_4772])).
% 5.96/2.19  tff(c_4808, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2516, c_76, c_70, c_2515, c_202, c_4790])).
% 5.96/2.19  tff(c_4815, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_4808])).
% 5.96/2.19  tff(c_4817, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2516, c_76, c_70, c_3591, c_4815])).
% 5.96/2.19  tff(c_4819, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2500, c_4817])).
% 5.96/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.96/2.19  
% 5.96/2.19  Inference rules
% 5.96/2.19  ----------------------
% 5.96/2.19  #Ref     : 0
% 5.96/2.19  #Sup     : 1051
% 5.96/2.19  #Fact    : 0
% 5.96/2.19  #Define  : 0
% 5.96/2.19  #Split   : 22
% 5.96/2.19  #Chain   : 0
% 5.96/2.19  #Close   : 0
% 5.96/2.19  
% 5.96/2.19  Ordering : KBO
% 5.96/2.19  
% 5.96/2.19  Simplification rules
% 5.96/2.19  ----------------------
% 5.96/2.19  #Subsume      : 135
% 5.96/2.19  #Demod        : 1566
% 5.96/2.19  #Tautology    : 578
% 5.96/2.19  #SimpNegUnit  : 16
% 5.96/2.19  #BackRed      : 107
% 5.96/2.19  
% 5.96/2.19  #Partial instantiations: 0
% 5.96/2.19  #Strategies tried      : 1
% 5.96/2.19  
% 5.96/2.19  Timing (in seconds)
% 5.96/2.19  ----------------------
% 5.96/2.19  Preprocessing        : 0.37
% 5.96/2.19  Parsing              : 0.20
% 5.96/2.19  CNF conversion       : 0.02
% 5.96/2.19  Main loop            : 0.99
% 5.96/2.19  Inferencing          : 0.34
% 5.96/2.19  Reduction            : 0.34
% 5.96/2.19  Demodulation         : 0.25
% 5.96/2.19  BG Simplification    : 0.04
% 5.96/2.19  Subsumption          : 0.18
% 5.96/2.19  Abstraction          : 0.04
% 5.96/2.19  MUC search           : 0.00
% 5.96/2.19  Cooper               : 0.00
% 5.96/2.19  Total                : 1.41
% 5.96/2.19  Index Insertion      : 0.00
% 5.96/2.19  Index Deletion       : 0.00
% 5.96/2.19  Index Matching       : 0.00
% 5.96/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
