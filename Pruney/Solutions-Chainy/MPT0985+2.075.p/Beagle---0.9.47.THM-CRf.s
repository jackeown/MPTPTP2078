%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:38 EST 2020

% Result     : Theorem 10.14s
% Output     : CNFRefutation 10.71s
% Verified   : 
% Statistics : Number of formulae       :  379 (4496 expanded)
%              Number of leaves         :   37 (1367 expanded)
%              Depth                    :   17
%              Number of atoms          :  685 (11817 expanded)
%              Number of equality atoms :  219 (4393 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_142,negated_conjecture,(
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

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

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

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_125,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_52,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_192,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_205,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_192])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_70,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_68,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_16209,plain,(
    ! [A_1165,B_1166,C_1167] :
      ( k2_relset_1(A_1165,B_1166,C_1167) = k2_relat_1(C_1167)
      | ~ m1_subset_1(C_1167,k1_zfmisc_1(k2_zfmisc_1(A_1165,B_1166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_16219,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_16209])).

tff(c_16228,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_16219])).

tff(c_36,plain,(
    ! [A_15] :
      ( k1_relat_1(k2_funct_1(A_15)) = k2_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_30,plain,(
    ! [A_14] :
      ( v1_funct_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_146,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_149,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_146])).

tff(c_152,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_149])).

tff(c_163,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_170,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_163])).

tff(c_179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_170])).

tff(c_180,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_212,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_74,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_858,plain,(
    ! [A_131,B_132,C_133] :
      ( k1_relset_1(A_131,B_132,C_133) = k1_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_873,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_858])).

tff(c_4391,plain,(
    ! [B_345,A_346,C_347] :
      ( k1_xboole_0 = B_345
      | k1_relset_1(A_346,B_345,C_347) = A_346
      | ~ v1_funct_2(C_347,A_346,B_345)
      | ~ m1_subset_1(C_347,k1_zfmisc_1(k2_zfmisc_1(A_346,B_345))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4404,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_4391])).

tff(c_4415,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_873,c_4404])).

tff(c_4417,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4415])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_223,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_212])).

tff(c_1442,plain,(
    ! [B_188,A_189,C_190] :
      ( k1_xboole_0 = B_188
      | k1_relset_1(A_189,B_188,C_190) = A_189
      | ~ v1_funct_2(C_190,A_189,B_188)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_189,B_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1455,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_1442])).

tff(c_1469,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_873,c_1455])).

tff(c_1471,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1469])).

tff(c_34,plain,(
    ! [A_15] :
      ( k2_relat_1(k2_funct_1(A_15)) = k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    ! [A_14] :
      ( v1_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_981,plain,(
    ! [A_148,B_149,C_150] :
      ( k2_relset_1(A_148,B_149,C_150) = k2_relat_1(C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_988,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_981])).

tff(c_997,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_988])).

tff(c_701,plain,(
    ! [A_115] :
      ( k1_relat_1(k2_funct_1(A_115)) = k2_relat_1(A_115)
      | ~ v2_funct_1(A_115)
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_240,plain,(
    ! [B_60,A_61] :
      ( v4_relat_1(B_60,A_61)
      | ~ r1_tarski(k1_relat_1(B_60),A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_250,plain,(
    ! [B_60] :
      ( v4_relat_1(B_60,k1_relat_1(B_60))
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_6,c_240])).

tff(c_3095,plain,(
    ! [A_291] :
      ( v4_relat_1(k2_funct_1(A_291),k2_relat_1(A_291))
      | ~ v1_relat_1(k2_funct_1(A_291))
      | ~ v2_funct_1(A_291)
      | ~ v1_funct_1(A_291)
      | ~ v1_relat_1(A_291) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_701,c_250])).

tff(c_3100,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_997,c_3095])).

tff(c_3109,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_76,c_70,c_3100])).

tff(c_3132,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3109])).

tff(c_3135,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_3132])).

tff(c_3139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_76,c_3135])).

tff(c_3141,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3109])).

tff(c_181,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_3140,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_3109])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_relat_1(B_8),A_7)
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3112,plain,(
    ! [A_292,A_293] :
      ( r1_tarski(k2_relat_1(A_292),A_293)
      | ~ v4_relat_1(k2_funct_1(A_292),A_293)
      | ~ v1_relat_1(k2_funct_1(A_292))
      | ~ v2_funct_1(A_292)
      | ~ v1_funct_1(A_292)
      | ~ v1_relat_1(A_292) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_701,c_20])).

tff(c_3564,plain,(
    ! [A_317] :
      ( r1_tarski(k2_relat_1(A_317),k1_relat_1(k2_funct_1(A_317)))
      | ~ v2_funct_1(A_317)
      | ~ v1_funct_1(A_317)
      | ~ v1_relat_1(A_317)
      | ~ v1_relat_1(k2_funct_1(A_317)) ) ),
    inference(resolution,[status(thm)],[c_250,c_3112])).

tff(c_3575,plain,
    ( r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_997,c_3564])).

tff(c_3589,plain,(
    r1_tarski('#skF_2',k1_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3141,c_205,c_76,c_70,c_3575])).

tff(c_304,plain,(
    ! [B_76,A_77] :
      ( r1_tarski(k1_relat_1(B_76),A_77)
      | ~ v4_relat_1(B_76,A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_324,plain,(
    ! [B_76,A_77] :
      ( k1_relat_1(B_76) = A_77
      | ~ r1_tarski(A_77,k1_relat_1(B_76))
      | ~ v4_relat_1(B_76,A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_304,c_2])).

tff(c_3595,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3589,c_324])).

tff(c_3606,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3141,c_3140,c_3595])).

tff(c_1038,plain,(
    ! [A_156] :
      ( m1_subset_1(A_156,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_156),k2_relat_1(A_156))))
      | ~ v1_funct_1(A_156)
      | ~ v1_relat_1(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1083,plain,(
    ! [A_156] :
      ( r1_tarski(A_156,k2_zfmisc_1(k1_relat_1(A_156),k2_relat_1(A_156)))
      | ~ v1_funct_1(A_156)
      | ~ v1_relat_1(A_156) ) ),
    inference(resolution,[status(thm)],[c_1038,c_14])).

tff(c_3714,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3606,c_1083])).

tff(c_3795,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3141,c_181,c_3714])).

tff(c_3961,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3795])).

tff(c_3980,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_76,c_70,c_1471,c_3961])).

tff(c_3982,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_3980])).

tff(c_3983,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1469])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_259,plain,(
    ! [C_64,A_65,B_66] :
      ( v4_relat_1(C_64,A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_298,plain,(
    ! [C_72,A_73] :
      ( v4_relat_1(C_72,A_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_259])).

tff(c_302,plain,(
    ! [A_5,A_73] :
      ( v4_relat_1(A_5,A_73)
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_298])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_113,plain,(
    ! [A_35,B_36] : v1_relat_1(k2_zfmisc_1(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_115,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_113])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_320,plain,(
    ! [A_77] :
      ( r1_tarski(k1_xboole_0,A_77)
      | ~ v4_relat_1(k1_xboole_0,A_77)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_304])).

tff(c_327,plain,(
    ! [A_78] :
      ( r1_tarski(k1_xboole_0,A_78)
      | ~ v4_relat_1(k1_xboole_0,A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_320])).

tff(c_331,plain,(
    ! [A_73] :
      ( r1_tarski(k1_xboole_0,A_73)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_302,c_327])).

tff(c_344,plain,(
    ! [A_73] : r1_tarski(k1_xboole_0,A_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_331])).

tff(c_4012,plain,(
    ! [A_73] : r1_tarski('#skF_2',A_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3983,c_344])).

tff(c_4020,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3983,c_3983,c_10])).

tff(c_1062,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_997,c_1038])).

tff(c_1085,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_76,c_1062])).

tff(c_1122,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_1085,c_14])).

tff(c_1146,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1122,c_2])).

tff(c_1262,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1146])).

tff(c_4149,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4020,c_1262])).

tff(c_4157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4012,c_4149])).

tff(c_4158,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1146])).

tff(c_4420,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4417,c_4158])).

tff(c_124,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_132,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_124])).

tff(c_182,plain,(
    ! [B_50,A_51] :
      ( B_50 = A_51
      | ~ r1_tarski(B_50,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_187,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_132,c_182])).

tff(c_258,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_4478,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4420,c_258])).

tff(c_4483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4478])).

tff(c_4484,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4415])).

tff(c_4515,plain,(
    ! [A_73] : r1_tarski('#skF_2',A_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4484,c_344])).

tff(c_4523,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4484,c_4484,c_10])).

tff(c_4746,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4523,c_258])).

tff(c_4751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4515,c_4746])).

tff(c_4752,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_4755,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4752,c_72])).

tff(c_5368,plain,(
    ! [A_425,B_426,C_427] :
      ( k1_relset_1(A_425,B_426,C_427) = k1_relat_1(C_427)
      | ~ m1_subset_1(C_427,k1_zfmisc_1(k2_zfmisc_1(A_425,B_426))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_5539,plain,(
    ! [C_449] :
      ( k1_relset_1('#skF_1','#skF_2',C_449) = k1_relat_1(C_449)
      | ~ m1_subset_1(C_449,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4752,c_5368])).

tff(c_5547,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4755,c_5539])).

tff(c_6188,plain,(
    ! [B_502,C_503,A_504] :
      ( k1_xboole_0 = B_502
      | v1_funct_2(C_503,A_504,B_502)
      | k1_relset_1(A_504,B_502,C_503) != A_504
      | ~ m1_subset_1(C_503,k1_zfmisc_1(k2_zfmisc_1(A_504,B_502))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6197,plain,(
    ! [C_503] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_503,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_503) != '#skF_1'
      | ~ m1_subset_1(C_503,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4752,c_6188])).

tff(c_6232,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_6197])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4764,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4752,c_8])).

tff(c_4784,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4764])).

tff(c_6268,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6232,c_4784])).

tff(c_6608,plain,(
    ! [A_517] : k2_zfmisc_1(A_517,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6232,c_6232,c_10])).

tff(c_6700,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_6608,c_4752])).

tff(c_6736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6268,c_6700])).

tff(c_6738,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_6197])).

tff(c_6814,plain,(
    ! [B_528,A_529,C_530] :
      ( k1_xboole_0 = B_528
      | k1_relset_1(A_529,B_528,C_530) = A_529
      | ~ v1_funct_2(C_530,A_529,B_528)
      | ~ m1_subset_1(C_530,k1_zfmisc_1(k2_zfmisc_1(A_529,B_528))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6823,plain,(
    ! [C_530] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_530) = '#skF_1'
      | ~ v1_funct_2(C_530,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_530,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4752,c_6814])).

tff(c_7428,plain,(
    ! [C_566] :
      ( k1_relset_1('#skF_1','#skF_2',C_566) = '#skF_1'
      | ~ v1_funct_2(C_566,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_566,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6738,c_6823])).

tff(c_7431,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4755,c_7428])).

tff(c_7438,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5547,c_7431])).

tff(c_5493,plain,(
    ! [A_441,B_442,C_443] :
      ( k2_relset_1(A_441,B_442,C_443) = k2_relat_1(C_443)
      | ~ m1_subset_1(C_443,k1_zfmisc_1(k2_zfmisc_1(A_441,B_442))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5642,plain,(
    ! [C_460] :
      ( k2_relset_1('#skF_1','#skF_2',C_460) = k2_relat_1(C_460)
      | ~ m1_subset_1(C_460,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4752,c_5493])).

tff(c_5645,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4755,c_5642])).

tff(c_5651,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_5645])).

tff(c_4841,plain,(
    ! [C_361,A_362,B_363] :
      ( v4_relat_1(C_361,A_362)
      | ~ m1_subset_1(C_361,k1_zfmisc_1(k2_zfmisc_1(A_362,B_363))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_5045,plain,(
    ! [A_392,A_393,B_394] :
      ( v4_relat_1(A_392,A_393)
      | ~ r1_tarski(A_392,k2_zfmisc_1(A_393,B_394)) ) ),
    inference(resolution,[status(thm)],[c_16,c_4841])).

tff(c_5304,plain,(
    ! [B_418,A_419,B_420] :
      ( v4_relat_1(k1_relat_1(B_418),A_419)
      | ~ v4_relat_1(B_418,k2_zfmisc_1(A_419,B_420))
      | ~ v1_relat_1(B_418) ) ),
    inference(resolution,[status(thm)],[c_20,c_5045])).

tff(c_5429,plain,(
    ! [B_432] :
      ( v4_relat_1(k1_relat_1(B_432),'#skF_1')
      | ~ v4_relat_1(B_432,'#skF_3')
      | ~ v1_relat_1(B_432) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4752,c_5304])).

tff(c_5799,plain,(
    ! [A_469] :
      ( v4_relat_1(k2_relat_1(A_469),'#skF_1')
      | ~ v4_relat_1(k2_funct_1(A_469),'#skF_3')
      | ~ v1_relat_1(k2_funct_1(A_469))
      | ~ v2_funct_1(A_469)
      | ~ v1_funct_1(A_469)
      | ~ v1_relat_1(A_469) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_5429])).

tff(c_5802,plain,
    ( v4_relat_1('#skF_2','#skF_1')
    | ~ v4_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5651,c_5799])).

tff(c_5810,plain,
    ( v4_relat_1('#skF_2','#skF_1')
    | ~ v4_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_76,c_70,c_5802])).

tff(c_5855,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5810])).

tff(c_5858,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_5855])).

tff(c_5862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_76,c_5858])).

tff(c_5864,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5810])).

tff(c_5710,plain,(
    ! [A_468] :
      ( m1_subset_1(A_468,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_468),k2_relat_1(A_468))))
      | ~ v1_funct_1(A_468)
      | ~ v1_relat_1(A_468) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_10101,plain,(
    ! [A_665] :
      ( m1_subset_1(k2_funct_1(A_665),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_665),k2_relat_1(k2_funct_1(A_665)))))
      | ~ v1_funct_1(k2_funct_1(A_665))
      | ~ v1_relat_1(k2_funct_1(A_665))
      | ~ v2_funct_1(A_665)
      | ~ v1_funct_1(A_665)
      | ~ v1_relat_1(A_665) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_5710])).

tff(c_10131,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5651,c_10101])).

tff(c_10153,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_76,c_70,c_5864,c_181,c_10131])).

tff(c_10185,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_10153])).

tff(c_10203,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_76,c_70,c_7438,c_10185])).

tff(c_10205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_10203])).

tff(c_10207,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4764])).

tff(c_10214,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10207,c_10207,c_12])).

tff(c_10206,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4764])).

tff(c_10252,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10207,c_10207,c_10206])).

tff(c_10253,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_10252])).

tff(c_10255,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10253,c_223])).

tff(c_10328,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10214,c_10255])).

tff(c_10217,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10207,c_10207,c_26])).

tff(c_10648,plain,(
    ! [A_720] :
      ( k2_relat_1(k2_funct_1(A_720)) = k1_relat_1(A_720)
      | ~ v2_funct_1(A_720)
      | ~ v1_funct_1(A_720)
      | ~ v1_relat_1(A_720) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_62,plain,(
    ! [A_31] :
      ( v1_funct_2(A_31,k1_relat_1(A_31),k2_relat_1(A_31))
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_12327,plain,(
    ! [A_861] :
      ( v1_funct_2(k2_funct_1(A_861),k1_relat_1(k2_funct_1(A_861)),k1_relat_1(A_861))
      | ~ v1_funct_1(k2_funct_1(A_861))
      | ~ v1_relat_1(k2_funct_1(A_861))
      | ~ v2_funct_1(A_861)
      | ~ v1_funct_1(A_861)
      | ~ v1_relat_1(A_861) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10648,c_62])).

tff(c_12342,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10217,c_12327])).

tff(c_12344,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_76,c_70,c_181,c_12342])).

tff(c_12345,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_12344])).

tff(c_12348,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_12345])).

tff(c_12352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_76,c_12348])).

tff(c_12354,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_12344])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10216,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10207,c_10207,c_24])).

tff(c_10666,plain,(
    ! [A_722] :
      ( k1_relat_1(k2_funct_1(A_722)) = k2_relat_1(A_722)
      | ~ v2_funct_1(A_722)
      | ~ v1_funct_1(A_722)
      | ~ v1_relat_1(A_722) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12405,plain,(
    ! [A_863] :
      ( v4_relat_1(k2_funct_1(A_863),k2_relat_1(A_863))
      | ~ v1_relat_1(k2_funct_1(A_863))
      | ~ v2_funct_1(A_863)
      | ~ v1_funct_1(A_863)
      | ~ v1_relat_1(A_863) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10666,c_250])).

tff(c_12416,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10216,c_12405])).

tff(c_12421,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_76,c_70,c_12354,c_12416])).

tff(c_10215,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10207,c_10207,c_10])).

tff(c_10416,plain,(
    ! [C_689,A_690,B_691] :
      ( v4_relat_1(C_689,A_690)
      | ~ m1_subset_1(C_689,k1_zfmisc_1(k2_zfmisc_1(A_690,B_691))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_10447,plain,(
    ! [C_694,A_695] :
      ( v4_relat_1(C_694,A_695)
      | ~ m1_subset_1(C_694,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10215,c_10416])).

tff(c_10453,plain,(
    ! [A_695] : v4_relat_1('#skF_3',A_695) ),
    inference(resolution,[status(thm)],[c_4755,c_10447])).

tff(c_10277,plain,(
    ! [B_668,A_669] :
      ( r1_tarski(k1_relat_1(B_668),A_669)
      | ~ v4_relat_1(B_668,A_669)
      | ~ v1_relat_1(B_668) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10293,plain,(
    ! [A_669] :
      ( r1_tarski('#skF_3',A_669)
      | ~ v4_relat_1('#skF_3',A_669)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10217,c_10277])).

tff(c_10299,plain,(
    ! [A_669] :
      ( r1_tarski('#skF_3',A_669)
      | ~ v4_relat_1('#skF_3',A_669) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_10293])).

tff(c_10460,plain,(
    ! [A_697] : r1_tarski('#skF_3',A_697) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10453,c_10299])).

tff(c_10482,plain,(
    ! [A_698] :
      ( A_698 = '#skF_3'
      | ~ r1_tarski(A_698,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10460,c_2])).

tff(c_10497,plain,(
    ! [B_8] :
      ( k1_relat_1(B_8) = '#skF_3'
      | ~ v4_relat_1(B_8,'#skF_3')
      | ~ v1_relat_1(B_8) ) ),
    inference(resolution,[status(thm)],[c_20,c_10482])).

tff(c_12435,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12421,c_10497])).

tff(c_12450,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12354,c_12435])).

tff(c_10826,plain,(
    ! [A_739] :
      ( m1_subset_1(A_739,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_739),k2_relat_1(A_739))))
      | ~ v1_funct_1(A_739)
      | ~ v1_relat_1(A_739) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_10860,plain,(
    ! [A_739] :
      ( r1_tarski(A_739,k2_zfmisc_1(k1_relat_1(A_739),k2_relat_1(A_739)))
      | ~ v1_funct_1(A_739)
      | ~ v1_relat_1(A_739) ) ),
    inference(resolution,[status(thm)],[c_10826,c_14])).

tff(c_12541,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12450,c_10860])).

tff(c_12622,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12354,c_181,c_10214,c_12541])).

tff(c_12624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10328,c_12622])).

tff(c_12625,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_10252])).

tff(c_12626,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10252])).

tff(c_12647,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12625,c_12626])).

tff(c_12628,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12625,c_12625,c_10216])).

tff(c_12633,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12625,c_12625,c_4755])).

tff(c_12696,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12625,c_12625,c_10214])).

tff(c_13137,plain,(
    ! [A_923,B_924,C_925] :
      ( k2_relset_1(A_923,B_924,C_925) = k2_relat_1(C_925)
      | ~ m1_subset_1(C_925,k1_zfmisc_1(k2_zfmisc_1(A_923,B_924))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_13185,plain,(
    ! [B_932,C_933] :
      ( k2_relset_1('#skF_1',B_932,C_933) = k2_relat_1(C_933)
      | ~ m1_subset_1(C_933,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12696,c_13137])).

tff(c_13187,plain,(
    ! [B_932] : k2_relset_1('#skF_1',B_932,'#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12633,c_13185])).

tff(c_13192,plain,(
    ! [B_932] : k2_relset_1('#skF_1',B_932,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12628,c_13187])).

tff(c_12639,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12625,c_68])).

tff(c_13194,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13192,c_12639])).

tff(c_13196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12647,c_13194])).

tff(c_13197,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_13934,plain,(
    ! [A_1011,B_1012,C_1013] :
      ( k2_relset_1(A_1011,B_1012,C_1013) = k2_relat_1(C_1013)
      | ~ m1_subset_1(C_1013,k1_zfmisc_1(k2_zfmisc_1(A_1011,B_1012))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_13944,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_13934])).

tff(c_13954,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_13944])).

tff(c_13198,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_13807,plain,(
    ! [A_996,B_997,C_998] :
      ( k1_relset_1(A_996,B_997,C_998) = k1_relat_1(C_998)
      | ~ m1_subset_1(C_998,k1_zfmisc_1(k2_zfmisc_1(A_996,B_997))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_13824,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_13198,c_13807])).

tff(c_15086,plain,(
    ! [B_1075,C_1076,A_1077] :
      ( k1_xboole_0 = B_1075
      | v1_funct_2(C_1076,A_1077,B_1075)
      | k1_relset_1(A_1077,B_1075,C_1076) != A_1077
      | ~ m1_subset_1(C_1076,k1_zfmisc_1(k2_zfmisc_1(A_1077,B_1075))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_15095,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_13198,c_15086])).

tff(c_15111,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13824,c_15095])).

tff(c_15112,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_13197,c_15111])).

tff(c_15117,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_15112])).

tff(c_15120,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_15117])).

tff(c_15123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_76,c_70,c_13954,c_15120])).

tff(c_15124,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_15112])).

tff(c_13303,plain,(
    ! [C_946,A_947,B_948] :
      ( v4_relat_1(C_946,A_947)
      | ~ m1_subset_1(C_946,k1_zfmisc_1(k2_zfmisc_1(A_947,B_948))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_13323,plain,(
    ! [C_949,A_950] :
      ( v4_relat_1(C_949,A_950)
      | ~ m1_subset_1(C_949,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_13303])).

tff(c_13328,plain,(
    ! [A_951,A_952] :
      ( v4_relat_1(A_951,A_952)
      | ~ r1_tarski(A_951,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_13323])).

tff(c_13257,plain,(
    ! [B_942,A_943] :
      ( r1_tarski(k1_relat_1(B_942),A_943)
      | ~ v4_relat_1(B_942,A_943)
      | ~ v1_relat_1(B_942) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_13273,plain,(
    ! [A_943] :
      ( r1_tarski(k1_xboole_0,A_943)
      | ~ v4_relat_1(k1_xboole_0,A_943)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_13257])).

tff(c_13279,plain,(
    ! [A_943] :
      ( r1_tarski(k1_xboole_0,A_943)
      | ~ v4_relat_1(k1_xboole_0,A_943) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_13273])).

tff(c_13332,plain,(
    ! [A_952] :
      ( r1_tarski(k1_xboole_0,A_952)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_13328,c_13279])).

tff(c_13335,plain,(
    ! [A_952] : r1_tarski(k1_xboole_0,A_952) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13332])).

tff(c_15154,plain,(
    ! [A_952] : r1_tarski('#skF_1',A_952) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15124,c_13335])).

tff(c_15163,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15124,c_15124,c_10])).

tff(c_13213,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_13198,c_14])).

tff(c_13216,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_13213,c_2])).

tff(c_13395,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_13216])).

tff(c_15360,plain,(
    ~ r1_tarski('#skF_1',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15163,c_13395])).

tff(c_15365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15154,c_15360])).

tff(c_15366,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_13216])).

tff(c_15369,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15366,c_13198])).

tff(c_16673,plain,(
    ! [A_1199,B_1200,C_1201] :
      ( k1_relset_1(A_1199,B_1200,C_1201) = k1_relat_1(C_1201)
      | ~ m1_subset_1(C_1201,k1_zfmisc_1(k2_zfmisc_1(A_1199,B_1200))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_16721,plain,(
    ! [C_1203] :
      ( k1_relset_1('#skF_2','#skF_1',C_1203) = k1_relat_1(C_1203)
      | ~ m1_subset_1(C_1203,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15366,c_16673])).

tff(c_16729,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_15369,c_16721])).

tff(c_17129,plain,(
    ! [B_1251,C_1252,A_1253] :
      ( k1_xboole_0 = B_1251
      | v1_funct_2(C_1252,A_1253,B_1251)
      | k1_relset_1(A_1253,B_1251,C_1252) != A_1253
      | ~ m1_subset_1(C_1252,k1_zfmisc_1(k2_zfmisc_1(A_1253,B_1251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_17138,plain,(
    ! [C_1252] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2(C_1252,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',C_1252) != '#skF_2'
      | ~ m1_subset_1(C_1252,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15366,c_17129])).

tff(c_17252,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_17138])).

tff(c_15384,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_15366,c_8])).

tff(c_15432,plain,(
    k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_15384])).

tff(c_17283,plain,(
    k2_funct_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17252,c_15432])).

tff(c_17295,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17252,c_17252,c_10])).

tff(c_17639,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17295,c_15366])).

tff(c_17641,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17283,c_17639])).

tff(c_17644,plain,(
    ! [C_1268] :
      ( v1_funct_2(C_1268,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',C_1268) != '#skF_2'
      | ~ m1_subset_1(C_1268,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_17138])).

tff(c_17647,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_15369,c_17644])).

tff(c_17653,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16729,c_17647])).

tff(c_17654,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_13197,c_17653])).

tff(c_17658,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_17654])).

tff(c_17661,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_76,c_70,c_16228,c_17658])).

tff(c_17662,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_15384])).

tff(c_17742,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_17662])).

tff(c_17751,plain,(
    ! [A_952] : r1_tarski('#skF_1',A_952) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17742,c_13335])).

tff(c_17759,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17742,c_17742,c_12])).

tff(c_13238,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_18012,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17759,c_13238])).

tff(c_18017,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17751,c_18012])).

tff(c_18018,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_17662])).

tff(c_18032,plain,(
    ! [A_952] : r1_tarski('#skF_2',A_952) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18018,c_13335])).

tff(c_18041,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18018,c_18018,c_10])).

tff(c_18250,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18041,c_13238])).

tff(c_18255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18032,c_18250])).

tff(c_18256,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_18259,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18256,c_72])).

tff(c_19169,plain,(
    ! [A_1388,B_1389,C_1390] :
      ( k2_relset_1(A_1388,B_1389,C_1390) = k2_relat_1(C_1390)
      | ~ m1_subset_1(C_1390,k1_zfmisc_1(k2_zfmisc_1(A_1388,B_1389))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_19208,plain,(
    ! [C_1394] :
      ( k2_relset_1('#skF_1','#skF_2',C_1394) = k2_relat_1(C_1394)
      | ~ m1_subset_1(C_1394,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18256,c_19169])).

tff(c_19211,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18259,c_19208])).

tff(c_19217,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_19211])).

tff(c_19403,plain,(
    ! [A_1401,B_1402,C_1403] :
      ( k1_relset_1(A_1401,B_1402,C_1403) = k1_relat_1(C_1403)
      | ~ m1_subset_1(C_1403,k1_zfmisc_1(k2_zfmisc_1(A_1401,B_1402))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_19428,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_13198,c_19403])).

tff(c_20507,plain,(
    ! [B_1472,C_1473,A_1474] :
      ( k1_xboole_0 = B_1472
      | v1_funct_2(C_1473,A_1474,B_1472)
      | k1_relset_1(A_1474,B_1472,C_1473) != A_1474
      | ~ m1_subset_1(C_1473,k1_zfmisc_1(k2_zfmisc_1(A_1474,B_1472))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_20519,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_13198,c_20507])).

tff(c_20537,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19428,c_20519])).

tff(c_20538,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_13197,c_20537])).

tff(c_20541,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_20538])).

tff(c_20544,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_20541])).

tff(c_20547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_76,c_70,c_19217,c_20544])).

tff(c_20548,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_20538])).

tff(c_18268,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_18256,c_8])).

tff(c_18324,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_18268])).

tff(c_20587,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20548,c_18324])).

tff(c_20592,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20548,c_20548,c_12])).

tff(c_20882,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20592,c_18256])).

tff(c_20884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20587,c_20882])).

tff(c_20886,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18268])).

tff(c_20895,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20886,c_20886,c_26])).

tff(c_20893,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20886,c_20886,c_10])).

tff(c_20994,plain,(
    ! [C_1484,A_1485,B_1486] :
      ( v4_relat_1(C_1484,A_1485)
      | ~ m1_subset_1(C_1484,k1_zfmisc_1(k2_zfmisc_1(A_1485,B_1486))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_21220,plain,(
    ! [C_1507,A_1508] :
      ( v4_relat_1(C_1507,A_1508)
      | ~ m1_subset_1(C_1507,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20893,c_20994])).

tff(c_21226,plain,(
    ! [A_1508] : v4_relat_1('#skF_3',A_1508) ),
    inference(resolution,[status(thm)],[c_18259,c_21220])).

tff(c_18288,plain,(
    ! [B_1287,A_1288] :
      ( r1_tarski(k1_relat_1(B_1287),A_1288)
      | ~ v4_relat_1(B_1287,A_1288)
      | ~ v1_relat_1(B_1287) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18305,plain,(
    ! [A_1288] :
      ( r1_tarski(k1_xboole_0,A_1288)
      | ~ v4_relat_1(k1_xboole_0,A_1288)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_18288])).

tff(c_18311,plain,(
    ! [A_1288] :
      ( r1_tarski(k1_xboole_0,A_1288)
      | ~ v4_relat_1(k1_xboole_0,A_1288) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_18305])).

tff(c_20887,plain,(
    ! [A_1288] :
      ( r1_tarski('#skF_3',A_1288)
      | ~ v4_relat_1('#skF_3',A_1288) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20886,c_20886,c_18311])).

tff(c_21231,plain,(
    ! [A_1288] : r1_tarski('#skF_3',A_1288) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21226,c_20887])).

tff(c_21908,plain,(
    ! [A_1588,B_1589,C_1590] :
      ( k1_relset_1(A_1588,B_1589,C_1590) = k1_relat_1(C_1590)
      | ~ m1_subset_1(C_1590,k1_zfmisc_1(k2_zfmisc_1(A_1588,B_1589))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_22072,plain,(
    ! [A_1611,B_1612,A_1613] :
      ( k1_relset_1(A_1611,B_1612,A_1613) = k1_relat_1(A_1613)
      | ~ r1_tarski(A_1613,k2_zfmisc_1(A_1611,B_1612)) ) ),
    inference(resolution,[status(thm)],[c_16,c_21908])).

tff(c_22079,plain,(
    ! [A_1611,B_1612] : k1_relset_1(A_1611,B_1612,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_21231,c_22072])).

tff(c_22096,plain,(
    ! [A_1611,B_1612] : k1_relset_1(A_1611,B_1612,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20895,c_22079])).

tff(c_52,plain,(
    ! [C_30,B_29] :
      ( v1_funct_2(C_30,k1_xboole_0,B_29)
      | k1_relset_1(k1_xboole_0,B_29,C_30) != k1_xboole_0
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_78,plain,(
    ! [C_30,B_29] :
      ( v1_funct_2(C_30,k1_xboole_0,B_29)
      | k1_relset_1(k1_xboole_0,B_29,C_30) != k1_xboole_0
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_52])).

tff(c_22153,plain,(
    ! [C_1621,B_1622] :
      ( v1_funct_2(C_1621,'#skF_3',B_1622)
      | k1_relset_1('#skF_3',B_1622,C_1621) != '#skF_3'
      | ~ m1_subset_1(C_1621,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20886,c_20886,c_20886,c_20886,c_78])).

tff(c_22155,plain,(
    ! [B_1622] :
      ( v1_funct_2('#skF_3','#skF_3',B_1622)
      | k1_relset_1('#skF_3',B_1622,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_18259,c_22153])).

tff(c_22161,plain,(
    ! [B_1622] : v1_funct_2('#skF_3','#skF_3',B_1622) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22096,c_22155])).

tff(c_21127,plain,(
    ! [C_1498,A_1499] :
      ( v4_relat_1(C_1498,A_1499)
      | ~ m1_subset_1(C_1498,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20893,c_20994])).

tff(c_21136,plain,(
    ! [A_1499] : v4_relat_1('#skF_3',A_1499) ),
    inference(resolution,[status(thm)],[c_18259,c_21127])).

tff(c_21141,plain,(
    ! [A_1288] : r1_tarski('#skF_3',A_1288) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21136,c_20887])).

tff(c_20892,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20886,c_20886,c_12])).

tff(c_20885,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_18268])).

tff(c_20954,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20886,c_20886,c_20885])).

tff(c_20955,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_20954])).

tff(c_21070,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20892,c_20955,c_20892,c_20955,c_13216])).

tff(c_21071,plain,(
    ~ r1_tarski('#skF_3',k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_21070])).

tff(c_21145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21141,c_21071])).

tff(c_21146,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_21070])).

tff(c_20961,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20955,c_13197])).

tff(c_21150,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21146,c_20961])).

tff(c_22166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22161,c_21150])).

tff(c_22167,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_20954])).

tff(c_22168,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_20954])).

tff(c_22194,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22167,c_22168])).

tff(c_22178,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22167,c_22167,c_18259])).

tff(c_22175,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22167,c_20886])).

tff(c_48,plain,(
    ! [A_28] :
      ( v1_funct_2(k1_xboole_0,A_28,k1_xboole_0)
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_28,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_80,plain,(
    ! [A_28] :
      ( v1_funct_2(k1_xboole_0,A_28,k1_xboole_0)
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_48])).

tff(c_22385,plain,(
    ! [A_28] :
      ( v1_funct_2('#skF_1',A_28,'#skF_1')
      | A_28 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22178,c_22175,c_22175,c_22175,c_22175,c_22175,c_80])).

tff(c_22218,plain,(
    ! [A_1626] : k2_zfmisc_1(A_1626,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22167,c_22167,c_20893])).

tff(c_42,plain,(
    ! [C_21,A_19,B_20] :
      ( v4_relat_1(C_21,A_19)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_22468,plain,(
    ! [C_1645,A_1646] :
      ( v4_relat_1(C_1645,A_1646)
      | ~ m1_subset_1(C_1645,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22218,c_42])).

tff(c_22477,plain,(
    ! [A_1646] : v4_relat_1('#skF_1',A_1646) ),
    inference(resolution,[status(thm)],[c_22178,c_22468])).

tff(c_22369,plain,(
    ! [A_1288] :
      ( r1_tarski('#skF_1',A_1288)
      | ~ v4_relat_1('#skF_1',A_1288) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22167,c_22167,c_20887])).

tff(c_22481,plain,(
    ! [A_1288] : r1_tarski('#skF_1',A_1288) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22477,c_22369])).

tff(c_22171,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22167,c_22167,c_20893])).

tff(c_22394,plain,
    ( k2_funct_1('#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22171,c_22167,c_22171,c_22167,c_13216])).

tff(c_22395,plain,(
    ~ r1_tarski('#skF_1',k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_22394])).

tff(c_22498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22481,c_22395])).

tff(c_22499,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_22394])).

tff(c_22183,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22167,c_13197])).

tff(c_22503,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22499,c_22183])).

tff(c_22527,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22385,c_22503])).

tff(c_22531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22194,c_22527])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:43:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.14/3.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.47/4.00  
% 10.47/4.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.47/4.00  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.47/4.00  
% 10.47/4.00  %Foreground sorts:
% 10.47/4.00  
% 10.47/4.00  
% 10.47/4.00  %Background operators:
% 10.47/4.00  
% 10.47/4.00  
% 10.47/4.00  %Foreground operators:
% 10.47/4.00  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.47/4.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.47/4.00  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.47/4.00  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.47/4.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.47/4.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.47/4.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.47/4.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.47/4.00  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.47/4.00  tff('#skF_2', type, '#skF_2': $i).
% 10.47/4.00  tff('#skF_3', type, '#skF_3': $i).
% 10.47/4.00  tff('#skF_1', type, '#skF_1': $i).
% 10.47/4.00  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.47/4.00  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.47/4.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.47/4.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.47/4.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.47/4.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.47/4.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.47/4.00  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.47/4.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.47/4.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.47/4.00  
% 10.71/4.04  tff(f_142, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 10.71/4.04  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.71/4.04  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.71/4.04  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 10.71/4.04  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.71/4.04  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.71/4.04  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.71/4.04  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 10.71/4.04  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.71/4.04  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 10.71/4.04  tff(f_125, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 10.71/4.04  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.71/4.04  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.71/4.04  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.71/4.04  tff(f_52, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 10.71/4.04  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.71/4.04  tff(c_192, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.71/4.04  tff(c_205, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_192])).
% 10.71/4.04  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.71/4.04  tff(c_70, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.71/4.04  tff(c_68, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.71/4.04  tff(c_16209, plain, (![A_1165, B_1166, C_1167]: (k2_relset_1(A_1165, B_1166, C_1167)=k2_relat_1(C_1167) | ~m1_subset_1(C_1167, k1_zfmisc_1(k2_zfmisc_1(A_1165, B_1166))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.71/4.04  tff(c_16219, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_16209])).
% 10.71/4.04  tff(c_16228, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_16219])).
% 10.71/4.04  tff(c_36, plain, (![A_15]: (k1_relat_1(k2_funct_1(A_15))=k2_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.71/4.04  tff(c_30, plain, (![A_14]: (v1_funct_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.71/4.04  tff(c_66, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.71/4.04  tff(c_146, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_66])).
% 10.71/4.04  tff(c_149, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_146])).
% 10.71/4.04  tff(c_152, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_149])).
% 10.71/4.04  tff(c_163, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.71/4.04  tff(c_170, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_163])).
% 10.71/4.04  tff(c_179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_152, c_170])).
% 10.71/4.04  tff(c_180, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_66])).
% 10.71/4.04  tff(c_212, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_180])).
% 10.71/4.04  tff(c_74, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.71/4.04  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.71/4.04  tff(c_858, plain, (![A_131, B_132, C_133]: (k1_relset_1(A_131, B_132, C_133)=k1_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.71/4.04  tff(c_873, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_858])).
% 10.71/4.04  tff(c_4391, plain, (![B_345, A_346, C_347]: (k1_xboole_0=B_345 | k1_relset_1(A_346, B_345, C_347)=A_346 | ~v1_funct_2(C_347, A_346, B_345) | ~m1_subset_1(C_347, k1_zfmisc_1(k2_zfmisc_1(A_346, B_345))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.71/4.04  tff(c_4404, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_4391])).
% 10.71/4.04  tff(c_4415, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_873, c_4404])).
% 10.71/4.04  tff(c_4417, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_4415])).
% 10.71/4.04  tff(c_16, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.71/4.04  tff(c_223, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_16, c_212])).
% 10.71/4.04  tff(c_1442, plain, (![B_188, A_189, C_190]: (k1_xboole_0=B_188 | k1_relset_1(A_189, B_188, C_190)=A_189 | ~v1_funct_2(C_190, A_189, B_188) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_189, B_188))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.71/4.04  tff(c_1455, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_1442])).
% 10.71/4.04  tff(c_1469, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_873, c_1455])).
% 10.71/4.04  tff(c_1471, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1469])).
% 10.71/4.04  tff(c_34, plain, (![A_15]: (k2_relat_1(k2_funct_1(A_15))=k1_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.71/4.04  tff(c_32, plain, (![A_14]: (v1_relat_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.71/4.04  tff(c_981, plain, (![A_148, B_149, C_150]: (k2_relset_1(A_148, B_149, C_150)=k2_relat_1(C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.71/4.04  tff(c_988, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_981])).
% 10.71/4.04  tff(c_997, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_988])).
% 10.71/4.04  tff(c_701, plain, (![A_115]: (k1_relat_1(k2_funct_1(A_115))=k2_relat_1(A_115) | ~v2_funct_1(A_115) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.71/4.04  tff(c_240, plain, (![B_60, A_61]: (v4_relat_1(B_60, A_61) | ~r1_tarski(k1_relat_1(B_60), A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.71/4.04  tff(c_250, plain, (![B_60]: (v4_relat_1(B_60, k1_relat_1(B_60)) | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_6, c_240])).
% 10.71/4.04  tff(c_3095, plain, (![A_291]: (v4_relat_1(k2_funct_1(A_291), k2_relat_1(A_291)) | ~v1_relat_1(k2_funct_1(A_291)) | ~v2_funct_1(A_291) | ~v1_funct_1(A_291) | ~v1_relat_1(A_291))), inference(superposition, [status(thm), theory('equality')], [c_701, c_250])).
% 10.71/4.04  tff(c_3100, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_997, c_3095])).
% 10.71/4.04  tff(c_3109, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_76, c_70, c_3100])).
% 10.71/4.04  tff(c_3132, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3109])).
% 10.71/4.04  tff(c_3135, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_3132])).
% 10.71/4.04  tff(c_3139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_76, c_3135])).
% 10.71/4.04  tff(c_3141, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3109])).
% 10.71/4.04  tff(c_181, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_66])).
% 10.71/4.04  tff(c_3140, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_3109])).
% 10.71/4.04  tff(c_20, plain, (![B_8, A_7]: (r1_tarski(k1_relat_1(B_8), A_7) | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.71/4.04  tff(c_3112, plain, (![A_292, A_293]: (r1_tarski(k2_relat_1(A_292), A_293) | ~v4_relat_1(k2_funct_1(A_292), A_293) | ~v1_relat_1(k2_funct_1(A_292)) | ~v2_funct_1(A_292) | ~v1_funct_1(A_292) | ~v1_relat_1(A_292))), inference(superposition, [status(thm), theory('equality')], [c_701, c_20])).
% 10.71/4.04  tff(c_3564, plain, (![A_317]: (r1_tarski(k2_relat_1(A_317), k1_relat_1(k2_funct_1(A_317))) | ~v2_funct_1(A_317) | ~v1_funct_1(A_317) | ~v1_relat_1(A_317) | ~v1_relat_1(k2_funct_1(A_317)))), inference(resolution, [status(thm)], [c_250, c_3112])).
% 10.71/4.04  tff(c_3575, plain, (r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_997, c_3564])).
% 10.71/4.04  tff(c_3589, plain, (r1_tarski('#skF_2', k1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3141, c_205, c_76, c_70, c_3575])).
% 10.71/4.04  tff(c_304, plain, (![B_76, A_77]: (r1_tarski(k1_relat_1(B_76), A_77) | ~v4_relat_1(B_76, A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.71/4.04  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.71/4.04  tff(c_324, plain, (![B_76, A_77]: (k1_relat_1(B_76)=A_77 | ~r1_tarski(A_77, k1_relat_1(B_76)) | ~v4_relat_1(B_76, A_77) | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_304, c_2])).
% 10.71/4.04  tff(c_3595, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_3589, c_324])).
% 10.71/4.04  tff(c_3606, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3141, c_3140, c_3595])).
% 10.71/4.04  tff(c_1038, plain, (![A_156]: (m1_subset_1(A_156, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_156), k2_relat_1(A_156)))) | ~v1_funct_1(A_156) | ~v1_relat_1(A_156))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.71/4.04  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.71/4.04  tff(c_1083, plain, (![A_156]: (r1_tarski(A_156, k2_zfmisc_1(k1_relat_1(A_156), k2_relat_1(A_156))) | ~v1_funct_1(A_156) | ~v1_relat_1(A_156))), inference(resolution, [status(thm)], [c_1038, c_14])).
% 10.71/4.04  tff(c_3714, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3606, c_1083])).
% 10.71/4.04  tff(c_3795, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_3141, c_181, c_3714])).
% 10.71/4.04  tff(c_3961, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_3795])).
% 10.71/4.04  tff(c_3980, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_76, c_70, c_1471, c_3961])).
% 10.71/4.04  tff(c_3982, plain, $false, inference(negUnitSimplification, [status(thm)], [c_223, c_3980])).
% 10.71/4.04  tff(c_3983, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1469])).
% 10.71/4.04  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.71/4.04  tff(c_259, plain, (![C_64, A_65, B_66]: (v4_relat_1(C_64, A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.71/4.04  tff(c_298, plain, (![C_72, A_73]: (v4_relat_1(C_72, A_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_259])).
% 10.71/4.04  tff(c_302, plain, (![A_5, A_73]: (v4_relat_1(A_5, A_73) | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_298])).
% 10.71/4.04  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.71/4.04  tff(c_113, plain, (![A_35, B_36]: (v1_relat_1(k2_zfmisc_1(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.71/4.04  tff(c_115, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_113])).
% 10.71/4.04  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.71/4.04  tff(c_320, plain, (![A_77]: (r1_tarski(k1_xboole_0, A_77) | ~v4_relat_1(k1_xboole_0, A_77) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_304])).
% 10.71/4.04  tff(c_327, plain, (![A_78]: (r1_tarski(k1_xboole_0, A_78) | ~v4_relat_1(k1_xboole_0, A_78))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_320])).
% 10.71/4.04  tff(c_331, plain, (![A_73]: (r1_tarski(k1_xboole_0, A_73) | ~r1_tarski(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_302, c_327])).
% 10.71/4.04  tff(c_344, plain, (![A_73]: (r1_tarski(k1_xboole_0, A_73))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_331])).
% 10.71/4.04  tff(c_4012, plain, (![A_73]: (r1_tarski('#skF_2', A_73))), inference(demodulation, [status(thm), theory('equality')], [c_3983, c_344])).
% 10.71/4.04  tff(c_4020, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3983, c_3983, c_10])).
% 10.71/4.04  tff(c_1062, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_997, c_1038])).
% 10.71/4.04  tff(c_1085, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_76, c_1062])).
% 10.71/4.04  tff(c_1122, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_1085, c_14])).
% 10.71/4.04  tff(c_1146, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_1122, c_2])).
% 10.71/4.04  tff(c_1262, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1146])).
% 10.71/4.04  tff(c_4149, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4020, c_1262])).
% 10.71/4.04  tff(c_4157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4012, c_4149])).
% 10.71/4.04  tff(c_4158, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_1146])).
% 10.71/4.04  tff(c_4420, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4417, c_4158])).
% 10.71/4.04  tff(c_124, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.71/4.04  tff(c_132, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_124])).
% 10.71/4.04  tff(c_182, plain, (![B_50, A_51]: (B_50=A_51 | ~r1_tarski(B_50, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.71/4.04  tff(c_187, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_132, c_182])).
% 10.71/4.04  tff(c_258, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_187])).
% 10.71/4.04  tff(c_4478, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4420, c_258])).
% 10.71/4.04  tff(c_4483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4478])).
% 10.71/4.04  tff(c_4484, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_4415])).
% 10.71/4.04  tff(c_4515, plain, (![A_73]: (r1_tarski('#skF_2', A_73))), inference(demodulation, [status(thm), theory('equality')], [c_4484, c_344])).
% 10.71/4.04  tff(c_4523, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4484, c_4484, c_10])).
% 10.71/4.04  tff(c_4746, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4523, c_258])).
% 10.71/4.04  tff(c_4751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4515, c_4746])).
% 10.71/4.04  tff(c_4752, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_187])).
% 10.71/4.04  tff(c_4755, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4752, c_72])).
% 10.71/4.04  tff(c_5368, plain, (![A_425, B_426, C_427]: (k1_relset_1(A_425, B_426, C_427)=k1_relat_1(C_427) | ~m1_subset_1(C_427, k1_zfmisc_1(k2_zfmisc_1(A_425, B_426))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.71/4.04  tff(c_5539, plain, (![C_449]: (k1_relset_1('#skF_1', '#skF_2', C_449)=k1_relat_1(C_449) | ~m1_subset_1(C_449, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4752, c_5368])).
% 10.71/4.04  tff(c_5547, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4755, c_5539])).
% 10.71/4.04  tff(c_6188, plain, (![B_502, C_503, A_504]: (k1_xboole_0=B_502 | v1_funct_2(C_503, A_504, B_502) | k1_relset_1(A_504, B_502, C_503)!=A_504 | ~m1_subset_1(C_503, k1_zfmisc_1(k2_zfmisc_1(A_504, B_502))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.71/4.04  tff(c_6197, plain, (![C_503]: (k1_xboole_0='#skF_2' | v1_funct_2(C_503, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_503)!='#skF_1' | ~m1_subset_1(C_503, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4752, c_6188])).
% 10.71/4.04  tff(c_6232, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_6197])).
% 10.71/4.04  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.71/4.04  tff(c_4764, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4752, c_8])).
% 10.71/4.04  tff(c_4784, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_4764])).
% 10.71/4.04  tff(c_6268, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6232, c_4784])).
% 10.71/4.04  tff(c_6608, plain, (![A_517]: (k2_zfmisc_1(A_517, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6232, c_6232, c_10])).
% 10.71/4.04  tff(c_6700, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_6608, c_4752])).
% 10.71/4.04  tff(c_6736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6268, c_6700])).
% 10.71/4.04  tff(c_6738, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_6197])).
% 10.71/4.04  tff(c_6814, plain, (![B_528, A_529, C_530]: (k1_xboole_0=B_528 | k1_relset_1(A_529, B_528, C_530)=A_529 | ~v1_funct_2(C_530, A_529, B_528) | ~m1_subset_1(C_530, k1_zfmisc_1(k2_zfmisc_1(A_529, B_528))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.71/4.04  tff(c_6823, plain, (![C_530]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_530)='#skF_1' | ~v1_funct_2(C_530, '#skF_1', '#skF_2') | ~m1_subset_1(C_530, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4752, c_6814])).
% 10.71/4.04  tff(c_7428, plain, (![C_566]: (k1_relset_1('#skF_1', '#skF_2', C_566)='#skF_1' | ~v1_funct_2(C_566, '#skF_1', '#skF_2') | ~m1_subset_1(C_566, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_6738, c_6823])).
% 10.71/4.04  tff(c_7431, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4755, c_7428])).
% 10.71/4.04  tff(c_7438, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5547, c_7431])).
% 10.71/4.04  tff(c_5493, plain, (![A_441, B_442, C_443]: (k2_relset_1(A_441, B_442, C_443)=k2_relat_1(C_443) | ~m1_subset_1(C_443, k1_zfmisc_1(k2_zfmisc_1(A_441, B_442))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.71/4.04  tff(c_5642, plain, (![C_460]: (k2_relset_1('#skF_1', '#skF_2', C_460)=k2_relat_1(C_460) | ~m1_subset_1(C_460, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_4752, c_5493])).
% 10.71/4.04  tff(c_5645, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4755, c_5642])).
% 10.71/4.04  tff(c_5651, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_5645])).
% 10.71/4.04  tff(c_4841, plain, (![C_361, A_362, B_363]: (v4_relat_1(C_361, A_362) | ~m1_subset_1(C_361, k1_zfmisc_1(k2_zfmisc_1(A_362, B_363))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.71/4.04  tff(c_5045, plain, (![A_392, A_393, B_394]: (v4_relat_1(A_392, A_393) | ~r1_tarski(A_392, k2_zfmisc_1(A_393, B_394)))), inference(resolution, [status(thm)], [c_16, c_4841])).
% 10.71/4.04  tff(c_5304, plain, (![B_418, A_419, B_420]: (v4_relat_1(k1_relat_1(B_418), A_419) | ~v4_relat_1(B_418, k2_zfmisc_1(A_419, B_420)) | ~v1_relat_1(B_418))), inference(resolution, [status(thm)], [c_20, c_5045])).
% 10.71/4.04  tff(c_5429, plain, (![B_432]: (v4_relat_1(k1_relat_1(B_432), '#skF_1') | ~v4_relat_1(B_432, '#skF_3') | ~v1_relat_1(B_432))), inference(superposition, [status(thm), theory('equality')], [c_4752, c_5304])).
% 10.71/4.04  tff(c_5799, plain, (![A_469]: (v4_relat_1(k2_relat_1(A_469), '#skF_1') | ~v4_relat_1(k2_funct_1(A_469), '#skF_3') | ~v1_relat_1(k2_funct_1(A_469)) | ~v2_funct_1(A_469) | ~v1_funct_1(A_469) | ~v1_relat_1(A_469))), inference(superposition, [status(thm), theory('equality')], [c_36, c_5429])).
% 10.71/4.04  tff(c_5802, plain, (v4_relat_1('#skF_2', '#skF_1') | ~v4_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5651, c_5799])).
% 10.71/4.04  tff(c_5810, plain, (v4_relat_1('#skF_2', '#skF_1') | ~v4_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_76, c_70, c_5802])).
% 10.71/4.04  tff(c_5855, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5810])).
% 10.71/4.04  tff(c_5858, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_5855])).
% 10.71/4.04  tff(c_5862, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_76, c_5858])).
% 10.71/4.04  tff(c_5864, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5810])).
% 10.71/4.04  tff(c_5710, plain, (![A_468]: (m1_subset_1(A_468, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_468), k2_relat_1(A_468)))) | ~v1_funct_1(A_468) | ~v1_relat_1(A_468))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.71/4.04  tff(c_10101, plain, (![A_665]: (m1_subset_1(k2_funct_1(A_665), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_665), k2_relat_1(k2_funct_1(A_665))))) | ~v1_funct_1(k2_funct_1(A_665)) | ~v1_relat_1(k2_funct_1(A_665)) | ~v2_funct_1(A_665) | ~v1_funct_1(A_665) | ~v1_relat_1(A_665))), inference(superposition, [status(thm), theory('equality')], [c_36, c_5710])).
% 10.71/4.04  tff(c_10131, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5651, c_10101])).
% 10.71/4.04  tff(c_10153, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_76, c_70, c_5864, c_181, c_10131])).
% 10.71/4.04  tff(c_10185, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_10153])).
% 10.71/4.04  tff(c_10203, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_76, c_70, c_7438, c_10185])).
% 10.71/4.04  tff(c_10205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_212, c_10203])).
% 10.71/4.04  tff(c_10207, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_4764])).
% 10.71/4.04  tff(c_10214, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10207, c_10207, c_12])).
% 10.71/4.04  tff(c_10206, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_4764])).
% 10.71/4.04  tff(c_10252, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10207, c_10207, c_10206])).
% 10.71/4.04  tff(c_10253, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_10252])).
% 10.71/4.04  tff(c_10255, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10253, c_223])).
% 10.71/4.04  tff(c_10328, plain, (~r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10214, c_10255])).
% 10.71/4.04  tff(c_10217, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10207, c_10207, c_26])).
% 10.71/4.04  tff(c_10648, plain, (![A_720]: (k2_relat_1(k2_funct_1(A_720))=k1_relat_1(A_720) | ~v2_funct_1(A_720) | ~v1_funct_1(A_720) | ~v1_relat_1(A_720))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.71/4.04  tff(c_62, plain, (![A_31]: (v1_funct_2(A_31, k1_relat_1(A_31), k2_relat_1(A_31)) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.71/4.04  tff(c_12327, plain, (![A_861]: (v1_funct_2(k2_funct_1(A_861), k1_relat_1(k2_funct_1(A_861)), k1_relat_1(A_861)) | ~v1_funct_1(k2_funct_1(A_861)) | ~v1_relat_1(k2_funct_1(A_861)) | ~v2_funct_1(A_861) | ~v1_funct_1(A_861) | ~v1_relat_1(A_861))), inference(superposition, [status(thm), theory('equality')], [c_10648, c_62])).
% 10.71/4.04  tff(c_12342, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10217, c_12327])).
% 10.71/4.04  tff(c_12344, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_76, c_70, c_181, c_12342])).
% 10.71/4.04  tff(c_12345, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_12344])).
% 10.71/4.04  tff(c_12348, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_12345])).
% 10.71/4.04  tff(c_12352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_76, c_12348])).
% 10.71/4.04  tff(c_12354, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_12344])).
% 10.71/4.04  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.71/4.04  tff(c_10216, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10207, c_10207, c_24])).
% 10.71/4.04  tff(c_10666, plain, (![A_722]: (k1_relat_1(k2_funct_1(A_722))=k2_relat_1(A_722) | ~v2_funct_1(A_722) | ~v1_funct_1(A_722) | ~v1_relat_1(A_722))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.71/4.04  tff(c_12405, plain, (![A_863]: (v4_relat_1(k2_funct_1(A_863), k2_relat_1(A_863)) | ~v1_relat_1(k2_funct_1(A_863)) | ~v2_funct_1(A_863) | ~v1_funct_1(A_863) | ~v1_relat_1(A_863))), inference(superposition, [status(thm), theory('equality')], [c_10666, c_250])).
% 10.71/4.04  tff(c_12416, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10216, c_12405])).
% 10.71/4.04  tff(c_12421, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_205, c_76, c_70, c_12354, c_12416])).
% 10.71/4.04  tff(c_10215, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10207, c_10207, c_10])).
% 10.71/4.04  tff(c_10416, plain, (![C_689, A_690, B_691]: (v4_relat_1(C_689, A_690) | ~m1_subset_1(C_689, k1_zfmisc_1(k2_zfmisc_1(A_690, B_691))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.71/4.04  tff(c_10447, plain, (![C_694, A_695]: (v4_relat_1(C_694, A_695) | ~m1_subset_1(C_694, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_10215, c_10416])).
% 10.71/4.04  tff(c_10453, plain, (![A_695]: (v4_relat_1('#skF_3', A_695))), inference(resolution, [status(thm)], [c_4755, c_10447])).
% 10.71/4.04  tff(c_10277, plain, (![B_668, A_669]: (r1_tarski(k1_relat_1(B_668), A_669) | ~v4_relat_1(B_668, A_669) | ~v1_relat_1(B_668))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.71/4.04  tff(c_10293, plain, (![A_669]: (r1_tarski('#skF_3', A_669) | ~v4_relat_1('#skF_3', A_669) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_10217, c_10277])).
% 10.71/4.04  tff(c_10299, plain, (![A_669]: (r1_tarski('#skF_3', A_669) | ~v4_relat_1('#skF_3', A_669))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_10293])).
% 10.71/4.04  tff(c_10460, plain, (![A_697]: (r1_tarski('#skF_3', A_697))), inference(demodulation, [status(thm), theory('equality')], [c_10453, c_10299])).
% 10.71/4.04  tff(c_10482, plain, (![A_698]: (A_698='#skF_3' | ~r1_tarski(A_698, '#skF_3'))), inference(resolution, [status(thm)], [c_10460, c_2])).
% 10.71/4.04  tff(c_10497, plain, (![B_8]: (k1_relat_1(B_8)='#skF_3' | ~v4_relat_1(B_8, '#skF_3') | ~v1_relat_1(B_8))), inference(resolution, [status(thm)], [c_20, c_10482])).
% 10.71/4.04  tff(c_12435, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_12421, c_10497])).
% 10.71/4.04  tff(c_12450, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12354, c_12435])).
% 10.71/4.04  tff(c_10826, plain, (![A_739]: (m1_subset_1(A_739, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_739), k2_relat_1(A_739)))) | ~v1_funct_1(A_739) | ~v1_relat_1(A_739))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.71/4.04  tff(c_10860, plain, (![A_739]: (r1_tarski(A_739, k2_zfmisc_1(k1_relat_1(A_739), k2_relat_1(A_739))) | ~v1_funct_1(A_739) | ~v1_relat_1(A_739))), inference(resolution, [status(thm)], [c_10826, c_14])).
% 10.71/4.04  tff(c_12541, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12450, c_10860])).
% 10.71/4.04  tff(c_12622, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12354, c_181, c_10214, c_12541])).
% 10.71/4.04  tff(c_12624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10328, c_12622])).
% 10.71/4.04  tff(c_12625, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_10252])).
% 10.71/4.04  tff(c_12626, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_10252])).
% 10.71/4.04  tff(c_12647, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12625, c_12626])).
% 10.71/4.04  tff(c_12628, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12625, c_12625, c_10216])).
% 10.71/4.04  tff(c_12633, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12625, c_12625, c_4755])).
% 10.71/4.04  tff(c_12696, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12625, c_12625, c_10214])).
% 10.71/4.04  tff(c_13137, plain, (![A_923, B_924, C_925]: (k2_relset_1(A_923, B_924, C_925)=k2_relat_1(C_925) | ~m1_subset_1(C_925, k1_zfmisc_1(k2_zfmisc_1(A_923, B_924))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.71/4.04  tff(c_13185, plain, (![B_932, C_933]: (k2_relset_1('#skF_1', B_932, C_933)=k2_relat_1(C_933) | ~m1_subset_1(C_933, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_12696, c_13137])).
% 10.71/4.04  tff(c_13187, plain, (![B_932]: (k2_relset_1('#skF_1', B_932, '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_12633, c_13185])).
% 10.71/4.04  tff(c_13192, plain, (![B_932]: (k2_relset_1('#skF_1', B_932, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12628, c_13187])).
% 10.71/4.04  tff(c_12639, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12625, c_68])).
% 10.71/4.04  tff(c_13194, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13192, c_12639])).
% 10.71/4.04  tff(c_13196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12647, c_13194])).
% 10.71/4.04  tff(c_13197, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_180])).
% 10.71/4.04  tff(c_13934, plain, (![A_1011, B_1012, C_1013]: (k2_relset_1(A_1011, B_1012, C_1013)=k2_relat_1(C_1013) | ~m1_subset_1(C_1013, k1_zfmisc_1(k2_zfmisc_1(A_1011, B_1012))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.71/4.04  tff(c_13944, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_13934])).
% 10.71/4.04  tff(c_13954, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_13944])).
% 10.71/4.04  tff(c_13198, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_180])).
% 10.71/4.04  tff(c_13807, plain, (![A_996, B_997, C_998]: (k1_relset_1(A_996, B_997, C_998)=k1_relat_1(C_998) | ~m1_subset_1(C_998, k1_zfmisc_1(k2_zfmisc_1(A_996, B_997))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.71/4.04  tff(c_13824, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_13198, c_13807])).
% 10.71/4.04  tff(c_15086, plain, (![B_1075, C_1076, A_1077]: (k1_xboole_0=B_1075 | v1_funct_2(C_1076, A_1077, B_1075) | k1_relset_1(A_1077, B_1075, C_1076)!=A_1077 | ~m1_subset_1(C_1076, k1_zfmisc_1(k2_zfmisc_1(A_1077, B_1075))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.71/4.04  tff(c_15095, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_13198, c_15086])).
% 10.71/4.04  tff(c_15111, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_13824, c_15095])).
% 10.71/4.04  tff(c_15112, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_13197, c_15111])).
% 10.71/4.04  tff(c_15117, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_15112])).
% 10.71/4.04  tff(c_15120, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_15117])).
% 10.71/4.04  tff(c_15123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_76, c_70, c_13954, c_15120])).
% 10.71/4.04  tff(c_15124, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_15112])).
% 10.71/4.04  tff(c_13303, plain, (![C_946, A_947, B_948]: (v4_relat_1(C_946, A_947) | ~m1_subset_1(C_946, k1_zfmisc_1(k2_zfmisc_1(A_947, B_948))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.71/4.04  tff(c_13323, plain, (![C_949, A_950]: (v4_relat_1(C_949, A_950) | ~m1_subset_1(C_949, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_13303])).
% 10.71/4.04  tff(c_13328, plain, (![A_951, A_952]: (v4_relat_1(A_951, A_952) | ~r1_tarski(A_951, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_13323])).
% 10.71/4.04  tff(c_13257, plain, (![B_942, A_943]: (r1_tarski(k1_relat_1(B_942), A_943) | ~v4_relat_1(B_942, A_943) | ~v1_relat_1(B_942))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.71/4.04  tff(c_13273, plain, (![A_943]: (r1_tarski(k1_xboole_0, A_943) | ~v4_relat_1(k1_xboole_0, A_943) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_13257])).
% 10.71/4.04  tff(c_13279, plain, (![A_943]: (r1_tarski(k1_xboole_0, A_943) | ~v4_relat_1(k1_xboole_0, A_943))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_13273])).
% 10.71/4.04  tff(c_13332, plain, (![A_952]: (r1_tarski(k1_xboole_0, A_952) | ~r1_tarski(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_13328, c_13279])).
% 10.71/4.04  tff(c_13335, plain, (![A_952]: (r1_tarski(k1_xboole_0, A_952))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_13332])).
% 10.71/4.04  tff(c_15154, plain, (![A_952]: (r1_tarski('#skF_1', A_952))), inference(demodulation, [status(thm), theory('equality')], [c_15124, c_13335])).
% 10.71/4.04  tff(c_15163, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_15124, c_15124, c_10])).
% 10.71/4.04  tff(c_13213, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_13198, c_14])).
% 10.71/4.04  tff(c_13216, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_13213, c_2])).
% 10.71/4.04  tff(c_13395, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_13216])).
% 10.71/4.04  tff(c_15360, plain, (~r1_tarski('#skF_1', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_15163, c_13395])).
% 10.71/4.04  tff(c_15365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15154, c_15360])).
% 10.71/4.04  tff(c_15366, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_13216])).
% 10.71/4.04  tff(c_15369, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_15366, c_13198])).
% 10.71/4.04  tff(c_16673, plain, (![A_1199, B_1200, C_1201]: (k1_relset_1(A_1199, B_1200, C_1201)=k1_relat_1(C_1201) | ~m1_subset_1(C_1201, k1_zfmisc_1(k2_zfmisc_1(A_1199, B_1200))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.71/4.04  tff(c_16721, plain, (![C_1203]: (k1_relset_1('#skF_2', '#skF_1', C_1203)=k1_relat_1(C_1203) | ~m1_subset_1(C_1203, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_15366, c_16673])).
% 10.71/4.04  tff(c_16729, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_15369, c_16721])).
% 10.71/4.04  tff(c_17129, plain, (![B_1251, C_1252, A_1253]: (k1_xboole_0=B_1251 | v1_funct_2(C_1252, A_1253, B_1251) | k1_relset_1(A_1253, B_1251, C_1252)!=A_1253 | ~m1_subset_1(C_1252, k1_zfmisc_1(k2_zfmisc_1(A_1253, B_1251))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.71/4.04  tff(c_17138, plain, (![C_1252]: (k1_xboole_0='#skF_1' | v1_funct_2(C_1252, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', C_1252)!='#skF_2' | ~m1_subset_1(C_1252, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_15366, c_17129])).
% 10.71/4.04  tff(c_17252, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_17138])).
% 10.71/4.04  tff(c_15384, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k2_funct_1('#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_15366, c_8])).
% 10.71/4.04  tff(c_15432, plain, (k2_funct_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_15384])).
% 10.71/4.04  tff(c_17283, plain, (k2_funct_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17252, c_15432])).
% 10.71/4.04  tff(c_17295, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17252, c_17252, c_10])).
% 10.71/4.04  tff(c_17639, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17295, c_15366])).
% 10.71/4.04  tff(c_17641, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17283, c_17639])).
% 10.71/4.04  tff(c_17644, plain, (![C_1268]: (v1_funct_2(C_1268, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', C_1268)!='#skF_2' | ~m1_subset_1(C_1268, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(splitRight, [status(thm)], [c_17138])).
% 10.71/4.04  tff(c_17647, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_15369, c_17644])).
% 10.71/4.04  tff(c_17653, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_16729, c_17647])).
% 10.71/4.04  tff(c_17654, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_13197, c_17653])).
% 10.71/4.04  tff(c_17658, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_17654])).
% 10.71/4.04  tff(c_17661, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_76, c_70, c_16228, c_17658])).
% 10.71/4.04  tff(c_17662, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_15384])).
% 10.71/4.04  tff(c_17742, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_17662])).
% 10.71/4.04  tff(c_17751, plain, (![A_952]: (r1_tarski('#skF_1', A_952))), inference(demodulation, [status(thm), theory('equality')], [c_17742, c_13335])).
% 10.71/4.04  tff(c_17759, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17742, c_17742, c_12])).
% 10.71/4.04  tff(c_13238, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_187])).
% 10.71/4.04  tff(c_18012, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17759, c_13238])).
% 10.71/4.04  tff(c_18017, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17751, c_18012])).
% 10.71/4.04  tff(c_18018, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_17662])).
% 10.71/4.04  tff(c_18032, plain, (![A_952]: (r1_tarski('#skF_2', A_952))), inference(demodulation, [status(thm), theory('equality')], [c_18018, c_13335])).
% 10.71/4.04  tff(c_18041, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18018, c_18018, c_10])).
% 10.71/4.04  tff(c_18250, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18041, c_13238])).
% 10.71/4.04  tff(c_18255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18032, c_18250])).
% 10.71/4.04  tff(c_18256, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_187])).
% 10.71/4.04  tff(c_18259, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18256, c_72])).
% 10.71/4.04  tff(c_19169, plain, (![A_1388, B_1389, C_1390]: (k2_relset_1(A_1388, B_1389, C_1390)=k2_relat_1(C_1390) | ~m1_subset_1(C_1390, k1_zfmisc_1(k2_zfmisc_1(A_1388, B_1389))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.71/4.04  tff(c_19208, plain, (![C_1394]: (k2_relset_1('#skF_1', '#skF_2', C_1394)=k2_relat_1(C_1394) | ~m1_subset_1(C_1394, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_18256, c_19169])).
% 10.71/4.04  tff(c_19211, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18259, c_19208])).
% 10.71/4.04  tff(c_19217, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_19211])).
% 10.71/4.04  tff(c_19403, plain, (![A_1401, B_1402, C_1403]: (k1_relset_1(A_1401, B_1402, C_1403)=k1_relat_1(C_1403) | ~m1_subset_1(C_1403, k1_zfmisc_1(k2_zfmisc_1(A_1401, B_1402))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.71/4.04  tff(c_19428, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_13198, c_19403])).
% 10.71/4.04  tff(c_20507, plain, (![B_1472, C_1473, A_1474]: (k1_xboole_0=B_1472 | v1_funct_2(C_1473, A_1474, B_1472) | k1_relset_1(A_1474, B_1472, C_1473)!=A_1474 | ~m1_subset_1(C_1473, k1_zfmisc_1(k2_zfmisc_1(A_1474, B_1472))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.71/4.04  tff(c_20519, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_13198, c_20507])).
% 10.71/4.04  tff(c_20537, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_19428, c_20519])).
% 10.71/4.04  tff(c_20538, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_13197, c_20537])).
% 10.71/4.04  tff(c_20541, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_20538])).
% 10.71/4.04  tff(c_20544, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_20541])).
% 10.71/4.04  tff(c_20547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_76, c_70, c_19217, c_20544])).
% 10.71/4.04  tff(c_20548, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_20538])).
% 10.71/4.04  tff(c_18268, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_18256, c_8])).
% 10.71/4.04  tff(c_18324, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_18268])).
% 10.71/4.04  tff(c_20587, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20548, c_18324])).
% 10.71/4.04  tff(c_20592, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20548, c_20548, c_12])).
% 10.71/4.04  tff(c_20882, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20592, c_18256])).
% 10.71/4.04  tff(c_20884, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20587, c_20882])).
% 10.71/4.04  tff(c_20886, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_18268])).
% 10.71/4.04  tff(c_20895, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20886, c_20886, c_26])).
% 10.71/4.04  tff(c_20893, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20886, c_20886, c_10])).
% 10.71/4.04  tff(c_20994, plain, (![C_1484, A_1485, B_1486]: (v4_relat_1(C_1484, A_1485) | ~m1_subset_1(C_1484, k1_zfmisc_1(k2_zfmisc_1(A_1485, B_1486))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.71/4.04  tff(c_21220, plain, (![C_1507, A_1508]: (v4_relat_1(C_1507, A_1508) | ~m1_subset_1(C_1507, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_20893, c_20994])).
% 10.71/4.04  tff(c_21226, plain, (![A_1508]: (v4_relat_1('#skF_3', A_1508))), inference(resolution, [status(thm)], [c_18259, c_21220])).
% 10.71/4.04  tff(c_18288, plain, (![B_1287, A_1288]: (r1_tarski(k1_relat_1(B_1287), A_1288) | ~v4_relat_1(B_1287, A_1288) | ~v1_relat_1(B_1287))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.71/4.04  tff(c_18305, plain, (![A_1288]: (r1_tarski(k1_xboole_0, A_1288) | ~v4_relat_1(k1_xboole_0, A_1288) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_18288])).
% 10.71/4.04  tff(c_18311, plain, (![A_1288]: (r1_tarski(k1_xboole_0, A_1288) | ~v4_relat_1(k1_xboole_0, A_1288))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_18305])).
% 10.71/4.04  tff(c_20887, plain, (![A_1288]: (r1_tarski('#skF_3', A_1288) | ~v4_relat_1('#skF_3', A_1288))), inference(demodulation, [status(thm), theory('equality')], [c_20886, c_20886, c_18311])).
% 10.71/4.04  tff(c_21231, plain, (![A_1288]: (r1_tarski('#skF_3', A_1288))), inference(demodulation, [status(thm), theory('equality')], [c_21226, c_20887])).
% 10.71/4.04  tff(c_21908, plain, (![A_1588, B_1589, C_1590]: (k1_relset_1(A_1588, B_1589, C_1590)=k1_relat_1(C_1590) | ~m1_subset_1(C_1590, k1_zfmisc_1(k2_zfmisc_1(A_1588, B_1589))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.71/4.04  tff(c_22072, plain, (![A_1611, B_1612, A_1613]: (k1_relset_1(A_1611, B_1612, A_1613)=k1_relat_1(A_1613) | ~r1_tarski(A_1613, k2_zfmisc_1(A_1611, B_1612)))), inference(resolution, [status(thm)], [c_16, c_21908])).
% 10.71/4.04  tff(c_22079, plain, (![A_1611, B_1612]: (k1_relset_1(A_1611, B_1612, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_21231, c_22072])).
% 10.71/4.04  tff(c_22096, plain, (![A_1611, B_1612]: (k1_relset_1(A_1611, B_1612, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20895, c_22079])).
% 10.71/4.04  tff(c_52, plain, (![C_30, B_29]: (v1_funct_2(C_30, k1_xboole_0, B_29) | k1_relset_1(k1_xboole_0, B_29, C_30)!=k1_xboole_0 | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_29))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.71/4.04  tff(c_78, plain, (![C_30, B_29]: (v1_funct_2(C_30, k1_xboole_0, B_29) | k1_relset_1(k1_xboole_0, B_29, C_30)!=k1_xboole_0 | ~m1_subset_1(C_30, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_52])).
% 10.71/4.04  tff(c_22153, plain, (![C_1621, B_1622]: (v1_funct_2(C_1621, '#skF_3', B_1622) | k1_relset_1('#skF_3', B_1622, C_1621)!='#skF_3' | ~m1_subset_1(C_1621, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_20886, c_20886, c_20886, c_20886, c_78])).
% 10.71/4.04  tff(c_22155, plain, (![B_1622]: (v1_funct_2('#skF_3', '#skF_3', B_1622) | k1_relset_1('#skF_3', B_1622, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_18259, c_22153])).
% 10.71/4.04  tff(c_22161, plain, (![B_1622]: (v1_funct_2('#skF_3', '#skF_3', B_1622))), inference(demodulation, [status(thm), theory('equality')], [c_22096, c_22155])).
% 10.71/4.04  tff(c_21127, plain, (![C_1498, A_1499]: (v4_relat_1(C_1498, A_1499) | ~m1_subset_1(C_1498, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_20893, c_20994])).
% 10.71/4.04  tff(c_21136, plain, (![A_1499]: (v4_relat_1('#skF_3', A_1499))), inference(resolution, [status(thm)], [c_18259, c_21127])).
% 10.71/4.04  tff(c_21141, plain, (![A_1288]: (r1_tarski('#skF_3', A_1288))), inference(demodulation, [status(thm), theory('equality')], [c_21136, c_20887])).
% 10.71/4.04  tff(c_20892, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20886, c_20886, c_12])).
% 10.71/4.04  tff(c_20885, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_18268])).
% 10.71/4.04  tff(c_20954, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20886, c_20886, c_20885])).
% 10.71/4.04  tff(c_20955, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_20954])).
% 10.71/4.04  tff(c_21070, plain, (k2_funct_1('#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20892, c_20955, c_20892, c_20955, c_13216])).
% 10.71/4.04  tff(c_21071, plain, (~r1_tarski('#skF_3', k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_21070])).
% 10.71/4.04  tff(c_21145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21141, c_21071])).
% 10.71/4.04  tff(c_21146, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_21070])).
% 10.71/4.04  tff(c_20961, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20955, c_13197])).
% 10.71/4.04  tff(c_21150, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21146, c_20961])).
% 10.71/4.04  tff(c_22166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22161, c_21150])).
% 10.71/4.04  tff(c_22167, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_20954])).
% 10.71/4.04  tff(c_22168, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_20954])).
% 10.71/4.04  tff(c_22194, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22167, c_22168])).
% 10.71/4.04  tff(c_22178, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22167, c_22167, c_18259])).
% 10.71/4.04  tff(c_22175, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22167, c_20886])).
% 10.71/4.04  tff(c_48, plain, (![A_28]: (v1_funct_2(k1_xboole_0, A_28, k1_xboole_0) | k1_xboole_0=A_28 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_28, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.71/4.04  tff(c_80, plain, (![A_28]: (v1_funct_2(k1_xboole_0, A_28, k1_xboole_0) | k1_xboole_0=A_28 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_48])).
% 10.71/4.04  tff(c_22385, plain, (![A_28]: (v1_funct_2('#skF_1', A_28, '#skF_1') | A_28='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22178, c_22175, c_22175, c_22175, c_22175, c_22175, c_80])).
% 10.71/4.04  tff(c_22218, plain, (![A_1626]: (k2_zfmisc_1(A_1626, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22167, c_22167, c_20893])).
% 10.71/4.04  tff(c_42, plain, (![C_21, A_19, B_20]: (v4_relat_1(C_21, A_19) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 10.71/4.04  tff(c_22468, plain, (![C_1645, A_1646]: (v4_relat_1(C_1645, A_1646) | ~m1_subset_1(C_1645, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_22218, c_42])).
% 10.71/4.04  tff(c_22477, plain, (![A_1646]: (v4_relat_1('#skF_1', A_1646))), inference(resolution, [status(thm)], [c_22178, c_22468])).
% 10.71/4.04  tff(c_22369, plain, (![A_1288]: (r1_tarski('#skF_1', A_1288) | ~v4_relat_1('#skF_1', A_1288))), inference(demodulation, [status(thm), theory('equality')], [c_22167, c_22167, c_20887])).
% 10.71/4.04  tff(c_22481, plain, (![A_1288]: (r1_tarski('#skF_1', A_1288))), inference(demodulation, [status(thm), theory('equality')], [c_22477, c_22369])).
% 10.71/4.04  tff(c_22171, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22167, c_22167, c_20893])).
% 10.71/4.04  tff(c_22394, plain, (k2_funct_1('#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22171, c_22167, c_22171, c_22167, c_13216])).
% 10.71/4.04  tff(c_22395, plain, (~r1_tarski('#skF_1', k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_22394])).
% 10.71/4.04  tff(c_22498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22481, c_22395])).
% 10.71/4.04  tff(c_22499, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_22394])).
% 10.71/4.04  tff(c_22183, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22167, c_13197])).
% 10.71/4.04  tff(c_22503, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22499, c_22183])).
% 10.71/4.04  tff(c_22527, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_22385, c_22503])).
% 10.71/4.04  tff(c_22531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22194, c_22527])).
% 10.71/4.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.71/4.04  
% 10.71/4.04  Inference rules
% 10.71/4.04  ----------------------
% 10.71/4.04  #Ref     : 0
% 10.71/4.04  #Sup     : 4748
% 10.71/4.04  #Fact    : 0
% 10.71/4.04  #Define  : 0
% 10.71/4.04  #Split   : 70
% 10.71/4.04  #Chain   : 0
% 10.71/4.04  #Close   : 0
% 10.71/4.04  
% 10.71/4.04  Ordering : KBO
% 10.71/4.04  
% 10.71/4.04  Simplification rules
% 10.71/4.04  ----------------------
% 10.71/4.04  #Subsume      : 606
% 10.71/4.04  #Demod        : 6699
% 10.71/4.04  #Tautology    : 2529
% 10.71/4.04  #SimpNegUnit  : 46
% 10.71/4.04  #BackRed      : 681
% 10.71/4.04  
% 10.71/4.04  #Partial instantiations: 0
% 10.71/4.04  #Strategies tried      : 1
% 10.71/4.04  
% 10.71/4.04  Timing (in seconds)
% 10.71/4.04  ----------------------
% 10.71/4.05  Preprocessing        : 0.38
% 10.71/4.05  Parsing              : 0.20
% 10.71/4.05  CNF conversion       : 0.03
% 10.71/4.05  Main loop            : 2.73
% 10.71/4.05  Inferencing          : 0.85
% 10.71/4.05  Reduction            : 1.04
% 10.71/4.05  Demodulation         : 0.78
% 10.71/4.05  BG Simplification    : 0.08
% 10.71/4.05  Subsumption          : 0.55
% 10.71/4.05  Abstraction          : 0.10
% 10.71/4.05  MUC search           : 0.00
% 10.71/4.05  Cooper               : 0.00
% 10.71/4.05  Total                : 3.24
% 10.71/4.05  Index Insertion      : 0.00
% 10.71/4.05  Index Deletion       : 0.00
% 10.71/4.05  Index Matching       : 0.00
% 10.71/4.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
