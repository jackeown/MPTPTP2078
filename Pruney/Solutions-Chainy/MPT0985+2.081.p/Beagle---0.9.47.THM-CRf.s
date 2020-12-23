%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:39 EST 2020

% Result     : Theorem 10.38s
% Output     : CNFRefutation 10.75s
% Verified   : 
% Statistics : Number of formulae       :  335 (4279 expanded)
%              Number of leaves         :   38 (1304 expanded)
%              Depth                    :   18
%              Number of atoms          :  594 (11154 expanded)
%              Number of equality atoms :  193 (4213 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_140,negated_conjecture,(
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

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_113,axiom,(
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

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_123,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_127,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_192,plain,(
    ! [A_51,A_52,B_53] :
      ( v1_relat_1(A_51)
      | ~ r1_tarski(A_51,k2_zfmisc_1(A_52,B_53)) ) ),
    inference(resolution,[status(thm)],[c_18,c_127])).

tff(c_212,plain,(
    ! [A_52,B_53] : v1_relat_1(k2_zfmisc_1(A_52,B_53)) ),
    inference(resolution,[status(thm)],[c_6,c_192])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_144,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_127])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_68,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_66,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_18252,plain,(
    ! [A_1202,B_1203,C_1204] :
      ( k2_relset_1(A_1202,B_1203,C_1204) = k2_relat_1(C_1204)
      | ~ m1_subset_1(C_1204,k1_zfmisc_1(k2_zfmisc_1(A_1202,B_1203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_18265,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_18252])).

tff(c_18280,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_18265])).

tff(c_34,plain,(
    ! [A_15] :
      ( k1_relat_1(k2_funct_1(A_15)) = k2_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    ! [A_14] :
      ( v1_funct_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_64,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_146,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_149,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_146])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_74,c_149])).

tff(c_154,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_233,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_250,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_233])).

tff(c_72,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4930,plain,(
    ! [A_316,B_317,C_318] :
      ( k1_relset_1(A_316,B_317,C_318) = k1_relat_1(C_318)
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(A_316,B_317))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4956,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_4930])).

tff(c_5616,plain,(
    ! [B_378,A_379,C_380] :
      ( k1_xboole_0 = B_378
      | k1_relset_1(A_379,B_378,C_380) = A_379
      | ~ v1_funct_2(C_380,A_379,B_378)
      | ~ m1_subset_1(C_380,k1_zfmisc_1(k2_zfmisc_1(A_379,B_378))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5629,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_5616])).

tff(c_5644,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4956,c_5629])).

tff(c_5648,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5644])).

tff(c_978,plain,(
    ! [A_149,B_150,C_151] :
      ( k1_relset_1(A_149,B_150,C_151) = k1_relat_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1005,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_978])).

tff(c_1345,plain,(
    ! [B_187,A_188,C_189] :
      ( k1_xboole_0 = B_187
      | k1_relset_1(A_188,B_187,C_189) = A_188
      | ~ v1_funct_2(C_189,A_188,B_187)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_188,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1358,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_1345])).

tff(c_1376,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1005,c_1358])).

tff(c_1380,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1376])).

tff(c_32,plain,(
    ! [A_15] :
      ( k2_relat_1(k2_funct_1(A_15)) = k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    ! [A_14] :
      ( v1_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_658,plain,(
    ! [A_119,B_120,C_121] :
      ( k2_relset_1(A_119,B_120,C_121) = k2_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_665,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_658])).

tff(c_678,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_665])).

tff(c_548,plain,(
    ! [A_107] :
      ( k1_relat_1(k2_funct_1(A_107)) = k2_relat_1(A_107)
      | ~ v2_funct_1(A_107)
      | ~ v1_funct_1(A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_251,plain,(
    ! [B_59,A_60] :
      ( v4_relat_1(B_59,A_60)
      | ~ r1_tarski(k1_relat_1(B_59),A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_256,plain,(
    ! [B_59] :
      ( v4_relat_1(B_59,k1_relat_1(B_59))
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_251])).

tff(c_2510,plain,(
    ! [A_237] :
      ( v4_relat_1(k2_funct_1(A_237),k2_relat_1(A_237))
      | ~ v1_relat_1(k2_funct_1(A_237))
      | ~ v2_funct_1(A_237)
      | ~ v1_funct_1(A_237)
      | ~ v1_relat_1(A_237) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_256])).

tff(c_2513,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_678,c_2510])).

tff(c_2518,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_74,c_68,c_2513])).

tff(c_2519,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2518])).

tff(c_2522,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_2519])).

tff(c_2526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_74,c_2522])).

tff(c_2528,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2518])).

tff(c_26,plain,(
    ! [A_13] :
      ( r1_tarski(A_13,k2_zfmisc_1(k1_relat_1(A_13),k2_relat_1(A_13)))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4396,plain,(
    ! [A_299] :
      ( r1_tarski(k2_funct_1(A_299),k2_zfmisc_1(k2_relat_1(A_299),k2_relat_1(k2_funct_1(A_299))))
      | ~ v1_relat_1(k2_funct_1(A_299))
      | ~ v2_funct_1(A_299)
      | ~ v1_funct_1(A_299)
      | ~ v1_relat_1(A_299) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_26])).

tff(c_4422,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_678,c_4396])).

tff(c_4438,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_74,c_68,c_2528,c_4422])).

tff(c_4507,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_4438])).

tff(c_4523,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_74,c_68,c_1380,c_4507])).

tff(c_4525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_250,c_4523])).

tff(c_4526,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1376])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_113,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_125,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_14,c_113])).

tff(c_4567,plain,(
    ! [A_5] : r1_tarski('#skF_2',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4526,c_125])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4569,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4526,c_4526,c_10])).

tff(c_689,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_678,c_26])).

tff(c_697,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_689])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_720,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_697,c_2])).

tff(c_827,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_720])).

tff(c_4786,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4569,c_827])).

tff(c_4796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4567,c_4786])).

tff(c_4797,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_720])).

tff(c_5659,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5648,c_4797])).

tff(c_124,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_113])).

tff(c_220,plain,(
    ! [B_56,A_57] :
      ( B_56 = A_57
      | ~ r1_tarski(B_56,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_227,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_124,c_220])).

tff(c_290,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_5751,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5659,c_290])).

tff(c_5756,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5751])).

tff(c_5757,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_5644])).

tff(c_5799,plain,(
    ! [A_5] : r1_tarski('#skF_2',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5757,c_125])).

tff(c_5801,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5757,c_5757,c_10])).

tff(c_5991,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5801,c_290])).

tff(c_5996,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5799,c_5991])).

tff(c_5997,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_6000,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5997,c_70])).

tff(c_6543,plain,(
    ! [A_454,B_455,C_456] :
      ( k1_relset_1(A_454,B_455,C_456) = k1_relat_1(C_456)
      | ~ m1_subset_1(C_456,k1_zfmisc_1(k2_zfmisc_1(A_454,B_455))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6596,plain,(
    ! [C_463] :
      ( k1_relset_1('#skF_1','#skF_2',C_463) = k1_relat_1(C_463)
      | ~ m1_subset_1(C_463,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5997,c_6543])).

tff(c_6608,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6000,c_6596])).

tff(c_8253,plain,(
    ! [B_564,A_565,C_566] :
      ( k1_xboole_0 = B_564
      | k1_relset_1(A_565,B_564,C_566) = A_565
      | ~ v1_funct_2(C_566,A_565,B_564)
      | ~ m1_subset_1(C_566,k1_zfmisc_1(k2_zfmisc_1(A_565,B_564))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_8262,plain,(
    ! [C_566] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_566) = '#skF_1'
      | ~ v1_funct_2(C_566,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_566,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5997,c_8253])).

tff(c_8310,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_8262])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6012,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_5997,c_8])).

tff(c_6084,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6012])).

tff(c_8342,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8310,c_6084])).

tff(c_8590,plain,(
    ! [A_578] : k2_zfmisc_1(A_578,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8310,c_8310,c_10])).

tff(c_7404,plain,(
    ! [B_539,A_540,C_541] :
      ( k1_xboole_0 = B_539
      | k1_relset_1(A_540,B_539,C_541) = A_540
      | ~ v1_funct_2(C_541,A_540,B_539)
      | ~ m1_subset_1(C_541,k1_zfmisc_1(k2_zfmisc_1(A_540,B_539))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_7413,plain,(
    ! [C_541] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_541) = '#skF_1'
      | ~ v1_funct_2(C_541,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_541,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5997,c_7404])).

tff(c_7487,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7413])).

tff(c_7529,plain,(
    ! [A_5] : r1_tarski('#skF_2',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7487,c_125])).

tff(c_7531,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7487,c_7487,c_10])).

tff(c_6689,plain,(
    ! [A_472,B_473,C_474] :
      ( k2_relset_1(A_472,B_473,C_474) = k2_relat_1(C_474)
      | ~ m1_subset_1(C_474,k1_zfmisc_1(k2_zfmisc_1(A_472,B_473))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6741,plain,(
    ! [C_481] :
      ( k2_relset_1('#skF_1','#skF_2',C_481) = k2_relat_1(C_481)
      | ~ m1_subset_1(C_481,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5997,c_6689])).

tff(c_6744,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6000,c_6741])).

tff(c_6754,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6744])).

tff(c_6767,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6754,c_26])).

tff(c_6775,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_6767])).

tff(c_6795,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_6775,c_2])).

tff(c_7395,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6795])).

tff(c_7777,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7531,c_7395])).

tff(c_7783,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7529,c_7777])).

tff(c_8129,plain,(
    ! [C_561] :
      ( k1_relset_1('#skF_1','#skF_2',C_561) = '#skF_1'
      | ~ v1_funct_2(C_561,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_561,k1_zfmisc_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_7413])).

tff(c_8132,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_6000,c_8129])).

tff(c_8143,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6608,c_8132])).

tff(c_8147,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8143,c_7395])).

tff(c_8158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5997,c_8147])).

tff(c_8159,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6795])).

tff(c_8600,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_8590,c_8159])).

tff(c_8731,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8342,c_8600])).

tff(c_8883,plain,(
    ! [C_588] :
      ( k1_relset_1('#skF_1','#skF_2',C_588) = '#skF_1'
      | ~ v1_funct_2(C_588,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_588,k1_zfmisc_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_8262])).

tff(c_8886,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_6000,c_8883])).

tff(c_8897,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6608,c_8886])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6236,plain,(
    ! [C_403,B_404,A_405] :
      ( v5_relat_1(C_403,B_404)
      | ~ m1_subset_1(C_403,k1_zfmisc_1(k2_zfmisc_1(A_405,B_404))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6317,plain,(
    ! [A_422,B_423,A_424] :
      ( v5_relat_1(A_422,B_423)
      | ~ r1_tarski(A_422,k2_zfmisc_1(A_424,B_423)) ) ),
    inference(resolution,[status(thm)],[c_18,c_6236])).

tff(c_6463,plain,(
    ! [B_441,B_442,A_443] :
      ( v5_relat_1(k1_relat_1(B_441),B_442)
      | ~ v4_relat_1(B_441,k2_zfmisc_1(A_443,B_442))
      | ~ v1_relat_1(B_441) ) ),
    inference(resolution,[status(thm)],[c_24,c_6317])).

tff(c_6486,plain,(
    ! [B_444] :
      ( v5_relat_1(k1_relat_1(B_444),'#skF_2')
      | ~ v4_relat_1(B_444,'#skF_3')
      | ~ v1_relat_1(B_444) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5997,c_6463])).

tff(c_6852,plain,(
    ! [A_489] :
      ( v5_relat_1(k2_relat_1(A_489),'#skF_2')
      | ~ v4_relat_1(k2_funct_1(A_489),'#skF_3')
      | ~ v1_relat_1(k2_funct_1(A_489))
      | ~ v2_funct_1(A_489)
      | ~ v1_funct_1(A_489)
      | ~ v1_relat_1(A_489) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_6486])).

tff(c_6855,plain,
    ( v5_relat_1('#skF_2','#skF_2')
    | ~ v4_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6754,c_6852])).

tff(c_6860,plain,
    ( v5_relat_1('#skF_2','#skF_2')
    | ~ v4_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_74,c_68,c_6855])).

tff(c_6919,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6860])).

tff(c_6922,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_6919])).

tff(c_6926,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_74,c_6922])).

tff(c_6928,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6860])).

tff(c_6347,plain,(
    ! [A_425] :
      ( k1_relat_1(k2_funct_1(A_425)) = k2_relat_1(A_425)
      | ~ v2_funct_1(A_425)
      | ~ v1_funct_1(A_425)
      | ~ v1_relat_1(A_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12007,plain,(
    ! [A_694] :
      ( r1_tarski(k2_funct_1(A_694),k2_zfmisc_1(k2_relat_1(A_694),k2_relat_1(k2_funct_1(A_694))))
      | ~ v1_relat_1(k2_funct_1(A_694))
      | ~ v2_funct_1(A_694)
      | ~ v1_funct_1(A_694)
      | ~ v1_relat_1(A_694) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6347,c_26])).

tff(c_12033,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6754,c_12007])).

tff(c_12049,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_74,c_68,c_6928,c_12033])).

tff(c_12080,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_12049])).

tff(c_12096,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_74,c_68,c_8897,c_12080])).

tff(c_12098,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_250,c_12096])).

tff(c_12100,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6012])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12112,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12100,c_12100,c_12])).

tff(c_12099,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_6012])).

tff(c_12192,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12100,c_12100,c_12099])).

tff(c_12193,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_12192])).

tff(c_12196,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12193,c_233])).

tff(c_12200,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12112,c_12196])).

tff(c_12113,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12100,c_14])).

tff(c_12842,plain,(
    ! [A_788,B_789,C_790] :
      ( k2_relset_1(A_788,B_789,C_790) = k2_relat_1(C_790)
      | ~ m1_subset_1(C_790,k1_zfmisc_1(k2_zfmisc_1(A_788,B_789))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_12859,plain,(
    ! [A_791,B_792] : k2_relset_1(A_791,B_792,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12113,c_12842])).

tff(c_12197,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12193,c_12193,c_66])).

tff(c_12863,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_12859,c_12197])).

tff(c_12492,plain,(
    ! [A_739] :
      ( k1_relat_1(k2_funct_1(A_739)) = k2_relat_1(A_739)
      | ~ v2_funct_1(A_739)
      | ~ v1_funct_1(A_739)
      | ~ v1_relat_1(A_739) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14266,plain,(
    ! [A_883] :
      ( v4_relat_1(k2_funct_1(A_883),k2_relat_1(A_883))
      | ~ v1_relat_1(k2_funct_1(A_883))
      | ~ v2_funct_1(A_883)
      | ~ v1_funct_1(A_883)
      | ~ v1_relat_1(A_883) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12492,c_256])).

tff(c_14269,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12863,c_14266])).

tff(c_14274,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_74,c_68,c_14269])).

tff(c_14275,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_14274])).

tff(c_14278,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_14275])).

tff(c_14282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_74,c_14278])).

tff(c_14284,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_14274])).

tff(c_155,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_14283,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_14274])).

tff(c_6025,plain,(
    ! [B_385,A_386] :
      ( r1_tarski(k1_relat_1(B_385),A_386)
      | ~ v4_relat_1(B_385,A_386)
      | ~ v1_relat_1(B_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_228,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_125,c_220])).

tff(c_6044,plain,(
    ! [B_385] :
      ( k1_relat_1(B_385) = k1_xboole_0
      | ~ v4_relat_1(B_385,k1_xboole_0)
      | ~ v1_relat_1(B_385) ) ),
    inference(resolution,[status(thm)],[c_6025,c_228])).

tff(c_12425,plain,(
    ! [B_385] :
      ( k1_relat_1(B_385) = '#skF_3'
      | ~ v4_relat_1(B_385,'#skF_3')
      | ~ v1_relat_1(B_385) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12100,c_12100,c_6044])).

tff(c_14293,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14283,c_12425])).

tff(c_14302,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14284,c_14293])).

tff(c_58,plain,(
    ! [A_31] :
      ( m1_subset_1(A_31,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_31),k2_relat_1(A_31))))
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_14366,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14302,c_58])).

tff(c_14449,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14284,c_155,c_12112,c_14366])).

tff(c_14451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12200,c_14449])).

tff(c_14452,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12192])).

tff(c_12111,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12100,c_12100,c_10])).

tff(c_14520,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14452,c_14452,c_12111])).

tff(c_14462,plain,(
    ~ r1_tarski(k2_funct_1('#skF_1'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14452,c_250])).

tff(c_14620,plain,(
    ~ r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14520,c_14462])).

tff(c_14465,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14452,c_144])).

tff(c_14469,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14452,c_74])).

tff(c_14468,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14452,c_68])).

tff(c_14455,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14452,c_14452,c_12112])).

tff(c_258,plain,(
    ! [C_62,A_63,B_64] :
      ( v4_relat_1(C_62,A_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14719,plain,(
    ! [A_914,A_915,B_916] :
      ( v4_relat_1(A_914,A_915)
      | ~ r1_tarski(A_914,k2_zfmisc_1(A_915,B_916)) ) ),
    inference(resolution,[status(thm)],[c_18,c_258])).

tff(c_14745,plain,(
    ! [A_915,B_916] : v4_relat_1(k2_zfmisc_1(A_915,B_916),A_915) ),
    inference(resolution,[status(thm)],[c_6,c_14719])).

tff(c_14458,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14452,c_12100])).

tff(c_14801,plain,(
    ! [B_926] :
      ( k1_relat_1(B_926) = '#skF_1'
      | ~ v4_relat_1(B_926,'#skF_1')
      | ~ v1_relat_1(B_926) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14458,c_14458,c_6044])).

tff(c_14805,plain,(
    ! [B_916] :
      ( k1_relat_1(k2_zfmisc_1('#skF_1',B_916)) = '#skF_1'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1',B_916)) ) ),
    inference(resolution,[status(thm)],[c_14745,c_14801])).

tff(c_14816,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_14455,c_14805])).

tff(c_14454,plain,(
    ! [A_5] : m1_subset_1('#skF_1',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14452,c_12113])).

tff(c_15106,plain,(
    ! [A_959,B_960,C_961] :
      ( k2_relset_1(A_959,B_960,C_961) = k2_relat_1(C_961)
      | ~ m1_subset_1(C_961,k1_zfmisc_1(k2_zfmisc_1(A_959,B_960))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_15127,plain,(
    ! [A_962,B_963] : k2_relset_1(A_962,B_963,'#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_14454,c_15106])).

tff(c_14466,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14452,c_66])).

tff(c_15131,plain,(
    k2_relat_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_15127,c_14466])).

tff(c_14643,plain,(
    ! [A_905] :
      ( k1_relat_1(k2_funct_1(A_905)) = k2_relat_1(A_905)
      | ~ v2_funct_1(A_905)
      | ~ v1_funct_1(A_905)
      | ~ v1_relat_1(A_905) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16593,plain,(
    ! [A_1072] :
      ( v4_relat_1(k2_funct_1(A_1072),k2_relat_1(A_1072))
      | ~ v1_relat_1(k2_funct_1(A_1072))
      | ~ v2_funct_1(A_1072)
      | ~ v1_funct_1(A_1072)
      | ~ v1_relat_1(A_1072) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14643,c_256])).

tff(c_16596,plain,
    ( v4_relat_1(k2_funct_1('#skF_1'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15131,c_16593])).

tff(c_16601,plain,
    ( v4_relat_1(k2_funct_1('#skF_1'),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14465,c_14469,c_14468,c_16596])).

tff(c_16602,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_16601])).

tff(c_16605,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_16602])).

tff(c_16609,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14465,c_14469,c_16605])).

tff(c_16611,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_16601])).

tff(c_17415,plain,(
    ! [A_1103] :
      ( r1_tarski(k2_funct_1(A_1103),k2_zfmisc_1(k2_relat_1(A_1103),k2_relat_1(k2_funct_1(A_1103))))
      | ~ v1_relat_1(k2_funct_1(A_1103))
      | ~ v2_funct_1(A_1103)
      | ~ v1_funct_1(A_1103)
      | ~ v1_relat_1(A_1103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14643,c_26])).

tff(c_17435,plain,
    ( r1_tarski(k2_funct_1('#skF_1'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_1'))))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15131,c_17415])).

tff(c_17449,plain,(
    r1_tarski(k2_funct_1('#skF_1'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14465,c_14469,c_14468,c_16611,c_17435])).

tff(c_17478,plain,
    ( r1_tarski(k2_funct_1('#skF_1'),k2_zfmisc_1('#skF_2',k1_relat_1('#skF_1')))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_17449])).

tff(c_17489,plain,(
    r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14465,c_14469,c_14468,c_14520,c_14816,c_17478])).

tff(c_17491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14620,c_17489])).

tff(c_17492,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_17493,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_18207,plain,(
    ! [A_1197,B_1198,C_1199] :
      ( k1_relset_1(A_1197,B_1198,C_1199) = k1_relat_1(C_1199)
      | ~ m1_subset_1(C_1199,k1_zfmisc_1(k2_zfmisc_1(A_1197,B_1198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_18232,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_17493,c_18207])).

tff(c_18587,plain,(
    ! [B_1233,C_1234,A_1235] :
      ( k1_xboole_0 = B_1233
      | v1_funct_2(C_1234,A_1235,B_1233)
      | k1_relset_1(A_1235,B_1233,C_1234) != A_1235
      | ~ m1_subset_1(C_1234,k1_zfmisc_1(k2_zfmisc_1(A_1235,B_1233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_18596,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_17493,c_18587])).

tff(c_18619,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18232,c_18596])).

tff(c_18620,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_17492,c_18619])).

tff(c_18627,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_18620])).

tff(c_18630,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_18627])).

tff(c_18633,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_74,c_68,c_18280,c_18630])).

tff(c_18634,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18620])).

tff(c_18673,plain,(
    ! [A_5] : r1_tarski('#skF_1',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18634,c_125])).

tff(c_18676,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18634,c_18634,c_12])).

tff(c_17549,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_18924,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18676,c_17549])).

tff(c_18929,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18673,c_18924])).

tff(c_18930,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_18933,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18930,c_70])).

tff(c_19564,plain,(
    ! [A_1321,B_1322,C_1323] :
      ( k2_relset_1(A_1321,B_1322,C_1323) = k2_relat_1(C_1323)
      | ~ m1_subset_1(C_1323,k1_zfmisc_1(k2_zfmisc_1(A_1321,B_1322))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_19609,plain,(
    ! [C_1328] :
      ( k2_relset_1('#skF_1','#skF_2',C_1328) = k2_relat_1(C_1328)
      | ~ m1_subset_1(C_1328,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18930,c_19564])).

tff(c_19612,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18933,c_19609])).

tff(c_19622,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_19612])).

tff(c_19677,plain,(
    ! [A_1331,B_1332,C_1333] :
      ( k1_relset_1(A_1331,B_1332,C_1333) = k1_relat_1(C_1333)
      | ~ m1_subset_1(C_1333,k1_zfmisc_1(k2_zfmisc_1(A_1331,B_1332))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_19698,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_17493,c_19677])).

tff(c_20428,plain,(
    ! [B_1402,C_1403,A_1404] :
      ( k1_xboole_0 = B_1402
      | v1_funct_2(C_1403,A_1404,B_1402)
      | k1_relset_1(A_1404,B_1402,C_1403) != A_1404
      | ~ m1_subset_1(C_1403,k1_zfmisc_1(k2_zfmisc_1(A_1404,B_1402))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_20440,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_17493,c_20428])).

tff(c_20460,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19698,c_20440])).

tff(c_20461,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_17492,c_20460])).

tff(c_20466,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_20461])).

tff(c_20469,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_20466])).

tff(c_20472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_74,c_68,c_19622,c_20469])).

tff(c_20473,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_20461])).

tff(c_18945,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_18930,c_8])).

tff(c_18995,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_18945])).

tff(c_20509,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20473,c_18995])).

tff(c_20519,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_1',B_4) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20473,c_20473,c_12])).

tff(c_20768,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20519,c_18930])).

tff(c_20770,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20509,c_20768])).

tff(c_20772,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18945])).

tff(c_20782,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_3',B_4) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20772,c_20772,c_12])).

tff(c_17523,plain,(
    ! [C_1105,A_1106,B_1107] :
      ( v4_relat_1(C_1105,A_1106)
      | ~ m1_subset_1(C_1105,k1_zfmisc_1(k2_zfmisc_1(A_1106,B_1107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_21108,plain,(
    ! [A_1449,A_1450,B_1451] :
      ( v4_relat_1(A_1449,A_1450)
      | ~ r1_tarski(A_1449,k2_zfmisc_1(A_1450,B_1451)) ) ),
    inference(resolution,[status(thm)],[c_18,c_17523])).

tff(c_21134,plain,(
    ! [A_1450,B_1451] : v4_relat_1(k2_zfmisc_1(A_1450,B_1451),A_1450) ),
    inference(resolution,[status(thm)],[c_6,c_21108])).

tff(c_20985,plain,(
    ! [B_1423,A_1424] :
      ( r1_tarski(k1_relat_1(B_1423),A_1424)
      | ~ v4_relat_1(B_1423,A_1424)
      | ~ v1_relat_1(B_1423) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20774,plain,(
    ! [A_5] :
      ( A_5 = '#skF_3'
      | ~ r1_tarski(A_5,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20772,c_20772,c_228])).

tff(c_21156,plain,(
    ! [B_1457] :
      ( k1_relat_1(B_1457) = '#skF_3'
      | ~ v4_relat_1(B_1457,'#skF_3')
      | ~ v1_relat_1(B_1457) ) ),
    inference(resolution,[status(thm)],[c_20985,c_20774])).

tff(c_21160,plain,(
    ! [B_1451] :
      ( k1_relat_1(k2_zfmisc_1('#skF_3',B_1451)) = '#skF_3'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_3',B_1451)) ) ),
    inference(resolution,[status(thm)],[c_21134,c_21156])).

tff(c_21171,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_20782,c_21160])).

tff(c_20783,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20772,c_14])).

tff(c_21714,plain,(
    ! [A_1516,B_1517,C_1518] :
      ( k1_relset_1(A_1516,B_1517,C_1518) = k1_relat_1(C_1518)
      | ~ m1_subset_1(C_1518,k1_zfmisc_1(k2_zfmisc_1(A_1516,B_1517))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_21724,plain,(
    ! [A_1516,B_1517] : k1_relset_1(A_1516,B_1517,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20783,c_21714])).

tff(c_21734,plain,(
    ! [A_1516,B_1517] : k1_relset_1(A_1516,B_1517,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21171,c_21724])).

tff(c_50,plain,(
    ! [C_30,B_29] :
      ( v1_funct_2(C_30,k1_xboole_0,B_29)
      | k1_relset_1(k1_xboole_0,B_29,C_30) != k1_xboole_0
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_78,plain,(
    ! [C_30,B_29] :
      ( v1_funct_2(C_30,k1_xboole_0,B_29)
      | k1_relset_1(k1_xboole_0,B_29,C_30) != k1_xboole_0
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_50])).

tff(c_21866,plain,(
    ! [C_1538,B_1539] :
      ( v1_funct_2(C_1538,'#skF_3',B_1539)
      | k1_relset_1('#skF_3',B_1539,C_1538) != '#skF_3'
      | ~ m1_subset_1(C_1538,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20772,c_20772,c_20772,c_20772,c_78])).

tff(c_21869,plain,(
    ! [B_1539] :
      ( v1_funct_2('#skF_3','#skF_3',B_1539)
      | k1_relset_1('#skF_3',B_1539,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_20783,c_21866])).

tff(c_21875,plain,(
    ! [B_1539] : v1_funct_2('#skF_3','#skF_3',B_1539) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21734,c_21869])).

tff(c_20771,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_18945])).

tff(c_20820,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20772,c_20772,c_20771])).

tff(c_20821,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_20820])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_17514,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_17493,c_16])).

tff(c_20824,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20821,c_17514])).

tff(c_20944,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20782,c_20824])).

tff(c_20953,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20944,c_20774])).

tff(c_20826,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20821,c_17492])).

tff(c_20960,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20953,c_20826])).

tff(c_21880,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21875,c_20960])).

tff(c_21881,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_20820])).

tff(c_21882,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_20820])).

tff(c_21906,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21881,c_21882])).

tff(c_46,plain,(
    ! [A_28] :
      ( v1_funct_2(k1_xboole_0,A_28,k1_xboole_0)
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_28,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_76,plain,(
    ! [A_28] :
      ( v1_funct_2(k1_xboole_0,A_28,k1_xboole_0)
      | k1_xboole_0 = A_28 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_46])).

tff(c_20780,plain,(
    ! [A_28] :
      ( v1_funct_2('#skF_3',A_28,'#skF_3')
      | A_28 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20772,c_20772,c_20772,c_76])).

tff(c_22091,plain,(
    ! [A_28] :
      ( v1_funct_2('#skF_1',A_28,'#skF_1')
      | A_28 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21881,c_21881,c_21881,c_20780])).

tff(c_20781,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20772,c_20772,c_10])).

tff(c_21935,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21881,c_21881,c_20781])).

tff(c_21894,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21881,c_17493])).

tff(c_22093,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21935,c_21894])).

tff(c_22100,plain,(
    r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_22093,c_16])).

tff(c_22064,plain,(
    ! [A_5] :
      ( A_5 = '#skF_1'
      | ~ r1_tarski(A_5,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21881,c_21881,c_20774])).

tff(c_22109,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22100,c_22064])).

tff(c_21895,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21881,c_17492])).

tff(c_22117,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22109,c_21895])).

tff(c_22145,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22091,c_22117])).

tff(c_22149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21906,c_22145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:17:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.38/3.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.38/3.88  
% 10.38/3.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.38/3.88  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.38/3.88  
% 10.38/3.88  %Foreground sorts:
% 10.38/3.88  
% 10.38/3.88  
% 10.38/3.88  %Background operators:
% 10.38/3.88  
% 10.38/3.88  
% 10.38/3.88  %Foreground operators:
% 10.38/3.88  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.38/3.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.38/3.88  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.38/3.88  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.38/3.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.38/3.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.38/3.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.38/3.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.38/3.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.38/3.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.38/3.88  tff('#skF_2', type, '#skF_2': $i).
% 10.38/3.88  tff('#skF_3', type, '#skF_3': $i).
% 10.38/3.88  tff('#skF_1', type, '#skF_1': $i).
% 10.38/3.88  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.38/3.88  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.38/3.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.38/3.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.38/3.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.38/3.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.38/3.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.38/3.88  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.38/3.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.38/3.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.38/3.88  
% 10.75/3.92  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.75/3.92  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.75/3.92  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.75/3.92  tff(f_140, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 10.75/3.92  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.75/3.92  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 10.75/3.92  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.75/3.92  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.75/3.92  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 10.75/3.92  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 10.75/3.92  tff(f_59, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 10.75/3.92  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 10.75/3.92  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.75/3.92  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.75/3.92  tff(f_123, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 10.75/3.92  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.75/3.92  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.75/3.92  tff(c_127, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.75/3.92  tff(c_192, plain, (![A_51, A_52, B_53]: (v1_relat_1(A_51) | ~r1_tarski(A_51, k2_zfmisc_1(A_52, B_53)))), inference(resolution, [status(thm)], [c_18, c_127])).
% 10.75/3.92  tff(c_212, plain, (![A_52, B_53]: (v1_relat_1(k2_zfmisc_1(A_52, B_53)))), inference(resolution, [status(thm)], [c_6, c_192])).
% 10.75/3.92  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 10.75/3.92  tff(c_144, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_127])).
% 10.75/3.92  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 10.75/3.92  tff(c_68, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 10.75/3.92  tff(c_66, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_140])).
% 10.75/3.92  tff(c_18252, plain, (![A_1202, B_1203, C_1204]: (k2_relset_1(A_1202, B_1203, C_1204)=k2_relat_1(C_1204) | ~m1_subset_1(C_1204, k1_zfmisc_1(k2_zfmisc_1(A_1202, B_1203))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.75/3.92  tff(c_18265, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_18252])).
% 10.75/3.92  tff(c_18280, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_18265])).
% 10.75/3.92  tff(c_34, plain, (![A_15]: (k1_relat_1(k2_funct_1(A_15))=k2_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.75/3.92  tff(c_28, plain, (![A_14]: (v1_funct_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.75/3.92  tff(c_64, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 10.75/3.92  tff(c_146, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_64])).
% 10.75/3.92  tff(c_149, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_146])).
% 10.75/3.92  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_74, c_149])).
% 10.75/3.92  tff(c_154, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_64])).
% 10.75/3.92  tff(c_233, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_154])).
% 10.75/3.92  tff(c_250, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_18, c_233])).
% 10.75/3.92  tff(c_72, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_140])).
% 10.75/3.92  tff(c_4930, plain, (![A_316, B_317, C_318]: (k1_relset_1(A_316, B_317, C_318)=k1_relat_1(C_318) | ~m1_subset_1(C_318, k1_zfmisc_1(k2_zfmisc_1(A_316, B_317))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.75/3.92  tff(c_4956, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_4930])).
% 10.75/3.92  tff(c_5616, plain, (![B_378, A_379, C_380]: (k1_xboole_0=B_378 | k1_relset_1(A_379, B_378, C_380)=A_379 | ~v1_funct_2(C_380, A_379, B_378) | ~m1_subset_1(C_380, k1_zfmisc_1(k2_zfmisc_1(A_379, B_378))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.75/3.92  tff(c_5629, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_5616])).
% 10.75/3.92  tff(c_5644, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4956, c_5629])).
% 10.75/3.92  tff(c_5648, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_5644])).
% 10.75/3.92  tff(c_978, plain, (![A_149, B_150, C_151]: (k1_relset_1(A_149, B_150, C_151)=k1_relat_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.75/3.92  tff(c_1005, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_978])).
% 10.75/3.92  tff(c_1345, plain, (![B_187, A_188, C_189]: (k1_xboole_0=B_187 | k1_relset_1(A_188, B_187, C_189)=A_188 | ~v1_funct_2(C_189, A_188, B_187) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_188, B_187))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.75/3.92  tff(c_1358, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_1345])).
% 10.75/3.92  tff(c_1376, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1005, c_1358])).
% 10.75/3.92  tff(c_1380, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1376])).
% 10.75/3.92  tff(c_32, plain, (![A_15]: (k2_relat_1(k2_funct_1(A_15))=k1_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.75/3.92  tff(c_30, plain, (![A_14]: (v1_relat_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.75/3.92  tff(c_658, plain, (![A_119, B_120, C_121]: (k2_relset_1(A_119, B_120, C_121)=k2_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.75/3.92  tff(c_665, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_658])).
% 10.75/3.92  tff(c_678, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_665])).
% 10.75/3.92  tff(c_548, plain, (![A_107]: (k1_relat_1(k2_funct_1(A_107))=k2_relat_1(A_107) | ~v2_funct_1(A_107) | ~v1_funct_1(A_107) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.75/3.92  tff(c_251, plain, (![B_59, A_60]: (v4_relat_1(B_59, A_60) | ~r1_tarski(k1_relat_1(B_59), A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.75/3.92  tff(c_256, plain, (![B_59]: (v4_relat_1(B_59, k1_relat_1(B_59)) | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_6, c_251])).
% 10.75/3.92  tff(c_2510, plain, (![A_237]: (v4_relat_1(k2_funct_1(A_237), k2_relat_1(A_237)) | ~v1_relat_1(k2_funct_1(A_237)) | ~v2_funct_1(A_237) | ~v1_funct_1(A_237) | ~v1_relat_1(A_237))), inference(superposition, [status(thm), theory('equality')], [c_548, c_256])).
% 10.75/3.92  tff(c_2513, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_678, c_2510])).
% 10.75/3.92  tff(c_2518, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_74, c_68, c_2513])).
% 10.75/3.92  tff(c_2519, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2518])).
% 10.75/3.92  tff(c_2522, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_2519])).
% 10.75/3.92  tff(c_2526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_74, c_2522])).
% 10.75/3.92  tff(c_2528, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2518])).
% 10.75/3.92  tff(c_26, plain, (![A_13]: (r1_tarski(A_13, k2_zfmisc_1(k1_relat_1(A_13), k2_relat_1(A_13))) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.75/3.92  tff(c_4396, plain, (![A_299]: (r1_tarski(k2_funct_1(A_299), k2_zfmisc_1(k2_relat_1(A_299), k2_relat_1(k2_funct_1(A_299)))) | ~v1_relat_1(k2_funct_1(A_299)) | ~v2_funct_1(A_299) | ~v1_funct_1(A_299) | ~v1_relat_1(A_299))), inference(superposition, [status(thm), theory('equality')], [c_548, c_26])).
% 10.75/3.92  tff(c_4422, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_678, c_4396])).
% 10.75/3.92  tff(c_4438, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_74, c_68, c_2528, c_4422])).
% 10.75/3.92  tff(c_4507, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_4438])).
% 10.75/3.92  tff(c_4523, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_74, c_68, c_1380, c_4507])).
% 10.75/3.92  tff(c_4525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_250, c_4523])).
% 10.75/3.92  tff(c_4526, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1376])).
% 10.75/3.92  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.75/3.92  tff(c_113, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.75/3.92  tff(c_125, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_14, c_113])).
% 10.75/3.92  tff(c_4567, plain, (![A_5]: (r1_tarski('#skF_2', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_4526, c_125])).
% 10.75/3.92  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.75/3.92  tff(c_4569, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4526, c_4526, c_10])).
% 10.75/3.92  tff(c_689, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_678, c_26])).
% 10.75/3.92  tff(c_697, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_689])).
% 10.75/3.92  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.75/3.92  tff(c_720, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_697, c_2])).
% 10.75/3.92  tff(c_827, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_720])).
% 10.75/3.92  tff(c_4786, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4569, c_827])).
% 10.75/3.92  tff(c_4796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4567, c_4786])).
% 10.75/3.92  tff(c_4797, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_720])).
% 10.75/3.92  tff(c_5659, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5648, c_4797])).
% 10.75/3.92  tff(c_124, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_113])).
% 10.75/3.92  tff(c_220, plain, (![B_56, A_57]: (B_56=A_57 | ~r1_tarski(B_56, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.75/3.92  tff(c_227, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_124, c_220])).
% 10.75/3.92  tff(c_290, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_227])).
% 10.75/3.92  tff(c_5751, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5659, c_290])).
% 10.75/3.92  tff(c_5756, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5751])).
% 10.75/3.92  tff(c_5757, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_5644])).
% 10.75/3.92  tff(c_5799, plain, (![A_5]: (r1_tarski('#skF_2', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_5757, c_125])).
% 10.75/3.92  tff(c_5801, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5757, c_5757, c_10])).
% 10.75/3.92  tff(c_5991, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5801, c_290])).
% 10.75/3.92  tff(c_5996, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5799, c_5991])).
% 10.75/3.92  tff(c_5997, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_227])).
% 10.75/3.92  tff(c_6000, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5997, c_70])).
% 10.75/3.92  tff(c_6543, plain, (![A_454, B_455, C_456]: (k1_relset_1(A_454, B_455, C_456)=k1_relat_1(C_456) | ~m1_subset_1(C_456, k1_zfmisc_1(k2_zfmisc_1(A_454, B_455))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.75/3.92  tff(c_6596, plain, (![C_463]: (k1_relset_1('#skF_1', '#skF_2', C_463)=k1_relat_1(C_463) | ~m1_subset_1(C_463, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5997, c_6543])).
% 10.75/3.92  tff(c_6608, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6000, c_6596])).
% 10.75/3.92  tff(c_8253, plain, (![B_564, A_565, C_566]: (k1_xboole_0=B_564 | k1_relset_1(A_565, B_564, C_566)=A_565 | ~v1_funct_2(C_566, A_565, B_564) | ~m1_subset_1(C_566, k1_zfmisc_1(k2_zfmisc_1(A_565, B_564))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.75/3.92  tff(c_8262, plain, (![C_566]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_566)='#skF_1' | ~v1_funct_2(C_566, '#skF_1', '#skF_2') | ~m1_subset_1(C_566, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5997, c_8253])).
% 10.75/3.92  tff(c_8310, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_8262])).
% 10.75/3.92  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.75/3.92  tff(c_6012, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_5997, c_8])).
% 10.75/3.92  tff(c_6084, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_6012])).
% 10.75/3.92  tff(c_8342, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8310, c_6084])).
% 10.75/3.92  tff(c_8590, plain, (![A_578]: (k2_zfmisc_1(A_578, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8310, c_8310, c_10])).
% 10.75/3.92  tff(c_7404, plain, (![B_539, A_540, C_541]: (k1_xboole_0=B_539 | k1_relset_1(A_540, B_539, C_541)=A_540 | ~v1_funct_2(C_541, A_540, B_539) | ~m1_subset_1(C_541, k1_zfmisc_1(k2_zfmisc_1(A_540, B_539))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.75/3.92  tff(c_7413, plain, (![C_541]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_541)='#skF_1' | ~v1_funct_2(C_541, '#skF_1', '#skF_2') | ~m1_subset_1(C_541, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5997, c_7404])).
% 10.75/3.92  tff(c_7487, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_7413])).
% 10.75/3.92  tff(c_7529, plain, (![A_5]: (r1_tarski('#skF_2', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_7487, c_125])).
% 10.75/3.92  tff(c_7531, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7487, c_7487, c_10])).
% 10.75/3.92  tff(c_6689, plain, (![A_472, B_473, C_474]: (k2_relset_1(A_472, B_473, C_474)=k2_relat_1(C_474) | ~m1_subset_1(C_474, k1_zfmisc_1(k2_zfmisc_1(A_472, B_473))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.75/3.92  tff(c_6741, plain, (![C_481]: (k2_relset_1('#skF_1', '#skF_2', C_481)=k2_relat_1(C_481) | ~m1_subset_1(C_481, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5997, c_6689])).
% 10.75/3.92  tff(c_6744, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6000, c_6741])).
% 10.75/3.92  tff(c_6754, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_6744])).
% 10.75/3.92  tff(c_6767, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6754, c_26])).
% 10.75/3.92  tff(c_6775, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_6767])).
% 10.75/3.92  tff(c_6795, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_6775, c_2])).
% 10.75/3.92  tff(c_7395, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_6795])).
% 10.75/3.92  tff(c_7777, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7531, c_7395])).
% 10.75/3.92  tff(c_7783, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7529, c_7777])).
% 10.75/3.92  tff(c_8129, plain, (![C_561]: (k1_relset_1('#skF_1', '#skF_2', C_561)='#skF_1' | ~v1_funct_2(C_561, '#skF_1', '#skF_2') | ~m1_subset_1(C_561, k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_7413])).
% 10.75/3.92  tff(c_8132, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_6000, c_8129])).
% 10.75/3.92  tff(c_8143, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6608, c_8132])).
% 10.75/3.92  tff(c_8147, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8143, c_7395])).
% 10.75/3.92  tff(c_8158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5997, c_8147])).
% 10.75/3.92  tff(c_8159, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_6795])).
% 10.75/3.92  tff(c_8600, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_8590, c_8159])).
% 10.75/3.92  tff(c_8731, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8342, c_8600])).
% 10.75/3.92  tff(c_8883, plain, (![C_588]: (k1_relset_1('#skF_1', '#skF_2', C_588)='#skF_1' | ~v1_funct_2(C_588, '#skF_1', '#skF_2') | ~m1_subset_1(C_588, k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_8262])).
% 10.75/3.92  tff(c_8886, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_6000, c_8883])).
% 10.75/3.92  tff(c_8897, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6608, c_8886])).
% 10.75/3.92  tff(c_24, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.75/3.92  tff(c_6236, plain, (![C_403, B_404, A_405]: (v5_relat_1(C_403, B_404) | ~m1_subset_1(C_403, k1_zfmisc_1(k2_zfmisc_1(A_405, B_404))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.75/3.92  tff(c_6317, plain, (![A_422, B_423, A_424]: (v5_relat_1(A_422, B_423) | ~r1_tarski(A_422, k2_zfmisc_1(A_424, B_423)))), inference(resolution, [status(thm)], [c_18, c_6236])).
% 10.75/3.92  tff(c_6463, plain, (![B_441, B_442, A_443]: (v5_relat_1(k1_relat_1(B_441), B_442) | ~v4_relat_1(B_441, k2_zfmisc_1(A_443, B_442)) | ~v1_relat_1(B_441))), inference(resolution, [status(thm)], [c_24, c_6317])).
% 10.75/3.92  tff(c_6486, plain, (![B_444]: (v5_relat_1(k1_relat_1(B_444), '#skF_2') | ~v4_relat_1(B_444, '#skF_3') | ~v1_relat_1(B_444))), inference(superposition, [status(thm), theory('equality')], [c_5997, c_6463])).
% 10.75/3.92  tff(c_6852, plain, (![A_489]: (v5_relat_1(k2_relat_1(A_489), '#skF_2') | ~v4_relat_1(k2_funct_1(A_489), '#skF_3') | ~v1_relat_1(k2_funct_1(A_489)) | ~v2_funct_1(A_489) | ~v1_funct_1(A_489) | ~v1_relat_1(A_489))), inference(superposition, [status(thm), theory('equality')], [c_34, c_6486])).
% 10.75/3.92  tff(c_6855, plain, (v5_relat_1('#skF_2', '#skF_2') | ~v4_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6754, c_6852])).
% 10.75/3.92  tff(c_6860, plain, (v5_relat_1('#skF_2', '#skF_2') | ~v4_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_74, c_68, c_6855])).
% 10.75/3.92  tff(c_6919, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_6860])).
% 10.75/3.92  tff(c_6922, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_6919])).
% 10.75/3.92  tff(c_6926, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_74, c_6922])).
% 10.75/3.92  tff(c_6928, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_6860])).
% 10.75/3.92  tff(c_6347, plain, (![A_425]: (k1_relat_1(k2_funct_1(A_425))=k2_relat_1(A_425) | ~v2_funct_1(A_425) | ~v1_funct_1(A_425) | ~v1_relat_1(A_425))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.75/3.92  tff(c_12007, plain, (![A_694]: (r1_tarski(k2_funct_1(A_694), k2_zfmisc_1(k2_relat_1(A_694), k2_relat_1(k2_funct_1(A_694)))) | ~v1_relat_1(k2_funct_1(A_694)) | ~v2_funct_1(A_694) | ~v1_funct_1(A_694) | ~v1_relat_1(A_694))), inference(superposition, [status(thm), theory('equality')], [c_6347, c_26])).
% 10.75/3.92  tff(c_12033, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6754, c_12007])).
% 10.75/3.92  tff(c_12049, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_74, c_68, c_6928, c_12033])).
% 10.75/3.92  tff(c_12080, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_12049])).
% 10.75/3.92  tff(c_12096, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_74, c_68, c_8897, c_12080])).
% 10.75/3.92  tff(c_12098, plain, $false, inference(negUnitSimplification, [status(thm)], [c_250, c_12096])).
% 10.75/3.92  tff(c_12100, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_6012])).
% 10.75/3.92  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.75/3.92  tff(c_12112, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12100, c_12100, c_12])).
% 10.75/3.92  tff(c_12099, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_6012])).
% 10.75/3.92  tff(c_12192, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12100, c_12100, c_12099])).
% 10.75/3.92  tff(c_12193, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_12192])).
% 10.75/3.92  tff(c_12196, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_12193, c_233])).
% 10.75/3.92  tff(c_12200, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12112, c_12196])).
% 10.75/3.92  tff(c_12113, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_12100, c_14])).
% 10.75/3.92  tff(c_12842, plain, (![A_788, B_789, C_790]: (k2_relset_1(A_788, B_789, C_790)=k2_relat_1(C_790) | ~m1_subset_1(C_790, k1_zfmisc_1(k2_zfmisc_1(A_788, B_789))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.75/3.92  tff(c_12859, plain, (![A_791, B_792]: (k2_relset_1(A_791, B_792, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_12113, c_12842])).
% 10.75/3.92  tff(c_12197, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12193, c_12193, c_66])).
% 10.75/3.92  tff(c_12863, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_12859, c_12197])).
% 10.75/3.92  tff(c_12492, plain, (![A_739]: (k1_relat_1(k2_funct_1(A_739))=k2_relat_1(A_739) | ~v2_funct_1(A_739) | ~v1_funct_1(A_739) | ~v1_relat_1(A_739))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.75/3.92  tff(c_14266, plain, (![A_883]: (v4_relat_1(k2_funct_1(A_883), k2_relat_1(A_883)) | ~v1_relat_1(k2_funct_1(A_883)) | ~v2_funct_1(A_883) | ~v1_funct_1(A_883) | ~v1_relat_1(A_883))), inference(superposition, [status(thm), theory('equality')], [c_12492, c_256])).
% 10.75/3.92  tff(c_14269, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12863, c_14266])).
% 10.75/3.92  tff(c_14274, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_74, c_68, c_14269])).
% 10.75/3.92  tff(c_14275, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_14274])).
% 10.75/3.92  tff(c_14278, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_14275])).
% 10.75/3.92  tff(c_14282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_74, c_14278])).
% 10.75/3.92  tff(c_14284, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_14274])).
% 10.75/3.92  tff(c_155, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_64])).
% 10.75/3.92  tff(c_14283, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_14274])).
% 10.75/3.92  tff(c_6025, plain, (![B_385, A_386]: (r1_tarski(k1_relat_1(B_385), A_386) | ~v4_relat_1(B_385, A_386) | ~v1_relat_1(B_385))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.75/3.92  tff(c_228, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_125, c_220])).
% 10.75/3.92  tff(c_6044, plain, (![B_385]: (k1_relat_1(B_385)=k1_xboole_0 | ~v4_relat_1(B_385, k1_xboole_0) | ~v1_relat_1(B_385))), inference(resolution, [status(thm)], [c_6025, c_228])).
% 10.75/3.92  tff(c_12425, plain, (![B_385]: (k1_relat_1(B_385)='#skF_3' | ~v4_relat_1(B_385, '#skF_3') | ~v1_relat_1(B_385))), inference(demodulation, [status(thm), theory('equality')], [c_12100, c_12100, c_6044])).
% 10.75/3.92  tff(c_14293, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_14283, c_12425])).
% 10.75/3.92  tff(c_14302, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14284, c_14293])).
% 10.75/3.92  tff(c_58, plain, (![A_31]: (m1_subset_1(A_31, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_31), k2_relat_1(A_31)))) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.75/3.92  tff(c_14366, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14302, c_58])).
% 10.75/3.92  tff(c_14449, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14284, c_155, c_12112, c_14366])).
% 10.75/3.92  tff(c_14451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12200, c_14449])).
% 10.75/3.92  tff(c_14452, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_12192])).
% 10.75/3.92  tff(c_12111, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12100, c_12100, c_10])).
% 10.75/3.92  tff(c_14520, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14452, c_14452, c_12111])).
% 10.75/3.92  tff(c_14462, plain, (~r1_tarski(k2_funct_1('#skF_1'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14452, c_250])).
% 10.75/3.92  tff(c_14620, plain, (~r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14520, c_14462])).
% 10.75/3.92  tff(c_14465, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14452, c_144])).
% 10.75/3.92  tff(c_14469, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14452, c_74])).
% 10.75/3.92  tff(c_14468, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14452, c_68])).
% 10.75/3.92  tff(c_14455, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14452, c_14452, c_12112])).
% 10.75/3.92  tff(c_258, plain, (![C_62, A_63, B_64]: (v4_relat_1(C_62, A_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.75/3.92  tff(c_14719, plain, (![A_914, A_915, B_916]: (v4_relat_1(A_914, A_915) | ~r1_tarski(A_914, k2_zfmisc_1(A_915, B_916)))), inference(resolution, [status(thm)], [c_18, c_258])).
% 10.75/3.92  tff(c_14745, plain, (![A_915, B_916]: (v4_relat_1(k2_zfmisc_1(A_915, B_916), A_915))), inference(resolution, [status(thm)], [c_6, c_14719])).
% 10.75/3.92  tff(c_14458, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14452, c_12100])).
% 10.75/3.92  tff(c_14801, plain, (![B_926]: (k1_relat_1(B_926)='#skF_1' | ~v4_relat_1(B_926, '#skF_1') | ~v1_relat_1(B_926))), inference(demodulation, [status(thm), theory('equality')], [c_14458, c_14458, c_6044])).
% 10.75/3.92  tff(c_14805, plain, (![B_916]: (k1_relat_1(k2_zfmisc_1('#skF_1', B_916))='#skF_1' | ~v1_relat_1(k2_zfmisc_1('#skF_1', B_916)))), inference(resolution, [status(thm)], [c_14745, c_14801])).
% 10.75/3.92  tff(c_14816, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_212, c_14455, c_14805])).
% 10.75/3.92  tff(c_14454, plain, (![A_5]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_14452, c_12113])).
% 10.75/3.92  tff(c_15106, plain, (![A_959, B_960, C_961]: (k2_relset_1(A_959, B_960, C_961)=k2_relat_1(C_961) | ~m1_subset_1(C_961, k1_zfmisc_1(k2_zfmisc_1(A_959, B_960))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.75/3.92  tff(c_15127, plain, (![A_962, B_963]: (k2_relset_1(A_962, B_963, '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_14454, c_15106])).
% 10.75/3.92  tff(c_14466, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14452, c_66])).
% 10.75/3.92  tff(c_15131, plain, (k2_relat_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_15127, c_14466])).
% 10.75/3.92  tff(c_14643, plain, (![A_905]: (k1_relat_1(k2_funct_1(A_905))=k2_relat_1(A_905) | ~v2_funct_1(A_905) | ~v1_funct_1(A_905) | ~v1_relat_1(A_905))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.75/3.92  tff(c_16593, plain, (![A_1072]: (v4_relat_1(k2_funct_1(A_1072), k2_relat_1(A_1072)) | ~v1_relat_1(k2_funct_1(A_1072)) | ~v2_funct_1(A_1072) | ~v1_funct_1(A_1072) | ~v1_relat_1(A_1072))), inference(superposition, [status(thm), theory('equality')], [c_14643, c_256])).
% 10.75/3.92  tff(c_16596, plain, (v4_relat_1(k2_funct_1('#skF_1'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15131, c_16593])).
% 10.75/3.92  tff(c_16601, plain, (v4_relat_1(k2_funct_1('#skF_1'), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14465, c_14469, c_14468, c_16596])).
% 10.75/3.92  tff(c_16602, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_16601])).
% 10.75/3.92  tff(c_16605, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_30, c_16602])).
% 10.75/3.92  tff(c_16609, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14465, c_14469, c_16605])).
% 10.75/3.92  tff(c_16611, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_16601])).
% 10.75/3.92  tff(c_17415, plain, (![A_1103]: (r1_tarski(k2_funct_1(A_1103), k2_zfmisc_1(k2_relat_1(A_1103), k2_relat_1(k2_funct_1(A_1103)))) | ~v1_relat_1(k2_funct_1(A_1103)) | ~v2_funct_1(A_1103) | ~v1_funct_1(A_1103) | ~v1_relat_1(A_1103))), inference(superposition, [status(thm), theory('equality')], [c_14643, c_26])).
% 10.75/3.92  tff(c_17435, plain, (r1_tarski(k2_funct_1('#skF_1'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_1')))) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15131, c_17415])).
% 10.75/3.92  tff(c_17449, plain, (r1_tarski(k2_funct_1('#skF_1'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_14465, c_14469, c_14468, c_16611, c_17435])).
% 10.75/3.92  tff(c_17478, plain, (r1_tarski(k2_funct_1('#skF_1'), k2_zfmisc_1('#skF_2', k1_relat_1('#skF_1'))) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_17449])).
% 10.75/3.92  tff(c_17489, plain, (r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_14465, c_14469, c_14468, c_14520, c_14816, c_17478])).
% 10.75/3.92  tff(c_17491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14620, c_17489])).
% 10.75/3.92  tff(c_17492, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_154])).
% 10.75/3.92  tff(c_17493, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_154])).
% 10.75/3.92  tff(c_18207, plain, (![A_1197, B_1198, C_1199]: (k1_relset_1(A_1197, B_1198, C_1199)=k1_relat_1(C_1199) | ~m1_subset_1(C_1199, k1_zfmisc_1(k2_zfmisc_1(A_1197, B_1198))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.75/3.92  tff(c_18232, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_17493, c_18207])).
% 10.75/3.92  tff(c_18587, plain, (![B_1233, C_1234, A_1235]: (k1_xboole_0=B_1233 | v1_funct_2(C_1234, A_1235, B_1233) | k1_relset_1(A_1235, B_1233, C_1234)!=A_1235 | ~m1_subset_1(C_1234, k1_zfmisc_1(k2_zfmisc_1(A_1235, B_1233))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.75/3.92  tff(c_18596, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_17493, c_18587])).
% 10.75/3.92  tff(c_18619, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18232, c_18596])).
% 10.75/3.92  tff(c_18620, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_17492, c_18619])).
% 10.75/3.92  tff(c_18627, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_18620])).
% 10.75/3.92  tff(c_18630, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_18627])).
% 10.75/3.92  tff(c_18633, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_74, c_68, c_18280, c_18630])).
% 10.75/3.92  tff(c_18634, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_18620])).
% 10.75/3.92  tff(c_18673, plain, (![A_5]: (r1_tarski('#skF_1', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_18634, c_125])).
% 10.75/3.92  tff(c_18676, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18634, c_18634, c_12])).
% 10.75/3.92  tff(c_17549, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_227])).
% 10.75/3.92  tff(c_18924, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18676, c_17549])).
% 10.75/3.92  tff(c_18929, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18673, c_18924])).
% 10.75/3.92  tff(c_18930, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_227])).
% 10.75/3.92  tff(c_18933, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18930, c_70])).
% 10.75/3.92  tff(c_19564, plain, (![A_1321, B_1322, C_1323]: (k2_relset_1(A_1321, B_1322, C_1323)=k2_relat_1(C_1323) | ~m1_subset_1(C_1323, k1_zfmisc_1(k2_zfmisc_1(A_1321, B_1322))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.75/3.92  tff(c_19609, plain, (![C_1328]: (k2_relset_1('#skF_1', '#skF_2', C_1328)=k2_relat_1(C_1328) | ~m1_subset_1(C_1328, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_18930, c_19564])).
% 10.75/3.92  tff(c_19612, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18933, c_19609])).
% 10.75/3.92  tff(c_19622, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_19612])).
% 10.75/3.92  tff(c_19677, plain, (![A_1331, B_1332, C_1333]: (k1_relset_1(A_1331, B_1332, C_1333)=k1_relat_1(C_1333) | ~m1_subset_1(C_1333, k1_zfmisc_1(k2_zfmisc_1(A_1331, B_1332))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.75/3.92  tff(c_19698, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_17493, c_19677])).
% 10.75/3.92  tff(c_20428, plain, (![B_1402, C_1403, A_1404]: (k1_xboole_0=B_1402 | v1_funct_2(C_1403, A_1404, B_1402) | k1_relset_1(A_1404, B_1402, C_1403)!=A_1404 | ~m1_subset_1(C_1403, k1_zfmisc_1(k2_zfmisc_1(A_1404, B_1402))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.75/3.92  tff(c_20440, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_17493, c_20428])).
% 10.75/3.92  tff(c_20460, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_19698, c_20440])).
% 10.75/3.92  tff(c_20461, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_17492, c_20460])).
% 10.75/3.92  tff(c_20466, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_20461])).
% 10.75/3.92  tff(c_20469, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_20466])).
% 10.75/3.92  tff(c_20472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_144, c_74, c_68, c_19622, c_20469])).
% 10.75/3.92  tff(c_20473, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_20461])).
% 10.75/3.92  tff(c_18945, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_18930, c_8])).
% 10.75/3.92  tff(c_18995, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_18945])).
% 10.75/3.92  tff(c_20509, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20473, c_18995])).
% 10.75/3.92  tff(c_20519, plain, (![B_4]: (k2_zfmisc_1('#skF_1', B_4)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20473, c_20473, c_12])).
% 10.75/3.92  tff(c_20768, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20519, c_18930])).
% 10.75/3.92  tff(c_20770, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20509, c_20768])).
% 10.75/3.92  tff(c_20772, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_18945])).
% 10.75/3.92  tff(c_20782, plain, (![B_4]: (k2_zfmisc_1('#skF_3', B_4)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20772, c_20772, c_12])).
% 10.75/3.92  tff(c_17523, plain, (![C_1105, A_1106, B_1107]: (v4_relat_1(C_1105, A_1106) | ~m1_subset_1(C_1105, k1_zfmisc_1(k2_zfmisc_1(A_1106, B_1107))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.75/3.92  tff(c_21108, plain, (![A_1449, A_1450, B_1451]: (v4_relat_1(A_1449, A_1450) | ~r1_tarski(A_1449, k2_zfmisc_1(A_1450, B_1451)))), inference(resolution, [status(thm)], [c_18, c_17523])).
% 10.75/3.92  tff(c_21134, plain, (![A_1450, B_1451]: (v4_relat_1(k2_zfmisc_1(A_1450, B_1451), A_1450))), inference(resolution, [status(thm)], [c_6, c_21108])).
% 10.75/3.92  tff(c_20985, plain, (![B_1423, A_1424]: (r1_tarski(k1_relat_1(B_1423), A_1424) | ~v4_relat_1(B_1423, A_1424) | ~v1_relat_1(B_1423))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.75/3.92  tff(c_20774, plain, (![A_5]: (A_5='#skF_3' | ~r1_tarski(A_5, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20772, c_20772, c_228])).
% 10.75/3.92  tff(c_21156, plain, (![B_1457]: (k1_relat_1(B_1457)='#skF_3' | ~v4_relat_1(B_1457, '#skF_3') | ~v1_relat_1(B_1457))), inference(resolution, [status(thm)], [c_20985, c_20774])).
% 10.75/3.92  tff(c_21160, plain, (![B_1451]: (k1_relat_1(k2_zfmisc_1('#skF_3', B_1451))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_3', B_1451)))), inference(resolution, [status(thm)], [c_21134, c_21156])).
% 10.75/3.92  tff(c_21171, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_212, c_20782, c_21160])).
% 10.75/3.92  tff(c_20783, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_20772, c_14])).
% 10.75/3.92  tff(c_21714, plain, (![A_1516, B_1517, C_1518]: (k1_relset_1(A_1516, B_1517, C_1518)=k1_relat_1(C_1518) | ~m1_subset_1(C_1518, k1_zfmisc_1(k2_zfmisc_1(A_1516, B_1517))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.75/3.92  tff(c_21724, plain, (![A_1516, B_1517]: (k1_relset_1(A_1516, B_1517, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_20783, c_21714])).
% 10.75/3.92  tff(c_21734, plain, (![A_1516, B_1517]: (k1_relset_1(A_1516, B_1517, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21171, c_21724])).
% 10.75/3.92  tff(c_50, plain, (![C_30, B_29]: (v1_funct_2(C_30, k1_xboole_0, B_29) | k1_relset_1(k1_xboole_0, B_29, C_30)!=k1_xboole_0 | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_29))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.75/3.92  tff(c_78, plain, (![C_30, B_29]: (v1_funct_2(C_30, k1_xboole_0, B_29) | k1_relset_1(k1_xboole_0, B_29, C_30)!=k1_xboole_0 | ~m1_subset_1(C_30, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_50])).
% 10.75/3.92  tff(c_21866, plain, (![C_1538, B_1539]: (v1_funct_2(C_1538, '#skF_3', B_1539) | k1_relset_1('#skF_3', B_1539, C_1538)!='#skF_3' | ~m1_subset_1(C_1538, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_20772, c_20772, c_20772, c_20772, c_78])).
% 10.75/3.92  tff(c_21869, plain, (![B_1539]: (v1_funct_2('#skF_3', '#skF_3', B_1539) | k1_relset_1('#skF_3', B_1539, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_20783, c_21866])).
% 10.75/3.92  tff(c_21875, plain, (![B_1539]: (v1_funct_2('#skF_3', '#skF_3', B_1539))), inference(demodulation, [status(thm), theory('equality')], [c_21734, c_21869])).
% 10.75/3.92  tff(c_20771, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_18945])).
% 10.75/3.92  tff(c_20820, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20772, c_20772, c_20771])).
% 10.75/3.92  tff(c_20821, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_20820])).
% 10.75/3.92  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.75/3.92  tff(c_17514, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_17493, c_16])).
% 10.75/3.92  tff(c_20824, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20821, c_17514])).
% 10.75/3.92  tff(c_20944, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20782, c_20824])).
% 10.75/3.92  tff(c_20953, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_20944, c_20774])).
% 10.75/3.92  tff(c_20826, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20821, c_17492])).
% 10.75/3.92  tff(c_20960, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20953, c_20826])).
% 10.75/3.92  tff(c_21880, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21875, c_20960])).
% 10.75/3.92  tff(c_21881, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_20820])).
% 10.75/3.92  tff(c_21882, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_20820])).
% 10.75/3.92  tff(c_21906, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_21881, c_21882])).
% 10.75/3.92  tff(c_46, plain, (![A_28]: (v1_funct_2(k1_xboole_0, A_28, k1_xboole_0) | k1_xboole_0=A_28 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_28, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.75/3.92  tff(c_76, plain, (![A_28]: (v1_funct_2(k1_xboole_0, A_28, k1_xboole_0) | k1_xboole_0=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_46])).
% 10.75/3.92  tff(c_20780, plain, (![A_28]: (v1_funct_2('#skF_3', A_28, '#skF_3') | A_28='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20772, c_20772, c_20772, c_76])).
% 10.75/3.92  tff(c_22091, plain, (![A_28]: (v1_funct_2('#skF_1', A_28, '#skF_1') | A_28='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21881, c_21881, c_21881, c_20780])).
% 10.75/3.92  tff(c_20781, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20772, c_20772, c_10])).
% 10.75/3.92  tff(c_21935, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21881, c_21881, c_20781])).
% 10.75/3.92  tff(c_21894, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_21881, c_17493])).
% 10.75/3.92  tff(c_22093, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_21935, c_21894])).
% 10.75/3.92  tff(c_22100, plain, (r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_22093, c_16])).
% 10.75/3.92  tff(c_22064, plain, (![A_5]: (A_5='#skF_1' | ~r1_tarski(A_5, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_21881, c_21881, c_20774])).
% 10.75/3.92  tff(c_22109, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_22100, c_22064])).
% 10.75/3.92  tff(c_21895, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_21881, c_17492])).
% 10.75/3.92  tff(c_22117, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22109, c_21895])).
% 10.75/3.92  tff(c_22145, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_22091, c_22117])).
% 10.75/3.92  tff(c_22149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21906, c_22145])).
% 10.75/3.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.75/3.92  
% 10.75/3.92  Inference rules
% 10.75/3.92  ----------------------
% 10.75/3.92  #Ref     : 0
% 10.75/3.92  #Sup     : 4663
% 10.75/3.92  #Fact    : 0
% 10.75/3.92  #Define  : 0
% 10.75/3.92  #Split   : 45
% 10.75/3.92  #Chain   : 0
% 10.75/3.92  #Close   : 0
% 10.75/3.92  
% 10.75/3.92  Ordering : KBO
% 10.75/3.92  
% 10.75/3.92  Simplification rules
% 10.75/3.92  ----------------------
% 10.75/3.92  #Subsume      : 632
% 10.75/3.92  #Demod        : 6624
% 10.75/3.92  #Tautology    : 2338
% 10.75/3.92  #SimpNegUnit  : 31
% 10.75/3.92  #BackRed      : 461
% 10.75/3.92  
% 10.75/3.92  #Partial instantiations: 0
% 10.75/3.92  #Strategies tried      : 1
% 10.75/3.92  
% 10.75/3.92  Timing (in seconds)
% 10.75/3.92  ----------------------
% 10.75/3.92  Preprocessing        : 0.34
% 10.75/3.92  Parsing              : 0.17
% 10.75/3.92  CNF conversion       : 0.02
% 10.75/3.92  Main loop            : 2.67
% 10.75/3.92  Inferencing          : 0.82
% 10.75/3.92  Reduction            : 1.04
% 10.75/3.92  Demodulation         : 0.77
% 10.75/3.92  BG Simplification    : 0.08
% 10.75/3.92  Subsumption          : 0.54
% 10.75/3.92  Abstraction          : 0.10
% 10.75/3.92  MUC search           : 0.00
% 10.75/3.92  Cooper               : 0.00
% 10.75/3.92  Total                : 3.12
% 10.75/3.92  Index Insertion      : 0.00
% 10.75/3.92  Index Deletion       : 0.00
% 10.75/3.92  Index Matching       : 0.00
% 10.75/3.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
