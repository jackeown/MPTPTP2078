%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:38 EST 2020

% Result     : Theorem 10.21s
% Output     : CNFRefutation 10.30s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 902 expanded)
%              Number of leaves         :   41 ( 316 expanded)
%              Depth                    :   14
%              Number of atoms          :  394 (2592 expanded)
%              Number of equality atoms :   89 ( 593 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_160,negated_conjecture,(
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

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_124,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_143,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(B,C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_114,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_15930,plain,(
    ! [C_753,A_754,B_755] :
      ( v4_relat_1(C_753,A_754)
      | ~ m1_subset_1(C_753,k1_zfmisc_1(k2_zfmisc_1(A_754,B_755))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_15947,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_15930])).

tff(c_15804,plain,(
    ! [C_742,A_743,B_744] :
      ( v1_relat_1(C_742)
      | ~ m1_subset_1(C_742,k1_zfmisc_1(k2_zfmisc_1(A_743,B_744))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_15821,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_15804])).

tff(c_18,plain,(
    ! [A_9] :
      ( k1_relat_1(A_9) != k1_xboole_0
      | k1_xboole_0 = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_15830,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_15821,c_18])).

tff(c_15874,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_15830])).

tff(c_82,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_24,plain,(
    ! [A_11] :
      ( v1_funct_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_72,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_150,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_153,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_150])).

tff(c_156,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_153])).

tff(c_194,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_200,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_194])).

tff(c_210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_200])).

tff(c_212,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_76,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_28,plain,(
    ! [A_12] :
      ( k2_relat_1(k2_funct_1(A_12)) = k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_351,plain,(
    ! [C_79,A_80,B_81] :
      ( v4_relat_1(C_79,A_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_364,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_351])).

tff(c_251,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_264,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_251])).

tff(c_280,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_264,c_18])).

tff(c_305,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_280])).

tff(c_26,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_74,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1123,plain,(
    ! [A_148,B_149,C_150] :
      ( k2_relset_1(A_148,B_149,C_150) = k2_relat_1(C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1132,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_1123])).

tff(c_1140,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1132])).

tff(c_711,plain,(
    ! [A_123] :
      ( k1_relat_1(k2_funct_1(A_123)) = k2_relat_1(A_123)
      | ~ v2_funct_1(A_123)
      | ~ v1_funct_1(A_123)
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_56,plain,(
    ! [A_29] :
      ( v1_funct_2(A_29,k1_relat_1(A_29),k2_relat_1(A_29))
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_7147,plain,(
    ! [A_380] :
      ( v1_funct_2(k2_funct_1(A_380),k2_relat_1(A_380),k2_relat_1(k2_funct_1(A_380)))
      | ~ v1_funct_1(k2_funct_1(A_380))
      | ~ v1_relat_1(k2_funct_1(A_380))
      | ~ v2_funct_1(A_380)
      | ~ v1_funct_1(A_380)
      | ~ v1_relat_1(A_380) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_711,c_56])).

tff(c_7174,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1140,c_7147])).

tff(c_7206,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_82,c_76,c_212,c_7174])).

tff(c_7213,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7206])).

tff(c_7216,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_7213])).

tff(c_7220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_82,c_7216])).

tff(c_7221,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_7206])).

tff(c_7244,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_7221])).

tff(c_7248,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_82,c_76,c_7244])).

tff(c_7222,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7206])).

tff(c_30,plain,(
    ! [A_12] :
      ( k1_relat_1(k2_funct_1(A_12)) = k2_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1009,plain,(
    ! [A_143] :
      ( m1_subset_1(A_143,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_143),k2_relat_1(A_143))))
      | ~ v1_funct_1(A_143)
      | ~ v1_relat_1(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_7266,plain,(
    ! [A_381] :
      ( m1_subset_1(k2_funct_1(A_381),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_381),k2_relat_1(k2_funct_1(A_381)))))
      | ~ v1_funct_1(k2_funct_1(A_381))
      | ~ v1_relat_1(k2_funct_1(A_381))
      | ~ v2_funct_1(A_381)
      | ~ v1_funct_1(A_381)
      | ~ v1_relat_1(A_381) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1009])).

tff(c_7310,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1140,c_7266])).

tff(c_7348,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_82,c_76,c_7222,c_212,c_7310])).

tff(c_7379,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4'))))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_7348])).

tff(c_7390,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_82,c_76,c_7379])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1837,plain,(
    ! [B_190,D_191,A_192,C_193] :
      ( k1_xboole_0 = B_190
      | m1_subset_1(D_191,k1_zfmisc_1(k2_zfmisc_1(A_192,C_193)))
      | ~ r1_tarski(B_190,C_193)
      | ~ m1_subset_1(D_191,k1_zfmisc_1(k2_zfmisc_1(A_192,B_190)))
      | ~ v1_funct_2(D_191,A_192,B_190)
      | ~ v1_funct_1(D_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_10043,plain,(
    ! [B_459,D_460,A_461,A_462] :
      ( k1_relat_1(B_459) = k1_xboole_0
      | m1_subset_1(D_460,k1_zfmisc_1(k2_zfmisc_1(A_461,A_462)))
      | ~ m1_subset_1(D_460,k1_zfmisc_1(k2_zfmisc_1(A_461,k1_relat_1(B_459))))
      | ~ v1_funct_2(D_460,A_461,k1_relat_1(B_459))
      | ~ v1_funct_1(D_460)
      | ~ v4_relat_1(B_459,A_462)
      | ~ v1_relat_1(B_459) ) ),
    inference(resolution,[status(thm)],[c_12,c_1837])).

tff(c_10047,plain,(
    ! [A_462] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_462)))
      | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v4_relat_1('#skF_4',A_462)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_7390,c_10043])).

tff(c_10078,plain,(
    ! [A_462] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_462)))
      | ~ v4_relat_1('#skF_4',A_462) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_212,c_7248,c_10047])).

tff(c_10103,plain,(
    ! [A_463] :
      ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_463)))
      | ~ v4_relat_1('#skF_4',A_463) ) ),
    inference(negUnitSimplification,[status(thm)],[c_305,c_10078])).

tff(c_211,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_213,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_10129,plain,(
    ~ v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_10103,c_213])).

tff(c_10147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_10129])).

tff(c_10148,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_6,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10158,plain,(
    ! [A_2] : m1_subset_1('#skF_4',k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10148,c_6])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_92,plain,(
    ! [A_40] :
      ( v1_xboole_0(k2_relat_1(A_40))
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_103,plain,(
    ! [A_45] :
      ( k2_relat_1(A_45) = k1_xboole_0
      | ~ v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_92,c_4])).

tff(c_111,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_103])).

tff(c_10156,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10148,c_10148,c_111])).

tff(c_10558,plain,(
    ! [A_509] :
      ( k1_relat_1(k2_funct_1(A_509)) = k2_relat_1(A_509)
      | ~ v2_funct_1(A_509)
      | ~ v1_funct_1(A_509)
      | ~ v1_relat_1(A_509) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_15621,plain,(
    ! [A_735] :
      ( v1_funct_2(k2_funct_1(A_735),k2_relat_1(A_735),k2_relat_1(k2_funct_1(A_735)))
      | ~ v1_funct_1(k2_funct_1(A_735))
      | ~ v1_relat_1(k2_funct_1(A_735))
      | ~ v2_funct_1(A_735)
      | ~ v1_funct_1(A_735)
      | ~ v1_relat_1(A_735) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10558,c_56])).

tff(c_15660,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10156,c_15621])).

tff(c_15676,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_82,c_76,c_212,c_15660])).

tff(c_15677,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_15676])).

tff(c_15680,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_15677])).

tff(c_15684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_82,c_15680])).

tff(c_15686,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_15676])).

tff(c_10153,plain,(
    ! [A_9] :
      ( k1_relat_1(A_9) != '#skF_4'
      | A_9 = '#skF_4'
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10148,c_10148,c_18])).

tff(c_15701,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_15686,c_10153])).

tff(c_15763,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_15701])).

tff(c_15766,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_15763])).

tff(c_15769,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_82,c_76,c_10156,c_15766])).

tff(c_15770,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_15701])).

tff(c_10832,plain,(
    ! [A_528,B_529,C_530] :
      ( k2_relset_1(A_528,B_529,C_530) = k2_relat_1(C_530)
      | ~ m1_subset_1(C_530,k1_zfmisc_1(k2_zfmisc_1(A_528,B_529))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_10839,plain,(
    ! [A_528,B_529] : k2_relset_1(A_528,B_529,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10158,c_10832])).

tff(c_10845,plain,(
    ! [A_528,B_529] : k2_relset_1(A_528,B_529,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10156,c_10839])).

tff(c_10847,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10845,c_74])).

tff(c_10855,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10847,c_213])).

tff(c_15775,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15770,c_10855])).

tff(c_15782,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10158,c_15775])).

tff(c_15784,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_15820,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_15784,c_15804])).

tff(c_16422,plain,(
    ! [A_803,B_804,C_805] :
      ( k2_relset_1(A_803,B_804,C_805) = k2_relat_1(C_805)
      | ~ m1_subset_1(C_805,k1_zfmisc_1(k2_zfmisc_1(A_803,B_804))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_16434,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_16422])).

tff(c_16443,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_16434])).

tff(c_16162,plain,(
    ! [A_788] :
      ( k1_relat_1(k2_funct_1(A_788)) = k2_relat_1(A_788)
      | ~ v2_funct_1(A_788)
      | ~ v1_funct_1(A_788)
      | ~ v1_relat_1(A_788) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_21415,plain,(
    ! [A_1021] :
      ( v1_funct_2(k2_funct_1(A_1021),k2_relat_1(A_1021),k2_relat_1(k2_funct_1(A_1021)))
      | ~ v1_funct_1(k2_funct_1(A_1021))
      | ~ v1_relat_1(k2_funct_1(A_1021))
      | ~ v2_funct_1(A_1021)
      | ~ v1_funct_1(A_1021)
      | ~ v1_relat_1(A_1021) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16162,c_56])).

tff(c_21442,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_16443,c_21415])).

tff(c_21471,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15821,c_82,c_76,c_15820,c_212,c_21442])).

tff(c_21481,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_21471])).

tff(c_21485,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15821,c_82,c_76,c_21481])).

tff(c_16280,plain,(
    ! [A_797] :
      ( m1_subset_1(A_797,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_797),k2_relat_1(A_797))))
      | ~ v1_funct_1(A_797)
      | ~ v1_relat_1(A_797) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_21801,plain,(
    ! [A_1032] :
      ( m1_subset_1(k2_funct_1(A_1032),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1032),k2_relat_1(k2_funct_1(A_1032)))))
      | ~ v1_funct_1(k2_funct_1(A_1032))
      | ~ v1_relat_1(k2_funct_1(A_1032))
      | ~ v2_funct_1(A_1032)
      | ~ v1_funct_1(A_1032)
      | ~ v1_relat_1(A_1032) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_16280])).

tff(c_21845,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_16443,c_21801])).

tff(c_21880,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15821,c_82,c_76,c_15820,c_212,c_21845])).

tff(c_21907,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4'))))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_21880])).

tff(c_21919,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15821,c_82,c_76,c_21907])).

tff(c_16539,plain,(
    ! [B_813,D_814,A_815,C_816] :
      ( k1_xboole_0 = B_813
      | v1_funct_2(D_814,A_815,C_816)
      | ~ r1_tarski(B_813,C_816)
      | ~ m1_subset_1(D_814,k1_zfmisc_1(k2_zfmisc_1(A_815,B_813)))
      | ~ v1_funct_2(D_814,A_815,B_813)
      | ~ v1_funct_1(D_814) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_25358,plain,(
    ! [B_1120,D_1121,A_1122,A_1123] :
      ( k1_relat_1(B_1120) = k1_xboole_0
      | v1_funct_2(D_1121,A_1122,A_1123)
      | ~ m1_subset_1(D_1121,k1_zfmisc_1(k2_zfmisc_1(A_1122,k1_relat_1(B_1120))))
      | ~ v1_funct_2(D_1121,A_1122,k1_relat_1(B_1120))
      | ~ v1_funct_1(D_1121)
      | ~ v4_relat_1(B_1120,A_1123)
      | ~ v1_relat_1(B_1120) ) ),
    inference(resolution,[status(thm)],[c_12,c_16539])).

tff(c_25366,plain,(
    ! [A_1123] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_1123)
      | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v4_relat_1('#skF_4',A_1123)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_21919,c_25358])).

tff(c_25396,plain,(
    ! [A_1123] :
      ( k1_relat_1('#skF_4') = k1_xboole_0
      | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_1123)
      | ~ v4_relat_1('#skF_4',A_1123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15821,c_212,c_21485,c_25366])).

tff(c_25418,plain,(
    ! [A_1124] :
      ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',A_1124)
      | ~ v4_relat_1('#skF_4',A_1124) ) ),
    inference(negUnitSimplification,[status(thm)],[c_15874,c_25396])).

tff(c_15783,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_25421,plain,(
    ~ v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_25418,c_15783])).

tff(c_25425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15947,c_25421])).

tff(c_25426,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_15830])).

tff(c_25434,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25426,c_25426,c_111])).

tff(c_16,plain,(
    ! [A_9] :
      ( k2_relat_1(A_9) != k1_xboole_0
      | k1_xboole_0 = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_15829,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_15821,c_16])).

tff(c_15851,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_15829])).

tff(c_25428,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25426,c_15851])).

tff(c_25461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25434,c_25428])).

tff(c_25462,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_15829])).

tff(c_25472,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25462,c_2])).

tff(c_52,plain,(
    ! [A_26,B_27] : m1_subset_1('#skF_1'(A_26,B_27),k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_25853,plain,(
    ! [C_1184,A_1185,B_1186] :
      ( v1_xboole_0(C_1184)
      | ~ m1_subset_1(C_1184,k1_zfmisc_1(k2_zfmisc_1(A_1185,B_1186)))
      | ~ v1_xboole_0(A_1185) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_25864,plain,(
    ! [A_1187,B_1188] :
      ( v1_xboole_0('#skF_1'(A_1187,B_1188))
      | ~ v1_xboole_0(A_1187) ) ),
    inference(resolution,[status(thm)],[c_52,c_25853])).

tff(c_25471,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25462,c_4])).

tff(c_25873,plain,(
    ! [A_1189,B_1190] :
      ( '#skF_1'(A_1189,B_1190) = '#skF_4'
      | ~ v1_xboole_0(A_1189) ) ),
    inference(resolution,[status(thm)],[c_25864,c_25471])).

tff(c_25883,plain,(
    ! [B_1191] : '#skF_1'('#skF_4',B_1191) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_25472,c_25873])).

tff(c_42,plain,(
    ! [A_26,B_27] : v1_funct_2('#skF_1'(A_26,B_27),A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_25900,plain,(
    ! [B_1191] : v1_funct_2('#skF_4','#skF_4',B_1191) ),
    inference(superposition,[status(thm),theory(equality)],[c_25883,c_42])).

tff(c_25463,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_15829])).

tff(c_25496,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25462,c_25463])).

tff(c_25470,plain,(
    ! [A_2] : m1_subset_1('#skF_4',k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25462,c_6])).

tff(c_26320,plain,(
    ! [A_1220,B_1221,C_1222] :
      ( k2_relset_1(A_1220,B_1221,C_1222) = k2_relat_1(C_1222)
      | ~ m1_subset_1(C_1222,k1_zfmisc_1(k2_zfmisc_1(A_1220,B_1221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_26324,plain,(
    ! [A_1220,B_1221] : k2_relset_1(A_1220,B_1221,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_25470,c_26320])).

tff(c_26329,plain,(
    ! [A_1220,B_1221] : k2_relset_1(A_1220,B_1221,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25496,c_26324])).

tff(c_26331,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26329,c_74])).

tff(c_20,plain,(
    ! [A_10] :
      ( k1_relat_1(A_10) = k1_xboole_0
      | k2_relat_1(A_10) != k1_xboole_0
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_25564,plain,(
    ! [A_1130] :
      ( k1_relat_1(A_1130) = '#skF_4'
      | k2_relat_1(A_1130) != '#skF_4'
      | ~ v1_relat_1(A_1130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25462,c_25462,c_20])).

tff(c_25570,plain,
    ( k1_relat_1('#skF_4') = '#skF_4'
    | k2_relat_1('#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_15821,c_25564])).

tff(c_25580,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25496,c_25570])).

tff(c_25729,plain,(
    ! [A_1160] :
      ( k2_relat_1(k2_funct_1(A_1160)) = k1_relat_1(A_1160)
      | ~ v2_funct_1(A_1160)
      | ~ v1_funct_1(A_1160)
      | ~ v1_relat_1(A_1160) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_15849,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != k1_xboole_0
    | k2_funct_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_15820,c_16])).

tff(c_25607,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4'
    | k2_funct_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25462,c_25462,c_15849])).

tff(c_25608,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_25607])).

tff(c_25738,plain,
    ( k1_relat_1('#skF_4') != '#skF_4'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_25729,c_25608])).

tff(c_25751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15821,c_82,c_76,c_25580,c_25738])).

tff(c_25752,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_25607])).

tff(c_25756,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25752,c_15783])).

tff(c_26339,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26331,c_25756])).

tff(c_26343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25900,c_26339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.21/4.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.30/4.16  
% 10.30/4.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.30/4.16  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 10.30/4.16  
% 10.30/4.16  %Foreground sorts:
% 10.30/4.16  
% 10.30/4.16  
% 10.30/4.16  %Background operators:
% 10.30/4.16  
% 10.30/4.16  
% 10.30/4.16  %Foreground operators:
% 10.30/4.16  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.30/4.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.30/4.16  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.30/4.16  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.30/4.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.30/4.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.30/4.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.30/4.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.30/4.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.30/4.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.30/4.16  tff('#skF_2', type, '#skF_2': $i).
% 10.30/4.16  tff('#skF_3', type, '#skF_3': $i).
% 10.30/4.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.30/4.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.30/4.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.30/4.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.30/4.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.30/4.16  tff('#skF_4', type, '#skF_4': $i).
% 10.30/4.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.30/4.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.30/4.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.30/4.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.30/4.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.30/4.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.30/4.16  
% 10.30/4.19  tff(f_160, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 10.30/4.19  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.30/4.19  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.30/4.19  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 10.30/4.19  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.30/4.19  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 10.30/4.19  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.30/4.19  tff(f_124, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 10.30/4.19  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 10.30/4.19  tff(f_143, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 10.30/4.19  tff(f_32, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 10.30/4.19  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.30/4.19  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 10.30/4.19  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 10.30/4.19  tff(f_114, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 10.30/4.19  tff(f_97, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 10.30/4.19  tff(f_62, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 10.30/4.19  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.30/4.19  tff(c_15930, plain, (![C_753, A_754, B_755]: (v4_relat_1(C_753, A_754) | ~m1_subset_1(C_753, k1_zfmisc_1(k2_zfmisc_1(A_754, B_755))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.30/4.19  tff(c_15947, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_15930])).
% 10.30/4.19  tff(c_15804, plain, (![C_742, A_743, B_744]: (v1_relat_1(C_742) | ~m1_subset_1(C_742, k1_zfmisc_1(k2_zfmisc_1(A_743, B_744))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.30/4.19  tff(c_15821, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_15804])).
% 10.30/4.19  tff(c_18, plain, (![A_9]: (k1_relat_1(A_9)!=k1_xboole_0 | k1_xboole_0=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.30/4.19  tff(c_15830, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_15821, c_18])).
% 10.30/4.19  tff(c_15874, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_15830])).
% 10.30/4.19  tff(c_82, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.30/4.19  tff(c_24, plain, (![A_11]: (v1_funct_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.30/4.19  tff(c_72, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.30/4.19  tff(c_150, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_72])).
% 10.30/4.19  tff(c_153, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_150])).
% 10.30/4.19  tff(c_156, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_153])).
% 10.30/4.19  tff(c_194, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.30/4.19  tff(c_200, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_194])).
% 10.30/4.19  tff(c_210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_200])).
% 10.30/4.19  tff(c_212, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_72])).
% 10.30/4.19  tff(c_76, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.30/4.19  tff(c_28, plain, (![A_12]: (k2_relat_1(k2_funct_1(A_12))=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.30/4.19  tff(c_351, plain, (![C_79, A_80, B_81]: (v4_relat_1(C_79, A_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.30/4.19  tff(c_364, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_351])).
% 10.30/4.19  tff(c_251, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.30/4.19  tff(c_264, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_251])).
% 10.30/4.19  tff(c_280, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_264, c_18])).
% 10.30/4.19  tff(c_305, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_280])).
% 10.30/4.19  tff(c_26, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_70])).
% 10.30/4.19  tff(c_74, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.30/4.19  tff(c_1123, plain, (![A_148, B_149, C_150]: (k2_relset_1(A_148, B_149, C_150)=k2_relat_1(C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.30/4.19  tff(c_1132, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_1123])).
% 10.30/4.19  tff(c_1140, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1132])).
% 10.30/4.19  tff(c_711, plain, (![A_123]: (k1_relat_1(k2_funct_1(A_123))=k2_relat_1(A_123) | ~v2_funct_1(A_123) | ~v1_funct_1(A_123) | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.30/4.19  tff(c_56, plain, (![A_29]: (v1_funct_2(A_29, k1_relat_1(A_29), k2_relat_1(A_29)) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_124])).
% 10.30/4.19  tff(c_7147, plain, (![A_380]: (v1_funct_2(k2_funct_1(A_380), k2_relat_1(A_380), k2_relat_1(k2_funct_1(A_380))) | ~v1_funct_1(k2_funct_1(A_380)) | ~v1_relat_1(k2_funct_1(A_380)) | ~v2_funct_1(A_380) | ~v1_funct_1(A_380) | ~v1_relat_1(A_380))), inference(superposition, [status(thm), theory('equality')], [c_711, c_56])).
% 10.30/4.19  tff(c_7174, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1140, c_7147])).
% 10.30/4.19  tff(c_7206, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_82, c_76, c_212, c_7174])).
% 10.30/4.19  tff(c_7213, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_7206])).
% 10.30/4.19  tff(c_7216, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_7213])).
% 10.30/4.19  tff(c_7220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_264, c_82, c_7216])).
% 10.30/4.19  tff(c_7221, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4')))), inference(splitRight, [status(thm)], [c_7206])).
% 10.30/4.19  tff(c_7244, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28, c_7221])).
% 10.30/4.19  tff(c_7248, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_82, c_76, c_7244])).
% 10.30/4.19  tff(c_7222, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_7206])).
% 10.30/4.19  tff(c_30, plain, (![A_12]: (k1_relat_1(k2_funct_1(A_12))=k2_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.30/4.19  tff(c_1009, plain, (![A_143]: (m1_subset_1(A_143, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_143), k2_relat_1(A_143)))) | ~v1_funct_1(A_143) | ~v1_relat_1(A_143))), inference(cnfTransformation, [status(thm)], [f_124])).
% 10.30/4.19  tff(c_7266, plain, (![A_381]: (m1_subset_1(k2_funct_1(A_381), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_381), k2_relat_1(k2_funct_1(A_381))))) | ~v1_funct_1(k2_funct_1(A_381)) | ~v1_relat_1(k2_funct_1(A_381)) | ~v2_funct_1(A_381) | ~v1_funct_1(A_381) | ~v1_relat_1(A_381))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1009])).
% 10.30/4.19  tff(c_7310, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1140, c_7266])).
% 10.30/4.19  tff(c_7348, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_82, c_76, c_7222, c_212, c_7310])).
% 10.30/4.19  tff(c_7379, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4')))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28, c_7348])).
% 10.30/4.19  tff(c_7390, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_82, c_76, c_7379])).
% 10.30/4.19  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.30/4.19  tff(c_1837, plain, (![B_190, D_191, A_192, C_193]: (k1_xboole_0=B_190 | m1_subset_1(D_191, k1_zfmisc_1(k2_zfmisc_1(A_192, C_193))) | ~r1_tarski(B_190, C_193) | ~m1_subset_1(D_191, k1_zfmisc_1(k2_zfmisc_1(A_192, B_190))) | ~v1_funct_2(D_191, A_192, B_190) | ~v1_funct_1(D_191))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.30/4.19  tff(c_10043, plain, (![B_459, D_460, A_461, A_462]: (k1_relat_1(B_459)=k1_xboole_0 | m1_subset_1(D_460, k1_zfmisc_1(k2_zfmisc_1(A_461, A_462))) | ~m1_subset_1(D_460, k1_zfmisc_1(k2_zfmisc_1(A_461, k1_relat_1(B_459)))) | ~v1_funct_2(D_460, A_461, k1_relat_1(B_459)) | ~v1_funct_1(D_460) | ~v4_relat_1(B_459, A_462) | ~v1_relat_1(B_459))), inference(resolution, [status(thm)], [c_12, c_1837])).
% 10.30/4.19  tff(c_10047, plain, (![A_462]: (k1_relat_1('#skF_4')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_462))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v4_relat_1('#skF_4', A_462) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_7390, c_10043])).
% 10.30/4.19  tff(c_10078, plain, (![A_462]: (k1_relat_1('#skF_4')=k1_xboole_0 | m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_462))) | ~v4_relat_1('#skF_4', A_462))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_212, c_7248, c_10047])).
% 10.30/4.19  tff(c_10103, plain, (![A_463]: (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_463))) | ~v4_relat_1('#skF_4', A_463))), inference(negUnitSimplification, [status(thm)], [c_305, c_10078])).
% 10.30/4.19  tff(c_211, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_72])).
% 10.30/4.19  tff(c_213, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_211])).
% 10.30/4.19  tff(c_10129, plain, (~v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_10103, c_213])).
% 10.30/4.19  tff(c_10147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_364, c_10129])).
% 10.30/4.19  tff(c_10148, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_280])).
% 10.30/4.19  tff(c_6, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.30/4.19  tff(c_10158, plain, (![A_2]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_10148, c_6])).
% 10.30/4.19  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 10.30/4.19  tff(c_92, plain, (![A_40]: (v1_xboole_0(k2_relat_1(A_40)) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.30/4.19  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 10.30/4.19  tff(c_103, plain, (![A_45]: (k2_relat_1(A_45)=k1_xboole_0 | ~v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_92, c_4])).
% 10.30/4.19  tff(c_111, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_103])).
% 10.30/4.19  tff(c_10156, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10148, c_10148, c_111])).
% 10.30/4.19  tff(c_10558, plain, (![A_509]: (k1_relat_1(k2_funct_1(A_509))=k2_relat_1(A_509) | ~v2_funct_1(A_509) | ~v1_funct_1(A_509) | ~v1_relat_1(A_509))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.30/4.19  tff(c_15621, plain, (![A_735]: (v1_funct_2(k2_funct_1(A_735), k2_relat_1(A_735), k2_relat_1(k2_funct_1(A_735))) | ~v1_funct_1(k2_funct_1(A_735)) | ~v1_relat_1(k2_funct_1(A_735)) | ~v2_funct_1(A_735) | ~v1_funct_1(A_735) | ~v1_relat_1(A_735))), inference(superposition, [status(thm), theory('equality')], [c_10558, c_56])).
% 10.30/4.19  tff(c_15660, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10156, c_15621])).
% 10.30/4.19  tff(c_15676, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_264, c_82, c_76, c_212, c_15660])).
% 10.30/4.19  tff(c_15677, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_15676])).
% 10.30/4.19  tff(c_15680, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_15677])).
% 10.30/4.19  tff(c_15684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_264, c_82, c_15680])).
% 10.30/4.19  tff(c_15686, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_15676])).
% 10.30/4.19  tff(c_10153, plain, (![A_9]: (k1_relat_1(A_9)!='#skF_4' | A_9='#skF_4' | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_10148, c_10148, c_18])).
% 10.30/4.19  tff(c_15701, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_15686, c_10153])).
% 10.30/4.19  tff(c_15763, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_15701])).
% 10.30/4.19  tff(c_15766, plain, (k2_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_30, c_15763])).
% 10.30/4.19  tff(c_15769, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_264, c_82, c_76, c_10156, c_15766])).
% 10.30/4.19  tff(c_15770, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_15701])).
% 10.30/4.19  tff(c_10832, plain, (![A_528, B_529, C_530]: (k2_relset_1(A_528, B_529, C_530)=k2_relat_1(C_530) | ~m1_subset_1(C_530, k1_zfmisc_1(k2_zfmisc_1(A_528, B_529))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.30/4.19  tff(c_10839, plain, (![A_528, B_529]: (k2_relset_1(A_528, B_529, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_10158, c_10832])).
% 10.30/4.19  tff(c_10845, plain, (![A_528, B_529]: (k2_relset_1(A_528, B_529, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10156, c_10839])).
% 10.30/4.19  tff(c_10847, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10845, c_74])).
% 10.30/4.19  tff(c_10855, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_10847, c_213])).
% 10.30/4.19  tff(c_15775, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_15770, c_10855])).
% 10.30/4.19  tff(c_15782, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10158, c_15775])).
% 10.30/4.19  tff(c_15784, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_211])).
% 10.30/4.19  tff(c_15820, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_15784, c_15804])).
% 10.30/4.19  tff(c_16422, plain, (![A_803, B_804, C_805]: (k2_relset_1(A_803, B_804, C_805)=k2_relat_1(C_805) | ~m1_subset_1(C_805, k1_zfmisc_1(k2_zfmisc_1(A_803, B_804))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.30/4.19  tff(c_16434, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_16422])).
% 10.30/4.19  tff(c_16443, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_16434])).
% 10.30/4.19  tff(c_16162, plain, (![A_788]: (k1_relat_1(k2_funct_1(A_788))=k2_relat_1(A_788) | ~v2_funct_1(A_788) | ~v1_funct_1(A_788) | ~v1_relat_1(A_788))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.30/4.19  tff(c_21415, plain, (![A_1021]: (v1_funct_2(k2_funct_1(A_1021), k2_relat_1(A_1021), k2_relat_1(k2_funct_1(A_1021))) | ~v1_funct_1(k2_funct_1(A_1021)) | ~v1_relat_1(k2_funct_1(A_1021)) | ~v2_funct_1(A_1021) | ~v1_funct_1(A_1021) | ~v1_relat_1(A_1021))), inference(superposition, [status(thm), theory('equality')], [c_16162, c_56])).
% 10.30/4.19  tff(c_21442, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_16443, c_21415])).
% 10.30/4.19  tff(c_21471, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_15821, c_82, c_76, c_15820, c_212, c_21442])).
% 10.30/4.19  tff(c_21481, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28, c_21471])).
% 10.30/4.19  tff(c_21485, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_15821, c_82, c_76, c_21481])).
% 10.30/4.19  tff(c_16280, plain, (![A_797]: (m1_subset_1(A_797, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_797), k2_relat_1(A_797)))) | ~v1_funct_1(A_797) | ~v1_relat_1(A_797))), inference(cnfTransformation, [status(thm)], [f_124])).
% 10.30/4.19  tff(c_21801, plain, (![A_1032]: (m1_subset_1(k2_funct_1(A_1032), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_1032), k2_relat_1(k2_funct_1(A_1032))))) | ~v1_funct_1(k2_funct_1(A_1032)) | ~v1_relat_1(k2_funct_1(A_1032)) | ~v2_funct_1(A_1032) | ~v1_funct_1(A_1032) | ~v1_relat_1(A_1032))), inference(superposition, [status(thm), theory('equality')], [c_30, c_16280])).
% 10.30/4.19  tff(c_21845, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_16443, c_21801])).
% 10.30/4.19  tff(c_21880, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_15821, c_82, c_76, c_15820, c_212, c_21845])).
% 10.30/4.19  tff(c_21907, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4')))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28, c_21880])).
% 10.30/4.19  tff(c_21919, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_15821, c_82, c_76, c_21907])).
% 10.30/4.19  tff(c_16539, plain, (![B_813, D_814, A_815, C_816]: (k1_xboole_0=B_813 | v1_funct_2(D_814, A_815, C_816) | ~r1_tarski(B_813, C_816) | ~m1_subset_1(D_814, k1_zfmisc_1(k2_zfmisc_1(A_815, B_813))) | ~v1_funct_2(D_814, A_815, B_813) | ~v1_funct_1(D_814))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.30/4.19  tff(c_25358, plain, (![B_1120, D_1121, A_1122, A_1123]: (k1_relat_1(B_1120)=k1_xboole_0 | v1_funct_2(D_1121, A_1122, A_1123) | ~m1_subset_1(D_1121, k1_zfmisc_1(k2_zfmisc_1(A_1122, k1_relat_1(B_1120)))) | ~v1_funct_2(D_1121, A_1122, k1_relat_1(B_1120)) | ~v1_funct_1(D_1121) | ~v4_relat_1(B_1120, A_1123) | ~v1_relat_1(B_1120))), inference(resolution, [status(thm)], [c_12, c_16539])).
% 10.30/4.19  tff(c_25366, plain, (![A_1123]: (k1_relat_1('#skF_4')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_1123) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v4_relat_1('#skF_4', A_1123) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_21919, c_25358])).
% 10.30/4.19  tff(c_25396, plain, (![A_1123]: (k1_relat_1('#skF_4')=k1_xboole_0 | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_1123) | ~v4_relat_1('#skF_4', A_1123))), inference(demodulation, [status(thm), theory('equality')], [c_15821, c_212, c_21485, c_25366])).
% 10.30/4.19  tff(c_25418, plain, (![A_1124]: (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', A_1124) | ~v4_relat_1('#skF_4', A_1124))), inference(negUnitSimplification, [status(thm)], [c_15874, c_25396])).
% 10.30/4.19  tff(c_15783, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_211])).
% 10.30/4.19  tff(c_25421, plain, (~v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_25418, c_15783])).
% 10.30/4.19  tff(c_25425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15947, c_25421])).
% 10.30/4.19  tff(c_25426, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_15830])).
% 10.30/4.19  tff(c_25434, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_25426, c_25426, c_111])).
% 10.30/4.19  tff(c_16, plain, (![A_9]: (k2_relat_1(A_9)!=k1_xboole_0 | k1_xboole_0=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 10.30/4.19  tff(c_15829, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_15821, c_16])).
% 10.30/4.19  tff(c_15851, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_15829])).
% 10.30/4.19  tff(c_25428, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_25426, c_15851])).
% 10.30/4.19  tff(c_25461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25434, c_25428])).
% 10.30/4.19  tff(c_25462, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_15829])).
% 10.30/4.19  tff(c_25472, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25462, c_2])).
% 10.30/4.19  tff(c_52, plain, (![A_26, B_27]: (m1_subset_1('#skF_1'(A_26, B_27), k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 10.30/4.19  tff(c_25853, plain, (![C_1184, A_1185, B_1186]: (v1_xboole_0(C_1184) | ~m1_subset_1(C_1184, k1_zfmisc_1(k2_zfmisc_1(A_1185, B_1186))) | ~v1_xboole_0(A_1185))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.30/4.19  tff(c_25864, plain, (![A_1187, B_1188]: (v1_xboole_0('#skF_1'(A_1187, B_1188)) | ~v1_xboole_0(A_1187))), inference(resolution, [status(thm)], [c_52, c_25853])).
% 10.30/4.19  tff(c_25471, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_25462, c_4])).
% 10.30/4.19  tff(c_25873, plain, (![A_1189, B_1190]: ('#skF_1'(A_1189, B_1190)='#skF_4' | ~v1_xboole_0(A_1189))), inference(resolution, [status(thm)], [c_25864, c_25471])).
% 10.30/4.19  tff(c_25883, plain, (![B_1191]: ('#skF_1'('#skF_4', B_1191)='#skF_4')), inference(resolution, [status(thm)], [c_25472, c_25873])).
% 10.30/4.19  tff(c_42, plain, (![A_26, B_27]: (v1_funct_2('#skF_1'(A_26, B_27), A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_114])).
% 10.30/4.19  tff(c_25900, plain, (![B_1191]: (v1_funct_2('#skF_4', '#skF_4', B_1191))), inference(superposition, [status(thm), theory('equality')], [c_25883, c_42])).
% 10.30/4.19  tff(c_25463, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_15829])).
% 10.30/4.19  tff(c_25496, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_25462, c_25463])).
% 10.30/4.19  tff(c_25470, plain, (![A_2]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_25462, c_6])).
% 10.30/4.19  tff(c_26320, plain, (![A_1220, B_1221, C_1222]: (k2_relset_1(A_1220, B_1221, C_1222)=k2_relat_1(C_1222) | ~m1_subset_1(C_1222, k1_zfmisc_1(k2_zfmisc_1(A_1220, B_1221))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 10.30/4.19  tff(c_26324, plain, (![A_1220, B_1221]: (k2_relset_1(A_1220, B_1221, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_25470, c_26320])).
% 10.30/4.19  tff(c_26329, plain, (![A_1220, B_1221]: (k2_relset_1(A_1220, B_1221, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25496, c_26324])).
% 10.30/4.19  tff(c_26331, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26329, c_74])).
% 10.30/4.19  tff(c_20, plain, (![A_10]: (k1_relat_1(A_10)=k1_xboole_0 | k2_relat_1(A_10)!=k1_xboole_0 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.30/4.19  tff(c_25564, plain, (![A_1130]: (k1_relat_1(A_1130)='#skF_4' | k2_relat_1(A_1130)!='#skF_4' | ~v1_relat_1(A_1130))), inference(demodulation, [status(thm), theory('equality')], [c_25462, c_25462, c_20])).
% 10.30/4.19  tff(c_25570, plain, (k1_relat_1('#skF_4')='#skF_4' | k2_relat_1('#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_15821, c_25564])).
% 10.30/4.19  tff(c_25580, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_25496, c_25570])).
% 10.30/4.19  tff(c_25729, plain, (![A_1160]: (k2_relat_1(k2_funct_1(A_1160))=k1_relat_1(A_1160) | ~v2_funct_1(A_1160) | ~v1_funct_1(A_1160) | ~v1_relat_1(A_1160))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.30/4.19  tff(c_15849, plain, (k2_relat_1(k2_funct_1('#skF_4'))!=k1_xboole_0 | k2_funct_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_15820, c_16])).
% 10.30/4.19  tff(c_25607, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4' | k2_funct_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_25462, c_25462, c_15849])).
% 10.30/4.19  tff(c_25608, plain, (k2_relat_1(k2_funct_1('#skF_4'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_25607])).
% 10.30/4.19  tff(c_25738, plain, (k1_relat_1('#skF_4')!='#skF_4' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_25729, c_25608])).
% 10.30/4.19  tff(c_25751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15821, c_82, c_76, c_25580, c_25738])).
% 10.30/4.19  tff(c_25752, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_25607])).
% 10.30/4.19  tff(c_25756, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_25752, c_15783])).
% 10.30/4.19  tff(c_26339, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26331, c_25756])).
% 10.30/4.19  tff(c_26343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25900, c_26339])).
% 10.30/4.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.30/4.19  
% 10.30/4.19  Inference rules
% 10.30/4.19  ----------------------
% 10.30/4.19  #Ref     : 0
% 10.30/4.19  #Sup     : 6256
% 10.30/4.19  #Fact    : 0
% 10.30/4.19  #Define  : 0
% 10.30/4.19  #Split   : 27
% 10.30/4.19  #Chain   : 0
% 10.30/4.19  #Close   : 0
% 10.30/4.19  
% 10.30/4.19  Ordering : KBO
% 10.30/4.19  
% 10.30/4.19  Simplification rules
% 10.30/4.19  ----------------------
% 10.30/4.19  #Subsume      : 666
% 10.30/4.19  #Demod        : 9920
% 10.30/4.19  #Tautology    : 4207
% 10.30/4.19  #SimpNegUnit  : 23
% 10.30/4.19  #BackRed      : 50
% 10.30/4.19  
% 10.30/4.19  #Partial instantiations: 0
% 10.30/4.19  #Strategies tried      : 1
% 10.30/4.19  
% 10.30/4.19  Timing (in seconds)
% 10.30/4.19  ----------------------
% 10.30/4.19  Preprocessing        : 0.35
% 10.30/4.19  Parsing              : 0.18
% 10.30/4.19  CNF conversion       : 0.02
% 10.30/4.19  Main loop            : 3.01
% 10.30/4.19  Inferencing          : 0.90
% 10.30/4.19  Reduction            : 1.15
% 10.30/4.19  Demodulation         : 0.88
% 10.30/4.19  BG Simplification    : 0.09
% 10.30/4.19  Subsumption          : 0.70
% 10.30/4.19  Abstraction          : 0.12
% 10.30/4.19  MUC search           : 0.00
% 10.30/4.19  Cooper               : 0.00
% 10.30/4.19  Total                : 3.43
% 10.30/4.19  Index Insertion      : 0.00
% 10.30/4.19  Index Deletion       : 0.00
% 10.30/4.19  Index Matching       : 0.00
% 10.30/4.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
