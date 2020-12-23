%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:42 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 329 expanded)
%              Number of leaves         :   26 ( 120 expanded)
%              Depth                    :   13
%              Number of atoms          :  161 ( 828 expanded)
%              Number of equality atoms :   46 ( 189 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_79,axiom,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_14,plain,(
    ! [A_5] :
      ( r1_tarski(A_5,k2_zfmisc_1(k1_relat_1(A_5),k2_relat_1(A_5)))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_38,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_107,plain,(
    ! [A_31,B_32,C_33] :
      ( k1_relset_1(A_31,B_32,C_33) = k1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_171,plain,(
    ! [A_57,B_58,A_59] :
      ( k1_relset_1(A_57,B_58,A_59) = k1_relat_1(A_59)
      | ~ r1_tarski(A_59,k2_zfmisc_1(A_57,B_58)) ) ),
    inference(resolution,[status(thm)],[c_12,c_107])).

tff(c_181,plain,(
    ! [A_5] :
      ( k1_relset_1(k1_relat_1(A_5),k2_relat_1(A_5),A_5) = k1_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_14,c_171])).

tff(c_182,plain,(
    ! [B_60,C_61,A_62] :
      ( k1_xboole_0 = B_60
      | v1_funct_2(C_61,A_62,B_60)
      | k1_relset_1(A_62,B_60,C_61) != A_62
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_287,plain,(
    ! [B_85,A_86,A_87] :
      ( k1_xboole_0 = B_85
      | v1_funct_2(A_86,A_87,B_85)
      | k1_relset_1(A_87,B_85,A_86) != A_87
      | ~ r1_tarski(A_86,k2_zfmisc_1(A_87,B_85)) ) ),
    inference(resolution,[status(thm)],[c_12,c_182])).

tff(c_336,plain,(
    ! [A_95] :
      ( k2_relat_1(A_95) = k1_xboole_0
      | v1_funct_2(A_95,k1_relat_1(A_95),k2_relat_1(A_95))
      | k1_relset_1(k1_relat_1(A_95),k2_relat_1(A_95),A_95) != k1_relat_1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(resolution,[status(thm)],[c_14,c_287])).

tff(c_36,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36])).

tff(c_87,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_339,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_336,c_87])).

tff(c_342,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_339])).

tff(c_343,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_342])).

tff(c_346,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_343])).

tff(c_350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_346])).

tff(c_351,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_342])).

tff(c_366,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_14])).

tff(c_376,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_6,c_366])).

tff(c_8,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_144,plain,(
    ! [B_43,C_44] :
      ( k1_relset_1(k1_xboole_0,B_43,C_44) = k1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_107])).

tff(c_148,plain,(
    ! [B_43,A_3] :
      ( k1_relset_1(k1_xboole_0,B_43,A_3) = k1_relat_1(A_3)
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_144])).

tff(c_383,plain,(
    ! [B_43] : k1_relset_1(k1_xboole_0,B_43,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_376,c_148])).

tff(c_93,plain,(
    ! [C_28,A_29,B_30] :
      ( v1_partfun1(C_28,A_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_103,plain,(
    ! [C_28] :
      ( v1_partfun1(C_28,k1_xboole_0)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_93])).

tff(c_119,plain,(
    ! [C_34] :
      ( v1_partfun1(C_34,k1_xboole_0)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_103])).

tff(c_124,plain,(
    ! [A_3] :
      ( v1_partfun1(A_3,k1_xboole_0)
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_119])).

tff(c_131,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_funct_2(C_38,A_39,B_40)
      | ~ v1_partfun1(C_38,A_39)
      | ~ v1_funct_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_219,plain,(
    ! [C_70,B_71] :
      ( v1_funct_2(C_70,k1_xboole_0,B_71)
      | ~ v1_partfun1(C_70,k1_xboole_0)
      | ~ v1_funct_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_131])).

tff(c_223,plain,(
    ! [A_3,B_71] :
      ( v1_funct_2(A_3,k1_xboole_0,B_71)
      | ~ v1_partfun1(A_3,k1_xboole_0)
      | ~ v1_funct_1(A_3)
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_219])).

tff(c_224,plain,(
    ! [B_72,A_73,C_74] :
      ( k1_xboole_0 = B_72
      | k1_relset_1(A_73,B_72,C_74) = A_73
      | ~ v1_funct_2(C_74,A_73,B_72)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_299,plain,(
    ! [B_88,A_89,A_90] :
      ( k1_xboole_0 = B_88
      | k1_relset_1(A_89,B_88,A_90) = A_89
      | ~ v1_funct_2(A_90,A_89,B_88)
      | ~ r1_tarski(A_90,k2_zfmisc_1(A_89,B_88)) ) ),
    inference(resolution,[status(thm)],[c_12,c_224])).

tff(c_311,plain,(
    ! [B_91,A_92] :
      ( k1_xboole_0 = B_91
      | k1_relset_1(k1_xboole_0,B_91,A_92) = k1_xboole_0
      | ~ v1_funct_2(A_92,k1_xboole_0,B_91)
      | ~ r1_tarski(A_92,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_299])).

tff(c_326,plain,(
    ! [B_93,A_94] :
      ( k1_xboole_0 = B_93
      | k1_relset_1(k1_xboole_0,B_93,A_94) = k1_xboole_0
      | ~ v1_partfun1(A_94,k1_xboole_0)
      | ~ v1_funct_1(A_94)
      | ~ r1_tarski(A_94,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_223,c_311])).

tff(c_419,plain,(
    ! [B_98,A_99] :
      ( k1_xboole_0 = B_98
      | k1_relset_1(k1_xboole_0,B_98,A_99) = k1_xboole_0
      | ~ v1_funct_1(A_99)
      | ~ r1_tarski(A_99,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_124,c_326])).

tff(c_421,plain,(
    ! [B_98] :
      ( k1_xboole_0 = B_98
      | k1_relset_1(k1_xboole_0,B_98,'#skF_1') = k1_xboole_0
      | ~ v1_funct_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_376,c_419])).

tff(c_424,plain,(
    ! [B_98] :
      ( k1_xboole_0 = B_98
      | k1_relat_1('#skF_1') = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_383,c_421])).

tff(c_425,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_424])).

tff(c_150,plain,(
    ! [A_47,A_48,B_49] :
      ( v1_partfun1(A_47,A_48)
      | ~ v1_xboole_0(A_48)
      | ~ r1_tarski(A_47,k2_zfmisc_1(A_48,B_49)) ) ),
    inference(resolution,[status(thm)],[c_12,c_93])).

tff(c_160,plain,(
    ! [A_5] :
      ( v1_partfun1(A_5,k1_relat_1(A_5))
      | ~ v1_xboole_0(k1_relat_1(A_5))
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_14,c_150])).

tff(c_259,plain,(
    ! [A_81,A_82,B_83] :
      ( v1_funct_2(A_81,A_82,B_83)
      | ~ v1_partfun1(A_81,A_82)
      | ~ v1_funct_1(A_81)
      | ~ r1_tarski(A_81,k2_zfmisc_1(A_82,B_83)) ) ),
    inference(resolution,[status(thm)],[c_12,c_131])).

tff(c_270,plain,(
    ! [A_84] :
      ( v1_funct_2(A_84,k1_relat_1(A_84),k2_relat_1(A_84))
      | ~ v1_partfun1(A_84,k1_relat_1(A_84))
      | ~ v1_funct_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(resolution,[status(thm)],[c_14,c_259])).

tff(c_273,plain,
    ( ~ v1_partfun1('#skF_1',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_270,c_87])).

tff(c_276,plain,(
    ~ v1_partfun1('#skF_1',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_273])).

tff(c_279,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_160,c_276])).

tff(c_285,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_279])).

tff(c_429,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_285])).

tff(c_433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_429])).

tff(c_436,plain,(
    ! [B_100] : k1_xboole_0 = B_100 ),
    inference(splitRight,[status(thm)],[c_424])).

tff(c_457,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_285])).

tff(c_557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_457])).

tff(c_558,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_563,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_12,c_558])).

tff(c_571,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_563])).

tff(c_575,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_571])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.38  
% 2.62/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.38  %$ v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.62/1.38  
% 2.62/1.38  %Foreground sorts:
% 2.62/1.38  
% 2.62/1.38  
% 2.62/1.38  %Background operators:
% 2.62/1.38  
% 2.62/1.38  
% 2.62/1.38  %Foreground operators:
% 2.62/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.62/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.62/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.62/1.38  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.62/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.62/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.62/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.38  
% 2.91/1.40  tff(f_90, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 2.91/1.40  tff(f_40, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 2.91/1.40  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.91/1.40  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.91/1.40  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.91/1.40  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.91/1.40  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.91/1.40  tff(f_61, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 2.91/1.40  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 2.91/1.40  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.91/1.40  tff(c_14, plain, (![A_5]: (r1_tarski(A_5, k2_zfmisc_1(k1_relat_1(A_5), k2_relat_1(A_5))) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.91/1.40  tff(c_12, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.91/1.40  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.91/1.40  tff(c_38, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.91/1.40  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.91/1.40  tff(c_107, plain, (![A_31, B_32, C_33]: (k1_relset_1(A_31, B_32, C_33)=k1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.91/1.40  tff(c_171, plain, (![A_57, B_58, A_59]: (k1_relset_1(A_57, B_58, A_59)=k1_relat_1(A_59) | ~r1_tarski(A_59, k2_zfmisc_1(A_57, B_58)))), inference(resolution, [status(thm)], [c_12, c_107])).
% 2.91/1.40  tff(c_181, plain, (![A_5]: (k1_relset_1(k1_relat_1(A_5), k2_relat_1(A_5), A_5)=k1_relat_1(A_5) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_14, c_171])).
% 2.91/1.40  tff(c_182, plain, (![B_60, C_61, A_62]: (k1_xboole_0=B_60 | v1_funct_2(C_61, A_62, B_60) | k1_relset_1(A_62, B_60, C_61)!=A_62 | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_60))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.91/1.40  tff(c_287, plain, (![B_85, A_86, A_87]: (k1_xboole_0=B_85 | v1_funct_2(A_86, A_87, B_85) | k1_relset_1(A_87, B_85, A_86)!=A_87 | ~r1_tarski(A_86, k2_zfmisc_1(A_87, B_85)))), inference(resolution, [status(thm)], [c_12, c_182])).
% 2.91/1.40  tff(c_336, plain, (![A_95]: (k2_relat_1(A_95)=k1_xboole_0 | v1_funct_2(A_95, k1_relat_1(A_95), k2_relat_1(A_95)) | k1_relset_1(k1_relat_1(A_95), k2_relat_1(A_95), A_95)!=k1_relat_1(A_95) | ~v1_relat_1(A_95))), inference(resolution, [status(thm)], [c_14, c_287])).
% 2.91/1.40  tff(c_36, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.91/1.40  tff(c_42, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36])).
% 2.91/1.40  tff(c_87, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_42])).
% 2.91/1.40  tff(c_339, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_336, c_87])).
% 2.91/1.40  tff(c_342, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_339])).
% 2.91/1.40  tff(c_343, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_342])).
% 2.91/1.40  tff(c_346, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_181, c_343])).
% 2.91/1.40  tff(c_350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_346])).
% 2.91/1.40  tff(c_351, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_342])).
% 2.91/1.40  tff(c_366, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_351, c_14])).
% 2.91/1.40  tff(c_376, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_6, c_366])).
% 2.91/1.40  tff(c_8, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.91/1.40  tff(c_144, plain, (![B_43, C_44]: (k1_relset_1(k1_xboole_0, B_43, C_44)=k1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_107])).
% 2.91/1.40  tff(c_148, plain, (![B_43, A_3]: (k1_relset_1(k1_xboole_0, B_43, A_3)=k1_relat_1(A_3) | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_144])).
% 2.91/1.40  tff(c_383, plain, (![B_43]: (k1_relset_1(k1_xboole_0, B_43, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_376, c_148])).
% 2.91/1.40  tff(c_93, plain, (![C_28, A_29, B_30]: (v1_partfun1(C_28, A_29) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.91/1.40  tff(c_103, plain, (![C_28]: (v1_partfun1(C_28, k1_xboole_0) | ~m1_subset_1(C_28, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_93])).
% 2.91/1.40  tff(c_119, plain, (![C_34]: (v1_partfun1(C_34, k1_xboole_0) | ~m1_subset_1(C_34, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_103])).
% 2.91/1.40  tff(c_124, plain, (![A_3]: (v1_partfun1(A_3, k1_xboole_0) | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_119])).
% 2.91/1.40  tff(c_131, plain, (![C_38, A_39, B_40]: (v1_funct_2(C_38, A_39, B_40) | ~v1_partfun1(C_38, A_39) | ~v1_funct_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.91/1.40  tff(c_219, plain, (![C_70, B_71]: (v1_funct_2(C_70, k1_xboole_0, B_71) | ~v1_partfun1(C_70, k1_xboole_0) | ~v1_funct_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_131])).
% 2.91/1.40  tff(c_223, plain, (![A_3, B_71]: (v1_funct_2(A_3, k1_xboole_0, B_71) | ~v1_partfun1(A_3, k1_xboole_0) | ~v1_funct_1(A_3) | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_219])).
% 2.91/1.40  tff(c_224, plain, (![B_72, A_73, C_74]: (k1_xboole_0=B_72 | k1_relset_1(A_73, B_72, C_74)=A_73 | ~v1_funct_2(C_74, A_73, B_72) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.91/1.40  tff(c_299, plain, (![B_88, A_89, A_90]: (k1_xboole_0=B_88 | k1_relset_1(A_89, B_88, A_90)=A_89 | ~v1_funct_2(A_90, A_89, B_88) | ~r1_tarski(A_90, k2_zfmisc_1(A_89, B_88)))), inference(resolution, [status(thm)], [c_12, c_224])).
% 2.91/1.40  tff(c_311, plain, (![B_91, A_92]: (k1_xboole_0=B_91 | k1_relset_1(k1_xboole_0, B_91, A_92)=k1_xboole_0 | ~v1_funct_2(A_92, k1_xboole_0, B_91) | ~r1_tarski(A_92, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_299])).
% 2.91/1.40  tff(c_326, plain, (![B_93, A_94]: (k1_xboole_0=B_93 | k1_relset_1(k1_xboole_0, B_93, A_94)=k1_xboole_0 | ~v1_partfun1(A_94, k1_xboole_0) | ~v1_funct_1(A_94) | ~r1_tarski(A_94, k1_xboole_0))), inference(resolution, [status(thm)], [c_223, c_311])).
% 2.91/1.40  tff(c_419, plain, (![B_98, A_99]: (k1_xboole_0=B_98 | k1_relset_1(k1_xboole_0, B_98, A_99)=k1_xboole_0 | ~v1_funct_1(A_99) | ~r1_tarski(A_99, k1_xboole_0))), inference(resolution, [status(thm)], [c_124, c_326])).
% 2.91/1.40  tff(c_421, plain, (![B_98]: (k1_xboole_0=B_98 | k1_relset_1(k1_xboole_0, B_98, '#skF_1')=k1_xboole_0 | ~v1_funct_1('#skF_1'))), inference(resolution, [status(thm)], [c_376, c_419])).
% 2.91/1.40  tff(c_424, plain, (![B_98]: (k1_xboole_0=B_98 | k1_relat_1('#skF_1')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_383, c_421])).
% 2.91/1.40  tff(c_425, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_424])).
% 2.91/1.40  tff(c_150, plain, (![A_47, A_48, B_49]: (v1_partfun1(A_47, A_48) | ~v1_xboole_0(A_48) | ~r1_tarski(A_47, k2_zfmisc_1(A_48, B_49)))), inference(resolution, [status(thm)], [c_12, c_93])).
% 2.91/1.40  tff(c_160, plain, (![A_5]: (v1_partfun1(A_5, k1_relat_1(A_5)) | ~v1_xboole_0(k1_relat_1(A_5)) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_14, c_150])).
% 2.91/1.40  tff(c_259, plain, (![A_81, A_82, B_83]: (v1_funct_2(A_81, A_82, B_83) | ~v1_partfun1(A_81, A_82) | ~v1_funct_1(A_81) | ~r1_tarski(A_81, k2_zfmisc_1(A_82, B_83)))), inference(resolution, [status(thm)], [c_12, c_131])).
% 2.91/1.40  tff(c_270, plain, (![A_84]: (v1_funct_2(A_84, k1_relat_1(A_84), k2_relat_1(A_84)) | ~v1_partfun1(A_84, k1_relat_1(A_84)) | ~v1_funct_1(A_84) | ~v1_relat_1(A_84))), inference(resolution, [status(thm)], [c_14, c_259])).
% 2.91/1.40  tff(c_273, plain, (~v1_partfun1('#skF_1', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_270, c_87])).
% 2.91/1.40  tff(c_276, plain, (~v1_partfun1('#skF_1', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_273])).
% 2.91/1.40  tff(c_279, plain, (~v1_xboole_0(k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_160, c_276])).
% 2.91/1.40  tff(c_285, plain, (~v1_xboole_0(k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_279])).
% 2.91/1.40  tff(c_429, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_425, c_285])).
% 2.91/1.40  tff(c_433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_429])).
% 2.91/1.40  tff(c_436, plain, (![B_100]: (k1_xboole_0=B_100)), inference(splitRight, [status(thm)], [c_424])).
% 2.91/1.40  tff(c_457, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_436, c_285])).
% 2.91/1.40  tff(c_557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_457])).
% 2.91/1.40  tff(c_558, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_42])).
% 2.91/1.40  tff(c_563, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_558])).
% 2.91/1.40  tff(c_571, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_14, c_563])).
% 2.91/1.40  tff(c_575, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_571])).
% 2.91/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.91/1.40  
% 2.91/1.40  Inference rules
% 2.91/1.40  ----------------------
% 2.91/1.40  #Ref     : 0
% 2.91/1.40  #Sup     : 143
% 2.91/1.40  #Fact    : 0
% 2.91/1.40  #Define  : 0
% 2.91/1.40  #Split   : 5
% 2.91/1.40  #Chain   : 0
% 2.91/1.40  #Close   : 0
% 2.91/1.40  
% 2.91/1.40  Ordering : KBO
% 2.91/1.40  
% 2.91/1.40  Simplification rules
% 2.91/1.40  ----------------------
% 2.91/1.40  #Subsume      : 29
% 2.91/1.40  #Demod        : 37
% 2.91/1.40  #Tautology    : 34
% 2.91/1.40  #SimpNegUnit  : 0
% 2.91/1.40  #BackRed      : 6
% 2.91/1.40  
% 2.91/1.40  #Partial instantiations: 39
% 2.91/1.40  #Strategies tried      : 1
% 2.91/1.40  
% 2.91/1.40  Timing (in seconds)
% 2.91/1.40  ----------------------
% 2.91/1.41  Preprocessing        : 0.32
% 2.91/1.41  Parsing              : 0.17
% 2.91/1.41  CNF conversion       : 0.02
% 2.91/1.41  Main loop            : 0.32
% 2.91/1.41  Inferencing          : 0.14
% 2.91/1.41  Reduction            : 0.08
% 2.91/1.41  Demodulation         : 0.06
% 2.91/1.41  BG Simplification    : 0.02
% 2.91/1.41  Subsumption          : 0.06
% 2.91/1.41  Abstraction          : 0.02
% 2.91/1.41  MUC search           : 0.00
% 2.91/1.41  Cooper               : 0.00
% 2.91/1.41  Total                : 0.68
% 2.91/1.41  Index Insertion      : 0.00
% 2.91/1.41  Index Deletion       : 0.00
% 2.91/1.41  Index Matching       : 0.00
% 2.91/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
