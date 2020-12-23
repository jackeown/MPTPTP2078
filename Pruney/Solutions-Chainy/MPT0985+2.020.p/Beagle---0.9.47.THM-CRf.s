%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:28 EST 2020

% Result     : Theorem 11.38s
% Output     : CNFRefutation 11.65s
% Verified   : 
% Statistics : Number of formulae       :  259 (1861 expanded)
%              Number of leaves         :   51 ( 628 expanded)
%              Depth                    :   15
%              Number of atoms          :  435 (4734 expanded)
%              Number of equality atoms :  133 (1004 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_183,negated_conjecture,(
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

tff(f_112,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_138,axiom,(
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

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_154,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_142,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_144,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_166,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(c_86,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_24581,plain,(
    ! [C_595,A_596,B_597] :
      ( v1_xboole_0(C_595)
      | ~ m1_subset_1(C_595,k1_zfmisc_1(k2_zfmisc_1(A_596,B_597)))
      | ~ v1_xboole_0(A_596) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_24603,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_24581])).

tff(c_24647,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_24603])).

tff(c_24498,plain,(
    ! [C_586,A_587,B_588] :
      ( v1_relat_1(C_586)
      | ~ m1_subset_1(C_586,k1_zfmisc_1(k2_zfmisc_1(A_587,B_588))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24518,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_24498])).

tff(c_90,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_84,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_82,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_25216,plain,(
    ! [A_641,B_642,C_643] :
      ( k2_relset_1(A_641,B_642,C_643) = k2_relat_1(C_643)
      | ~ m1_subset_1(C_643,k1_zfmisc_1(k2_zfmisc_1(A_641,B_642))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_25225,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_25216])).

tff(c_25240,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_25225])).

tff(c_40,plain,(
    ! [A_22] :
      ( k1_relat_1(k2_funct_1(A_22)) = k2_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_177,plain,(
    ! [A_59] :
      ( v1_funct_1(k2_funct_1(A_59))
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_80,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_169,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_180,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_177,c_169])).

tff(c_183,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_180])).

tff(c_316,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_322,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_316])).

tff(c_335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_322])).

tff(c_336,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_346,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_336])).

tff(c_395,plain,(
    ! [C_79,A_80,B_81] :
      ( v1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_411,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_395])).

tff(c_1229,plain,(
    ! [A_130,B_131,C_132] :
      ( k2_relset_1(A_130,B_131,C_132) = k2_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1238,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_1229])).

tff(c_1253,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1238])).

tff(c_34,plain,(
    ! [A_19] :
      ( v1_relat_1(k2_funct_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_88,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_1335,plain,(
    ! [A_136,B_137,C_138] :
      ( k1_relset_1(A_136,B_137,C_138) = k1_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1362,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_1335])).

tff(c_3262,plain,(
    ! [B_195,A_196,C_197] :
      ( k1_xboole_0 = B_195
      | k1_relset_1(A_196,B_195,C_197) = A_196
      | ~ v1_funct_2(C_197,A_196,B_195)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_196,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_3277,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_86,c_3262])).

tff(c_3297,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1362,c_3277])).

tff(c_3301,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3297])).

tff(c_756,plain,(
    ! [A_111] :
      ( k2_relat_1(k2_funct_1(A_111)) = k1_relat_1(A_111)
      | ~ v2_funct_1(A_111)
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_24,plain,(
    ! [A_16] :
      ( k10_relat_1(A_16,k2_relat_1(A_16)) = k1_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_9979,plain,(
    ! [A_304] :
      ( k10_relat_1(k2_funct_1(A_304),k1_relat_1(A_304)) = k1_relat_1(k2_funct_1(A_304))
      | ~ v1_relat_1(k2_funct_1(A_304))
      | ~ v2_funct_1(A_304)
      | ~ v1_funct_1(A_304)
      | ~ v1_relat_1(A_304) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_756,c_24])).

tff(c_9988,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3301,c_9979])).

tff(c_10001,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_90,c_84,c_9988])).

tff(c_10006,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_10001])).

tff(c_10009,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_10006])).

tff(c_10013,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_90,c_10009])).

tff(c_10015,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_10001])).

tff(c_337,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_1265,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1253,c_24])).

tff(c_1273,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_1265])).

tff(c_3309,plain,(
    k10_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3301,c_1273])).

tff(c_733,plain,(
    ! [A_108] :
      ( k1_relat_1(k2_funct_1(A_108)) = k2_relat_1(A_108)
      | ~ v2_funct_1(A_108)
      | ~ v1_funct_1(A_108)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_22,plain,(
    ! [A_15] :
      ( k9_relat_1(A_15,k1_relat_1(A_15)) = k2_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_13960,plain,(
    ! [A_344] :
      ( k9_relat_1(k2_funct_1(A_344),k2_relat_1(A_344)) = k2_relat_1(k2_funct_1(A_344))
      | ~ v1_relat_1(k2_funct_1(A_344))
      | ~ v2_funct_1(A_344)
      | ~ v1_funct_1(A_344)
      | ~ v1_relat_1(A_344) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_733,c_22])).

tff(c_13976,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1253,c_13960])).

tff(c_13989,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_90,c_84,c_10015,c_13976])).

tff(c_36,plain,(
    ! [B_21,A_20] :
      ( k9_relat_1(k2_funct_1(B_21),A_20) = k10_relat_1(B_21,A_20)
      | ~ v2_funct_1(B_21)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_13997,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13989,c_36])).

tff(c_14004,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_90,c_84,c_3309,c_13997])).

tff(c_68,plain,(
    ! [A_41] :
      ( m1_subset_1(A_41,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_41),k2_relat_1(A_41))))
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_14040,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14004,c_68])).

tff(c_14076,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10015,c_337,c_14040])).

tff(c_14178,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_14076])).

tff(c_14193,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_90,c_84,c_1253,c_14178])).

tff(c_14195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_346,c_14193])).

tff(c_14196,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3297])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_14243,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14196,c_2])).

tff(c_10,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14239,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14196,c_14196,c_10])).

tff(c_1259,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1253,c_68])).

tff(c_1269,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_90,c_1259])).

tff(c_16,plain,(
    ! [B_9,A_7] :
      ( v1_xboole_0(B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_7))
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1297,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_1269,c_16])).

tff(c_1399,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1297])).

tff(c_14503,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14239,c_1399])).

tff(c_14510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14243,c_14503])).

tff(c_14511,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1297])).

tff(c_165,plain,(
    ! [B_55,A_56] :
      ( ~ v1_xboole_0(B_55)
      | B_55 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_168,plain,(
    ! [A_56] :
      ( k1_xboole_0 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_2,c_165])).

tff(c_14534,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14511,c_168])).

tff(c_12,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_347,plain,(
    ! [A_73] : m1_subset_1(k6_partfun1(A_73),k1_zfmisc_1(k2_zfmisc_1(A_73,A_73))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_351,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_347])).

tff(c_427,plain,(
    ! [B_84,A_85] :
      ( v1_xboole_0(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_85))
      | ~ v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_430,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_351,c_427])).

tff(c_442,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_430])).

tff(c_455,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_442,c_168])).

tff(c_66,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_26,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_92,plain,(
    ! [A_17] : k1_relat_1(k6_partfun1(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_26])).

tff(c_493,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_92])).

tff(c_14554,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14534,c_14534,c_493])).

tff(c_44,plain,(
    ! [C_29,A_26,B_27] :
      ( v1_xboole_0(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1296,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1269,c_44])).

tff(c_1300,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1296])).

tff(c_14662,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14554,c_1300])).

tff(c_14668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14511,c_14662])).

tff(c_14669,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1296])).

tff(c_14692,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14669,c_168])).

tff(c_14748,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14692,c_14692,c_10])).

tff(c_28,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_91,plain,(
    ! [A_17] : k2_relat_1(k6_partfun1(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_28])).

tff(c_499,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_91])).

tff(c_14738,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14692,c_14692,c_499])).

tff(c_14901,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14738,c_1253])).

tff(c_444,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_86,c_427])).

tff(c_578,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_444])).

tff(c_14922,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14901,c_578])).

tff(c_15083,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14669,c_14748,c_14922])).

tff(c_15084,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_444])).

tff(c_15098,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_15084,c_168])).

tff(c_15113,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15098,c_15098,c_12])).

tff(c_64,plain,(
    ! [A_39] : m1_subset_1(k6_partfun1(A_39),k1_zfmisc_1(k2_zfmisc_1(A_39,A_39))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_458,plain,(
    ! [C_86,A_87,B_88] :
      ( v1_xboole_0(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_529,plain,(
    ! [A_89] :
      ( v1_xboole_0(k6_partfun1(A_89))
      | ~ v1_xboole_0(A_89) ) ),
    inference(resolution,[status(thm)],[c_64,c_458])).

tff(c_541,plain,(
    ! [A_89] :
      ( k6_partfun1(A_89) = k1_xboole_0
      | ~ v1_xboole_0(A_89) ) ),
    inference(resolution,[status(thm)],[c_529,c_168])).

tff(c_15097,plain,(
    k6_partfun1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_15084,c_541])).

tff(c_15135,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15098,c_15097])).

tff(c_15153,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_15135,c_91])).

tff(c_14,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_15116,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15098,c_14])).

tff(c_15471,plain,(
    ! [A_381,B_382,C_383] :
      ( k2_relset_1(A_381,B_382,C_383) = k2_relat_1(C_383)
      | ~ m1_subset_1(C_383,k1_zfmisc_1(k2_zfmisc_1(A_381,B_382))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_15487,plain,(
    ! [A_381,B_382] : k2_relset_1(A_381,B_382,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_15116,c_15471])).

tff(c_15493,plain,(
    ! [A_381,B_382] : k2_relset_1(A_381,B_382,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15153,c_15487])).

tff(c_15496,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15493,c_82])).

tff(c_15505,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15496,c_346])).

tff(c_15508,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15113,c_15505])).

tff(c_15147,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_15135,c_92])).

tff(c_15193,plain,(
    ! [A_367] :
      ( k2_relat_1(k2_funct_1(A_367)) = k1_relat_1(A_367)
      | ~ v2_funct_1(A_367)
      | ~ v1_funct_1(A_367)
      | ~ v1_relat_1(A_367) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_22351,plain,(
    ! [A_555] :
      ( k10_relat_1(k2_funct_1(A_555),k1_relat_1(A_555)) = k1_relat_1(k2_funct_1(A_555))
      | ~ v1_relat_1(k2_funct_1(A_555))
      | ~ v2_funct_1(A_555)
      | ~ v1_funct_1(A_555)
      | ~ v1_relat_1(A_555) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15193,c_24])).

tff(c_22363,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15147,c_22351])).

tff(c_22370,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_90,c_84,c_22363])).

tff(c_23473,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_22370])).

tff(c_23476,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_23473])).

tff(c_23480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_90,c_23476])).

tff(c_23482,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_22370])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_15118,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15098,c_4])).

tff(c_119,plain,(
    ! [A_50] : k2_zfmisc_1(A_50,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_123,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_20])).

tff(c_519,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_24])).

tff(c_523,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_493,c_519])).

tff(c_15104,plain,(
    k10_relat_1('#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15098,c_15098,c_15098,c_523])).

tff(c_15322,plain,(
    ! [A_372] :
      ( k1_relat_1(k2_funct_1(A_372)) = k2_relat_1(A_372)
      | ~ v2_funct_1(A_372)
      | ~ v1_funct_1(A_372)
      | ~ v1_relat_1(A_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_24360,plain,(
    ! [A_580] :
      ( k9_relat_1(k2_funct_1(A_580),k2_relat_1(A_580)) = k2_relat_1(k2_funct_1(A_580))
      | ~ v1_relat_1(k2_funct_1(A_580))
      | ~ v2_funct_1(A_580)
      | ~ v1_funct_1(A_580)
      | ~ v1_relat_1(A_580) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15322,c_22])).

tff(c_24379,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15153,c_24360])).

tff(c_24386,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_90,c_84,c_23482,c_24379])).

tff(c_24392,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24386,c_36])).

tff(c_24399,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_90,c_84,c_15104,c_24392])).

tff(c_15115,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15098,c_15098,c_10])).

tff(c_15804,plain,(
    ! [B_419,A_420] :
      ( m1_subset_1(B_419,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_419),A_420)))
      | ~ r1_tarski(k2_relat_1(B_419),A_420)
      | ~ v1_funct_1(B_419)
      | ~ v1_relat_1(B_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_15828,plain,(
    ! [B_419] :
      ( m1_subset_1(B_419,k1_zfmisc_1('#skF_3'))
      | ~ r1_tarski(k2_relat_1(B_419),'#skF_3')
      | ~ v1_funct_1(B_419)
      | ~ v1_relat_1(B_419) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15115,c_15804])).

tff(c_24420,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3'))
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_24399,c_15828])).

tff(c_24458,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23482,c_337,c_15118,c_24420])).

tff(c_24460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15508,c_24458])).

tff(c_24461,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_24462,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_24941,plain,(
    ! [A_625,B_626,C_627] :
      ( k1_relset_1(A_625,B_626,C_627) = k1_relat_1(C_627)
      | ~ m1_subset_1(C_627,k1_zfmisc_1(k2_zfmisc_1(A_625,B_626))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_24963,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_24462,c_24941])).

tff(c_26144,plain,(
    ! [B_684,C_685,A_686] :
      ( k1_xboole_0 = B_684
      | v1_funct_2(C_685,A_686,B_684)
      | k1_relset_1(A_686,B_684,C_685) != A_686
      | ~ m1_subset_1(C_685,k1_zfmisc_1(k2_zfmisc_1(A_686,B_684))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_26156,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_24462,c_26144])).

tff(c_26176,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24963,c_26156])).

tff(c_26177,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_24461,c_26176])).

tff(c_26185,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_26177])).

tff(c_26188,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_26185])).

tff(c_26191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24518,c_90,c_84,c_25240,c_26188])).

tff(c_26192,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26177])).

tff(c_26234,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26192,c_2])).

tff(c_26236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24647,c_26234])).

tff(c_26238,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_24603])).

tff(c_26259,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26238,c_168])).

tff(c_26237,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_24603])).

tff(c_26247,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26237,c_168])).

tff(c_26281,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26259,c_26247])).

tff(c_26299,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26281,c_24518])).

tff(c_30,plain,(
    ! [A_18] :
      ( v1_funct_1(A_18)
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26261,plain,(
    v1_funct_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26238,c_30])).

tff(c_24464,plain,(
    ! [A_582] : m1_subset_1(k6_partfun1(A_582),k1_zfmisc_1(k2_zfmisc_1(A_582,A_582))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_24468,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_24464])).

tff(c_24557,plain,(
    ! [B_593,A_594] :
      ( v1_xboole_0(B_593)
      | ~ m1_subset_1(B_593,k1_zfmisc_1(A_594))
      | ~ v1_xboole_0(A_594) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_24560,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24468,c_24557])).

tff(c_24575,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24560])).

tff(c_24616,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24575,c_168])).

tff(c_24640,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24616,c_91])).

tff(c_26339,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26259,c_26259,c_24640])).

tff(c_26262,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26247,c_26247,c_24616])).

tff(c_26316,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26281,c_26281,c_26262])).

tff(c_26328,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_26316,c_92])).

tff(c_70,plain,(
    ! [A_41] :
      ( v1_funct_2(A_41,k1_relat_1(A_41),k2_relat_1(A_41))
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_26362,plain,
    ( v1_funct_2('#skF_1','#skF_1',k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26328,c_70])).

tff(c_26369,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26299,c_26261,c_26339,c_26362])).

tff(c_50,plain,(
    ! [A_36] :
      ( v1_funct_2(k1_xboole_0,A_36,k1_xboole_0)
      | k1_xboole_0 = A_36
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_36,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_94,plain,(
    ! [A_36] :
      ( v1_funct_2(k1_xboole_0,A_36,k1_xboole_0)
      | k1_xboole_0 = A_36 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_50])).

tff(c_26265,plain,(
    ! [A_36] :
      ( v1_funct_2('#skF_3',A_36,'#skF_3')
      | A_36 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26247,c_26247,c_26247,c_94])).

tff(c_26558,plain,(
    ! [A_36] :
      ( v1_funct_2('#skF_1',A_36,'#skF_1')
      | A_36 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26281,c_26281,c_26281,c_26265])).

tff(c_26269,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26247,c_26247,c_10])).

tff(c_26424,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26281,c_26281,c_26269])).

tff(c_24577,plain,
    ( v1_xboole_0(k2_funct_1('#skF_3'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_24462,c_24557])).

tff(c_26575,plain,(
    v1_xboole_0(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26238,c_26424,c_26281,c_24577])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( ~ v1_xboole_0(B_3)
      | B_3 = A_2
      | ~ v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_26248,plain,(
    ! [A_2] :
      ( A_2 = '#skF_3'
      | ~ v1_xboole_0(A_2) ) ),
    inference(resolution,[status(thm)],[c_26237,c_6])).

tff(c_26379,plain,(
    ! [A_2] :
      ( A_2 = '#skF_1'
      | ~ v1_xboole_0(A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26281,c_26248])).

tff(c_26588,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26575,c_26379])).

tff(c_26301,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26281,c_24461])).

tff(c_26593,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26588,c_26301])).

tff(c_26626,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26558,c_26593])).

tff(c_26627,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26626,c_26593])).

tff(c_26633,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26369,c_26627])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:51:21 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.38/4.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.53/4.15  
% 11.53/4.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.53/4.15  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.53/4.15  
% 11.53/4.15  %Foreground sorts:
% 11.53/4.15  
% 11.53/4.15  
% 11.53/4.15  %Background operators:
% 11.53/4.15  
% 11.53/4.15  
% 11.53/4.15  %Foreground operators:
% 11.53/4.15  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.53/4.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.53/4.15  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.53/4.15  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.53/4.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.53/4.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.53/4.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.53/4.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.53/4.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.53/4.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.53/4.15  tff('#skF_2', type, '#skF_2': $i).
% 11.53/4.15  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.53/4.15  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 11.53/4.15  tff('#skF_3', type, '#skF_3': $i).
% 11.53/4.15  tff('#skF_1', type, '#skF_1': $i).
% 11.53/4.15  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.53/4.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.53/4.15  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 11.53/4.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.53/4.15  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 11.53/4.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.53/4.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.53/4.15  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 11.53/4.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.53/4.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.53/4.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.53/4.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.53/4.15  
% 11.65/4.18  tff(f_183, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 11.65/4.18  tff(f_112, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 11.65/4.18  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.65/4.18  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.65/4.18  tff(f_101, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 11.65/4.18  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 11.65/4.18  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.65/4.18  tff(f_138, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 11.65/4.18  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 11.65/4.18  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 11.65/4.18  tff(f_91, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 11.65/4.18  tff(f_154, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 11.65/4.18  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.65/4.18  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.65/4.18  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 11.65/4.18  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 11.65/4.18  tff(f_142, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 11.65/4.18  tff(f_144, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 11.65/4.18  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 11.65/4.18  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 11.65/4.18  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.65/4.18  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.65/4.18  tff(f_166, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 11.65/4.18  tff(f_75, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 11.65/4.18  tff(c_86, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_183])).
% 11.65/4.18  tff(c_24581, plain, (![C_595, A_596, B_597]: (v1_xboole_0(C_595) | ~m1_subset_1(C_595, k1_zfmisc_1(k2_zfmisc_1(A_596, B_597))) | ~v1_xboole_0(A_596))), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.65/4.18  tff(c_24603, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_86, c_24581])).
% 11.65/4.18  tff(c_24647, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_24603])).
% 11.65/4.18  tff(c_24498, plain, (![C_586, A_587, B_588]: (v1_relat_1(C_586) | ~m1_subset_1(C_586, k1_zfmisc_1(k2_zfmisc_1(A_587, B_588))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.65/4.18  tff(c_24518, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_24498])).
% 11.65/4.18  tff(c_90, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 11.65/4.18  tff(c_84, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_183])).
% 11.65/4.18  tff(c_82, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_183])).
% 11.65/4.18  tff(c_25216, plain, (![A_641, B_642, C_643]: (k2_relset_1(A_641, B_642, C_643)=k2_relat_1(C_643) | ~m1_subset_1(C_643, k1_zfmisc_1(k2_zfmisc_1(A_641, B_642))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.65/4.18  tff(c_25225, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_25216])).
% 11.65/4.18  tff(c_25240, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_25225])).
% 11.65/4.18  tff(c_40, plain, (![A_22]: (k1_relat_1(k2_funct_1(A_22))=k2_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.65/4.18  tff(c_177, plain, (![A_59]: (v1_funct_1(k2_funct_1(A_59)) | ~v1_funct_1(A_59) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.65/4.18  tff(c_80, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_183])).
% 11.65/4.18  tff(c_169, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_80])).
% 11.65/4.18  tff(c_180, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_177, c_169])).
% 11.65/4.18  tff(c_183, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_180])).
% 11.65/4.18  tff(c_316, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.65/4.18  tff(c_322, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_316])).
% 11.65/4.18  tff(c_335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183, c_322])).
% 11.65/4.18  tff(c_336, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_80])).
% 11.65/4.18  tff(c_346, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_336])).
% 11.65/4.18  tff(c_395, plain, (![C_79, A_80, B_81]: (v1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 11.65/4.18  tff(c_411, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_395])).
% 11.65/4.18  tff(c_1229, plain, (![A_130, B_131, C_132]: (k2_relset_1(A_130, B_131, C_132)=k2_relat_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.65/4.18  tff(c_1238, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_1229])).
% 11.65/4.18  tff(c_1253, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1238])).
% 11.65/4.18  tff(c_34, plain, (![A_19]: (v1_relat_1(k2_funct_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.65/4.18  tff(c_88, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_183])).
% 11.65/4.18  tff(c_1335, plain, (![A_136, B_137, C_138]: (k1_relset_1(A_136, B_137, C_138)=k1_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 11.65/4.18  tff(c_1362, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_1335])).
% 11.65/4.18  tff(c_3262, plain, (![B_195, A_196, C_197]: (k1_xboole_0=B_195 | k1_relset_1(A_196, B_195, C_197)=A_196 | ~v1_funct_2(C_197, A_196, B_195) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_196, B_195))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.65/4.18  tff(c_3277, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_86, c_3262])).
% 11.65/4.18  tff(c_3297, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1362, c_3277])).
% 11.65/4.18  tff(c_3301, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_3297])).
% 11.65/4.18  tff(c_756, plain, (![A_111]: (k2_relat_1(k2_funct_1(A_111))=k1_relat_1(A_111) | ~v2_funct_1(A_111) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.65/4.18  tff(c_24, plain, (![A_16]: (k10_relat_1(A_16, k2_relat_1(A_16))=k1_relat_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.65/4.18  tff(c_9979, plain, (![A_304]: (k10_relat_1(k2_funct_1(A_304), k1_relat_1(A_304))=k1_relat_1(k2_funct_1(A_304)) | ~v1_relat_1(k2_funct_1(A_304)) | ~v2_funct_1(A_304) | ~v1_funct_1(A_304) | ~v1_relat_1(A_304))), inference(superposition, [status(thm), theory('equality')], [c_756, c_24])).
% 11.65/4.18  tff(c_9988, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3301, c_9979])).
% 11.65/4.18  tff(c_10001, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_411, c_90, c_84, c_9988])).
% 11.65/4.18  tff(c_10006, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_10001])).
% 11.65/4.18  tff(c_10009, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_10006])).
% 11.65/4.18  tff(c_10013, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_411, c_90, c_10009])).
% 11.65/4.18  tff(c_10015, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_10001])).
% 11.65/4.18  tff(c_337, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_80])).
% 11.65/4.18  tff(c_1265, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1253, c_24])).
% 11.65/4.18  tff(c_1273, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_411, c_1265])).
% 11.65/4.18  tff(c_3309, plain, (k10_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3301, c_1273])).
% 11.65/4.18  tff(c_733, plain, (![A_108]: (k1_relat_1(k2_funct_1(A_108))=k2_relat_1(A_108) | ~v2_funct_1(A_108) | ~v1_funct_1(A_108) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.65/4.18  tff(c_22, plain, (![A_15]: (k9_relat_1(A_15, k1_relat_1(A_15))=k2_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.65/4.18  tff(c_13960, plain, (![A_344]: (k9_relat_1(k2_funct_1(A_344), k2_relat_1(A_344))=k2_relat_1(k2_funct_1(A_344)) | ~v1_relat_1(k2_funct_1(A_344)) | ~v2_funct_1(A_344) | ~v1_funct_1(A_344) | ~v1_relat_1(A_344))), inference(superposition, [status(thm), theory('equality')], [c_733, c_22])).
% 11.65/4.18  tff(c_13976, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1253, c_13960])).
% 11.65/4.18  tff(c_13989, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_411, c_90, c_84, c_10015, c_13976])).
% 11.65/4.18  tff(c_36, plain, (![B_21, A_20]: (k9_relat_1(k2_funct_1(B_21), A_20)=k10_relat_1(B_21, A_20) | ~v2_funct_1(B_21) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.65/4.18  tff(c_13997, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13989, c_36])).
% 11.65/4.18  tff(c_14004, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_411, c_90, c_84, c_3309, c_13997])).
% 11.65/4.18  tff(c_68, plain, (![A_41]: (m1_subset_1(A_41, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_41), k2_relat_1(A_41)))) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_154])).
% 11.65/4.18  tff(c_14040, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14004, c_68])).
% 11.65/4.18  tff(c_14076, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_10015, c_337, c_14040])).
% 11.65/4.18  tff(c_14178, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_14076])).
% 11.65/4.18  tff(c_14193, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_411, c_90, c_84, c_1253, c_14178])).
% 11.65/4.18  tff(c_14195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_346, c_14193])).
% 11.65/4.18  tff(c_14196, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_3297])).
% 11.65/4.18  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 11.65/4.18  tff(c_14243, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14196, c_2])).
% 11.65/4.18  tff(c_10, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.65/4.18  tff(c_14239, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14196, c_14196, c_10])).
% 11.65/4.18  tff(c_1259, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1253, c_68])).
% 11.65/4.18  tff(c_1269, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_411, c_90, c_1259])).
% 11.65/4.18  tff(c_16, plain, (![B_9, A_7]: (v1_xboole_0(B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_7)) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.65/4.18  tff(c_1297, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_1269, c_16])).
% 11.65/4.18  tff(c_1399, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_1297])).
% 11.65/4.18  tff(c_14503, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14239, c_1399])).
% 11.65/4.18  tff(c_14510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14243, c_14503])).
% 11.65/4.18  tff(c_14511, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_1297])).
% 11.65/4.18  tff(c_165, plain, (![B_55, A_56]: (~v1_xboole_0(B_55) | B_55=A_56 | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.65/4.18  tff(c_168, plain, (![A_56]: (k1_xboole_0=A_56 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_2, c_165])).
% 11.65/4.18  tff(c_14534, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_14511, c_168])).
% 11.65/4.18  tff(c_12, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.65/4.18  tff(c_347, plain, (![A_73]: (m1_subset_1(k6_partfun1(A_73), k1_zfmisc_1(k2_zfmisc_1(A_73, A_73))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.65/4.18  tff(c_351, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_347])).
% 11.65/4.18  tff(c_427, plain, (![B_84, A_85]: (v1_xboole_0(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(A_85)) | ~v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.65/4.18  tff(c_430, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_351, c_427])).
% 11.65/4.18  tff(c_442, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_430])).
% 11.65/4.18  tff(c_455, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_442, c_168])).
% 11.65/4.18  tff(c_66, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.65/4.18  tff(c_26, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.65/4.18  tff(c_92, plain, (![A_17]: (k1_relat_1(k6_partfun1(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_26])).
% 11.65/4.18  tff(c_493, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_455, c_92])).
% 11.65/4.18  tff(c_14554, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14534, c_14534, c_493])).
% 11.65/4.18  tff(c_44, plain, (![C_29, A_26, B_27]: (v1_xboole_0(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.65/4.18  tff(c_1296, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1269, c_44])).
% 11.65/4.18  tff(c_1300, plain, (~v1_xboole_0(k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1296])).
% 11.65/4.18  tff(c_14662, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14554, c_1300])).
% 11.65/4.18  tff(c_14668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14511, c_14662])).
% 11.65/4.18  tff(c_14669, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_1296])).
% 11.65/4.18  tff(c_14692, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_14669, c_168])).
% 11.65/4.18  tff(c_14748, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14692, c_14692, c_10])).
% 11.65/4.18  tff(c_28, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.65/4.18  tff(c_91, plain, (![A_17]: (k2_relat_1(k6_partfun1(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_28])).
% 11.65/4.18  tff(c_499, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_455, c_91])).
% 11.65/4.18  tff(c_14738, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14692, c_14692, c_499])).
% 11.65/4.18  tff(c_14901, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14738, c_1253])).
% 11.65/4.18  tff(c_444, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_86, c_427])).
% 11.65/4.18  tff(c_578, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_444])).
% 11.65/4.18  tff(c_14922, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14901, c_578])).
% 11.65/4.18  tff(c_15083, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14669, c_14748, c_14922])).
% 11.65/4.18  tff(c_15084, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_444])).
% 11.65/4.18  tff(c_15098, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_15084, c_168])).
% 11.65/4.18  tff(c_15113, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15098, c_15098, c_12])).
% 11.65/4.18  tff(c_64, plain, (![A_39]: (m1_subset_1(k6_partfun1(A_39), k1_zfmisc_1(k2_zfmisc_1(A_39, A_39))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.65/4.18  tff(c_458, plain, (![C_86, A_87, B_88]: (v1_xboole_0(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_112])).
% 11.65/4.18  tff(c_529, plain, (![A_89]: (v1_xboole_0(k6_partfun1(A_89)) | ~v1_xboole_0(A_89))), inference(resolution, [status(thm)], [c_64, c_458])).
% 11.65/4.18  tff(c_541, plain, (![A_89]: (k6_partfun1(A_89)=k1_xboole_0 | ~v1_xboole_0(A_89))), inference(resolution, [status(thm)], [c_529, c_168])).
% 11.65/4.18  tff(c_15097, plain, (k6_partfun1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_15084, c_541])).
% 11.65/4.18  tff(c_15135, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15098, c_15097])).
% 11.65/4.18  tff(c_15153, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_15135, c_91])).
% 11.65/4.18  tff(c_14, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.65/4.18  tff(c_15116, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_15098, c_14])).
% 11.65/4.18  tff(c_15471, plain, (![A_381, B_382, C_383]: (k2_relset_1(A_381, B_382, C_383)=k2_relat_1(C_383) | ~m1_subset_1(C_383, k1_zfmisc_1(k2_zfmisc_1(A_381, B_382))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.65/4.18  tff(c_15487, plain, (![A_381, B_382]: (k2_relset_1(A_381, B_382, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_15116, c_15471])).
% 11.65/4.18  tff(c_15493, plain, (![A_381, B_382]: (k2_relset_1(A_381, B_382, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15153, c_15487])).
% 11.65/4.18  tff(c_15496, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15493, c_82])).
% 11.65/4.18  tff(c_15505, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_15496, c_346])).
% 11.65/4.18  tff(c_15508, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_15113, c_15505])).
% 11.65/4.18  tff(c_15147, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_15135, c_92])).
% 11.65/4.18  tff(c_15193, plain, (![A_367]: (k2_relat_1(k2_funct_1(A_367))=k1_relat_1(A_367) | ~v2_funct_1(A_367) | ~v1_funct_1(A_367) | ~v1_relat_1(A_367))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.65/4.18  tff(c_22351, plain, (![A_555]: (k10_relat_1(k2_funct_1(A_555), k1_relat_1(A_555))=k1_relat_1(k2_funct_1(A_555)) | ~v1_relat_1(k2_funct_1(A_555)) | ~v2_funct_1(A_555) | ~v1_funct_1(A_555) | ~v1_relat_1(A_555))), inference(superposition, [status(thm), theory('equality')], [c_15193, c_24])).
% 11.65/4.18  tff(c_22363, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_15147, c_22351])).
% 11.65/4.18  tff(c_22370, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_411, c_90, c_84, c_22363])).
% 11.65/4.18  tff(c_23473, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_22370])).
% 11.65/4.18  tff(c_23476, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_23473])).
% 11.65/4.18  tff(c_23480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_411, c_90, c_23476])).
% 11.65/4.18  tff(c_23482, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_22370])).
% 11.65/4.18  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 11.65/4.18  tff(c_15118, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_15098, c_4])).
% 11.65/4.18  tff(c_119, plain, (![A_50]: (k2_zfmisc_1(A_50, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.65/4.18  tff(c_20, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.65/4.18  tff(c_123, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_119, c_20])).
% 11.65/4.18  tff(c_519, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_499, c_24])).
% 11.65/4.18  tff(c_523, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_123, c_493, c_519])).
% 11.65/4.18  tff(c_15104, plain, (k10_relat_1('#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15098, c_15098, c_15098, c_523])).
% 11.65/4.18  tff(c_15322, plain, (![A_372]: (k1_relat_1(k2_funct_1(A_372))=k2_relat_1(A_372) | ~v2_funct_1(A_372) | ~v1_funct_1(A_372) | ~v1_relat_1(A_372))), inference(cnfTransformation, [status(thm)], [f_101])).
% 11.65/4.18  tff(c_24360, plain, (![A_580]: (k9_relat_1(k2_funct_1(A_580), k2_relat_1(A_580))=k2_relat_1(k2_funct_1(A_580)) | ~v1_relat_1(k2_funct_1(A_580)) | ~v2_funct_1(A_580) | ~v1_funct_1(A_580) | ~v1_relat_1(A_580))), inference(superposition, [status(thm), theory('equality')], [c_15322, c_22])).
% 11.65/4.18  tff(c_24379, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_15153, c_24360])).
% 11.65/4.18  tff(c_24386, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_411, c_90, c_84, c_23482, c_24379])).
% 11.65/4.18  tff(c_24392, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24386, c_36])).
% 11.65/4.18  tff(c_24399, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_411, c_90, c_84, c_15104, c_24392])).
% 11.65/4.18  tff(c_15115, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15098, c_15098, c_10])).
% 11.65/4.18  tff(c_15804, plain, (![B_419, A_420]: (m1_subset_1(B_419, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_419), A_420))) | ~r1_tarski(k2_relat_1(B_419), A_420) | ~v1_funct_1(B_419) | ~v1_relat_1(B_419))), inference(cnfTransformation, [status(thm)], [f_166])).
% 11.65/4.18  tff(c_15828, plain, (![B_419]: (m1_subset_1(B_419, k1_zfmisc_1('#skF_3')) | ~r1_tarski(k2_relat_1(B_419), '#skF_3') | ~v1_funct_1(B_419) | ~v1_relat_1(B_419))), inference(superposition, [status(thm), theory('equality')], [c_15115, c_15804])).
% 11.65/4.18  tff(c_24420, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3')) | ~r1_tarski('#skF_3', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_24399, c_15828])).
% 11.65/4.18  tff(c_24458, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_23482, c_337, c_15118, c_24420])).
% 11.65/4.18  tff(c_24460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15508, c_24458])).
% 11.65/4.18  tff(c_24461, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_336])).
% 11.65/4.18  tff(c_24462, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_336])).
% 11.65/4.18  tff(c_24941, plain, (![A_625, B_626, C_627]: (k1_relset_1(A_625, B_626, C_627)=k1_relat_1(C_627) | ~m1_subset_1(C_627, k1_zfmisc_1(k2_zfmisc_1(A_625, B_626))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 11.65/4.18  tff(c_24963, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_24462, c_24941])).
% 11.65/4.18  tff(c_26144, plain, (![B_684, C_685, A_686]: (k1_xboole_0=B_684 | v1_funct_2(C_685, A_686, B_684) | k1_relset_1(A_686, B_684, C_685)!=A_686 | ~m1_subset_1(C_685, k1_zfmisc_1(k2_zfmisc_1(A_686, B_684))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.65/4.18  tff(c_26156, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_24462, c_26144])).
% 11.65/4.18  tff(c_26176, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24963, c_26156])).
% 11.65/4.18  tff(c_26177, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_24461, c_26176])).
% 11.65/4.18  tff(c_26185, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_26177])).
% 11.65/4.18  tff(c_26188, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40, c_26185])).
% 11.65/4.18  tff(c_26191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24518, c_90, c_84, c_25240, c_26188])).
% 11.65/4.18  tff(c_26192, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_26177])).
% 11.65/4.18  tff(c_26234, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26192, c_2])).
% 11.65/4.18  tff(c_26236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24647, c_26234])).
% 11.65/4.18  tff(c_26238, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_24603])).
% 11.65/4.18  tff(c_26259, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26238, c_168])).
% 11.65/4.18  tff(c_26237, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_24603])).
% 11.65/4.18  tff(c_26247, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_26237, c_168])).
% 11.65/4.18  tff(c_26281, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26259, c_26247])).
% 11.65/4.18  tff(c_26299, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26281, c_24518])).
% 11.65/4.18  tff(c_30, plain, (![A_18]: (v1_funct_1(A_18) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.65/4.18  tff(c_26261, plain, (v1_funct_1('#skF_1')), inference(resolution, [status(thm)], [c_26238, c_30])).
% 11.65/4.18  tff(c_24464, plain, (![A_582]: (m1_subset_1(k6_partfun1(A_582), k1_zfmisc_1(k2_zfmisc_1(A_582, A_582))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 11.65/4.18  tff(c_24468, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_24464])).
% 11.65/4.18  tff(c_24557, plain, (![B_593, A_594]: (v1_xboole_0(B_593) | ~m1_subset_1(B_593, k1_zfmisc_1(A_594)) | ~v1_xboole_0(A_594))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.65/4.18  tff(c_24560, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_24468, c_24557])).
% 11.65/4.18  tff(c_24575, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24560])).
% 11.65/4.18  tff(c_24616, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_24575, c_168])).
% 11.65/4.18  tff(c_24640, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_24616, c_91])).
% 11.65/4.18  tff(c_26339, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26259, c_26259, c_24640])).
% 11.65/4.18  tff(c_26262, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26247, c_26247, c_24616])).
% 11.65/4.18  tff(c_26316, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26281, c_26281, c_26262])).
% 11.65/4.18  tff(c_26328, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_26316, c_92])).
% 11.65/4.18  tff(c_70, plain, (![A_41]: (v1_funct_2(A_41, k1_relat_1(A_41), k2_relat_1(A_41)) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_154])).
% 11.65/4.18  tff(c_26362, plain, (v1_funct_2('#skF_1', '#skF_1', k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26328, c_70])).
% 11.65/4.18  tff(c_26369, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26299, c_26261, c_26339, c_26362])).
% 11.65/4.18  tff(c_50, plain, (![A_36]: (v1_funct_2(k1_xboole_0, A_36, k1_xboole_0) | k1_xboole_0=A_36 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_36, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 11.65/4.18  tff(c_94, plain, (![A_36]: (v1_funct_2(k1_xboole_0, A_36, k1_xboole_0) | k1_xboole_0=A_36)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_50])).
% 11.65/4.18  tff(c_26265, plain, (![A_36]: (v1_funct_2('#skF_3', A_36, '#skF_3') | A_36='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26247, c_26247, c_26247, c_94])).
% 11.65/4.18  tff(c_26558, plain, (![A_36]: (v1_funct_2('#skF_1', A_36, '#skF_1') | A_36='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26281, c_26281, c_26281, c_26265])).
% 11.65/4.18  tff(c_26269, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26247, c_26247, c_10])).
% 11.65/4.18  tff(c_26424, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26281, c_26281, c_26269])).
% 11.65/4.18  tff(c_24577, plain, (v1_xboole_0(k2_funct_1('#skF_3')) | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_24462, c_24557])).
% 11.65/4.18  tff(c_26575, plain, (v1_xboole_0(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26238, c_26424, c_26281, c_24577])).
% 11.65/4.18  tff(c_6, plain, (![B_3, A_2]: (~v1_xboole_0(B_3) | B_3=A_2 | ~v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 11.65/4.18  tff(c_26248, plain, (![A_2]: (A_2='#skF_3' | ~v1_xboole_0(A_2))), inference(resolution, [status(thm)], [c_26237, c_6])).
% 11.65/4.18  tff(c_26379, plain, (![A_2]: (A_2='#skF_1' | ~v1_xboole_0(A_2))), inference(demodulation, [status(thm), theory('equality')], [c_26281, c_26248])).
% 11.65/4.18  tff(c_26588, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_26575, c_26379])).
% 11.65/4.18  tff(c_26301, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26281, c_24461])).
% 11.65/4.18  tff(c_26593, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26588, c_26301])).
% 11.65/4.18  tff(c_26626, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_26558, c_26593])).
% 11.65/4.18  tff(c_26627, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26626, c_26593])).
% 11.65/4.18  tff(c_26633, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26369, c_26627])).
% 11.65/4.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.65/4.18  
% 11.65/4.18  Inference rules
% 11.65/4.18  ----------------------
% 11.65/4.18  #Ref     : 0
% 11.65/4.18  #Sup     : 7473
% 11.65/4.18  #Fact    : 0
% 11.65/4.18  #Define  : 0
% 11.65/4.18  #Split   : 40
% 11.65/4.18  #Chain   : 0
% 11.65/4.18  #Close   : 0
% 11.65/4.18  
% 11.65/4.18  Ordering : KBO
% 11.65/4.18  
% 11.65/4.18  Simplification rules
% 11.65/4.18  ----------------------
% 11.65/4.18  #Subsume      : 2755
% 11.65/4.18  #Demod        : 4679
% 11.65/4.18  #Tautology    : 1554
% 11.65/4.18  #SimpNegUnit  : 5
% 11.65/4.18  #BackRed      : 253
% 11.65/4.18  
% 11.65/4.18  #Partial instantiations: 0
% 11.65/4.18  #Strategies tried      : 1
% 11.65/4.18  
% 11.65/4.18  Timing (in seconds)
% 11.65/4.18  ----------------------
% 11.65/4.19  Preprocessing        : 0.35
% 11.65/4.19  Parsing              : 0.19
% 11.65/4.19  CNF conversion       : 0.02
% 11.65/4.19  Main loop            : 3.02
% 11.65/4.19  Inferencing          : 0.75
% 11.65/4.19  Reduction            : 1.01
% 11.65/4.19  Demodulation         : 0.76
% 11.65/4.19  BG Simplification    : 0.10
% 11.65/4.19  Subsumption          : 0.97
% 11.65/4.19  Abstraction          : 0.13
% 11.65/4.19  MUC search           : 0.00
% 11.65/4.19  Cooper               : 0.00
% 11.65/4.19  Total                : 3.45
% 11.65/4.19  Index Insertion      : 0.00
% 11.65/4.19  Index Deletion       : 0.00
% 11.65/4.19  Index Matching       : 0.00
% 11.65/4.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
