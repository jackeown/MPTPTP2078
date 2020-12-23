%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:35 EST 2020

% Result     : Theorem 15.43s
% Output     : CNFRefutation 15.43s
% Verified   : 
% Statistics : Number of formulae       :  267 (1763 expanded)
%              Number of leaves         :   45 ( 592 expanded)
%              Depth                    :   12
%              Number of atoms          :  447 (4514 expanded)
%              Number of equality atoms :  121 ( 933 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_181,negated_conjecture,(
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

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_152,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_125,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_129,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_142,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_88,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_50681,plain,(
    ! [C_1322,A_1323,B_1324] :
      ( v1_xboole_0(C_1322)
      | ~ m1_subset_1(C_1322,k1_zfmisc_1(k2_zfmisc_1(A_1323,B_1324)))
      | ~ v1_xboole_0(A_1323) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_50707,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_50681])).

tff(c_50712,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50707])).

tff(c_50532,plain,(
    ! [C_1304,A_1305,B_1306] :
      ( v1_relat_1(C_1304)
      | ~ m1_subset_1(C_1304,k1_zfmisc_1(k2_zfmisc_1(A_1305,B_1306))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_50557,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_50532])).

tff(c_92,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_86,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_84,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_51193,plain,(
    ! [A_1364,B_1365,C_1366] :
      ( k2_relset_1(A_1364,B_1365,C_1366) = k2_relat_1(C_1366)
      | ~ m1_subset_1(C_1366,k1_zfmisc_1(k2_zfmisc_1(A_1364,B_1365))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_51208,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_51193])).

tff(c_51225,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_51208])).

tff(c_32,plain,(
    ! [A_18] :
      ( k1_relat_1(k2_funct_1(A_18)) = k2_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_173,plain,(
    ! [A_64] :
      ( v1_funct_1(k2_funct_1(A_64))
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_82,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_161,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_176,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_173,c_161])).

tff(c_179,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_176])).

tff(c_263,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_272,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_263])).

tff(c_287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_272])).

tff(c_288,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_300,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_333,plain,(
    ! [C_87,A_88,B_89] :
      ( v1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_354,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_333])).

tff(c_1060,plain,(
    ! [A_145,B_146,C_147] :
      ( k2_relset_1(A_145,B_146,C_147) = k2_relat_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1072,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_1060])).

tff(c_1088,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1072])).

tff(c_28,plain,(
    ! [A_17] :
      ( v1_relat_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_289,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_789,plain,(
    ! [A_125] :
      ( k1_relat_1(k2_funct_1(A_125)) = k2_relat_1(A_125)
      | ~ v2_funct_1(A_125)
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_72,plain,(
    ! [A_40] :
      ( v1_funct_2(A_40,k1_relat_1(A_40),k2_relat_1(A_40))
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_16892,plain,(
    ! [A_521] :
      ( v1_funct_2(k2_funct_1(A_521),k2_relat_1(A_521),k2_relat_1(k2_funct_1(A_521)))
      | ~ v1_funct_1(k2_funct_1(A_521))
      | ~ v1_relat_1(k2_funct_1(A_521))
      | ~ v2_funct_1(A_521)
      | ~ v1_funct_1(A_521)
      | ~ v1_relat_1(A_521) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_789,c_72])).

tff(c_16916,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1088,c_16892])).

tff(c_16944,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_92,c_86,c_289,c_16916])).

tff(c_16949,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_16944])).

tff(c_16952,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_16949])).

tff(c_16956,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_92,c_16952])).

tff(c_16958,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_16944])).

tff(c_90,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_998,plain,(
    ! [A_139,B_140,C_141] :
      ( k1_relset_1(A_139,B_140,C_141) = k1_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1025,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_998])).

tff(c_2247,plain,(
    ! [B_219,A_220,C_221] :
      ( k1_xboole_0 = B_219
      | k1_relset_1(A_220,B_219,C_221) = A_220
      | ~ v1_funct_2(C_221,A_220,B_219)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_220,B_219))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2265,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_2247])).

tff(c_2287,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1025,c_2265])).

tff(c_2291,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2287])).

tff(c_30,plain,(
    ! [A_18] :
      ( k2_relat_1(k2_funct_1(A_18)) = k1_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_869,plain,(
    ! [A_131] :
      ( m1_subset_1(A_131,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_131),k2_relat_1(A_131))))
      | ~ v1_funct_1(A_131)
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_20129,plain,(
    ! [A_564] :
      ( m1_subset_1(k2_funct_1(A_564),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_564)),k1_relat_1(A_564))))
      | ~ v1_funct_1(k2_funct_1(A_564))
      | ~ v1_relat_1(k2_funct_1(A_564))
      | ~ v2_funct_1(A_564)
      | ~ v1_funct_1(A_564)
      | ~ v1_relat_1(A_564) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_869])).

tff(c_20176,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2291,c_20129])).

tff(c_20217,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_92,c_86,c_16958,c_289,c_20176])).

tff(c_20254,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),'#skF_2')))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_20217])).

tff(c_20270,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_92,c_86,c_1088,c_20254])).

tff(c_20272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_20270])).

tff(c_20273,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2287])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_20323,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20273,c_2])).

tff(c_10,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20321,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20273,c_20273,c_10])).

tff(c_70,plain,(
    ! [A_40] :
      ( m1_subset_1(A_40,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_40),k2_relat_1(A_40))))
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1094,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1088,c_70])).

tff(c_1101,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_92,c_1094])).

tff(c_16,plain,(
    ! [B_9,A_7] :
      ( v1_xboole_0(B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_7))
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1160,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_1101,c_16])).

tff(c_1188,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1160])).

tff(c_20541,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20321,c_1188])).

tff(c_20548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20323,c_20541])).

tff(c_20549,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1160])).

tff(c_290,plain,(
    ! [B_75,A_76] :
      ( ~ v1_xboole_0(B_75)
      | B_75 = A_76
      | ~ v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_293,plain,(
    ! [A_76] :
      ( k1_xboole_0 = A_76
      | ~ v1_xboole_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_2,c_290])).

tff(c_20569,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20549,c_293])).

tff(c_12,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_302,plain,(
    ! [A_79] : m1_subset_1(k6_partfun1(A_79),k1_zfmisc_1(k2_zfmisc_1(A_79,A_79))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_306,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_302])).

tff(c_379,plain,(
    ! [B_92,A_93] :
      ( v1_xboole_0(B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_93))
      | ~ v1_xboole_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_391,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_306,c_379])).

tff(c_410,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_391])).

tff(c_420,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_410,c_293])).

tff(c_68,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_20,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_94,plain,(
    ! [A_13] : k1_relat_1(k6_partfun1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_20])).

tff(c_440,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_94])).

tff(c_20589,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20569,c_20569,c_440])).

tff(c_36,plain,(
    ! [C_25,A_22,B_23] :
      ( v1_xboole_0(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1156,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1101,c_36])).

tff(c_1183,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1156])).

tff(c_20680,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20589,c_1183])).

tff(c_20683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20549,c_20680])).

tff(c_20684,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1156])).

tff(c_20723,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20684,c_293])).

tff(c_20755,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20723,c_20723,c_10])).

tff(c_22,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_93,plain,(
    ! [A_13] : k2_relat_1(k6_partfun1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_22])).

tff(c_434,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_93])).

tff(c_20746,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20723,c_20723,c_434])).

tff(c_20814,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20746,c_1088])).

tff(c_412,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_88,c_379])).

tff(c_450,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_412])).

tff(c_20834,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20814,c_450])).

tff(c_21097,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20684,c_20755,c_20834])).

tff(c_21098,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_412])).

tff(c_21124,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_21098,c_293])).

tff(c_21136,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21124,c_21124,c_12])).

tff(c_21137,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21124,c_21124,c_10])).

tff(c_21099,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_412])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( ~ v1_xboole_0(B_3)
      | B_3 = A_2
      | ~ v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_21198,plain,(
    ! [A_593] :
      ( A_593 = '#skF_4'
      | ~ v1_xboole_0(A_593) ) ),
    inference(resolution,[status(thm)],[c_21098,c_6])).

tff(c_21205,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_21099,c_21198])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_21968,plain,(
    ! [B_648,A_649] :
      ( B_648 = '#skF_4'
      | A_649 = '#skF_4'
      | k2_zfmisc_1(A_649,B_648) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21124,c_21124,c_21124,c_8])).

tff(c_21978,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_21205,c_21968])).

tff(c_21983,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_21978])).

tff(c_21987,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21983,c_300])).

tff(c_21992,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21137,c_21987])).

tff(c_21126,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21124,c_21124,c_434])).

tff(c_21506,plain,(
    ! [A_620] :
      ( k1_relat_1(k2_funct_1(A_620)) = k2_relat_1(A_620)
      | ~ v2_funct_1(A_620)
      | ~ v1_funct_1(A_620)
      | ~ v1_relat_1(A_620) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_34209,plain,(
    ! [A_959] :
      ( v1_funct_2(k2_funct_1(A_959),k2_relat_1(A_959),k2_relat_1(k2_funct_1(A_959)))
      | ~ v1_funct_1(k2_funct_1(A_959))
      | ~ v1_relat_1(k2_funct_1(A_959))
      | ~ v2_funct_1(A_959)
      | ~ v1_funct_1(A_959)
      | ~ v1_relat_1(A_959) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21506,c_72])).

tff(c_34236,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_21126,c_34209])).

tff(c_34253,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_92,c_86,c_289,c_34236])).

tff(c_35404,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_34253])).

tff(c_35407,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_35404])).

tff(c_35411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_92,c_35407])).

tff(c_35413,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_34253])).

tff(c_21907,plain,(
    ! [A_644] :
      ( m1_subset_1(A_644,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_644),k2_relat_1(A_644))))
      | ~ v1_funct_1(A_644)
      | ~ v1_relat_1(A_644) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_36955,plain,(
    ! [A_980] :
      ( m1_subset_1(k2_funct_1(A_980),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_980),k2_relat_1(k2_funct_1(A_980)))))
      | ~ v1_funct_1(k2_funct_1(A_980))
      | ~ v1_relat_1(k2_funct_1(A_980))
      | ~ v2_funct_1(A_980)
      | ~ v1_funct_1(A_980)
      | ~ v1_relat_1(A_980) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_21907])).

tff(c_37011,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_21126,c_36955])).

tff(c_37039,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_92,c_86,c_35413,c_289,c_21136,c_37011])).

tff(c_37041,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21992,c_37039])).

tff(c_37042,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_21978])).

tff(c_37047,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37042,c_300])).

tff(c_37052,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21136,c_37047])).

tff(c_21168,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21124,c_21124,c_440])).

tff(c_21472,plain,(
    ! [A_615] :
      ( k2_relat_1(k2_funct_1(A_615)) = k1_relat_1(A_615)
      | ~ v2_funct_1(A_615)
      | ~ v1_funct_1(A_615)
      | ~ v1_relat_1(A_615) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_47751,plain,(
    ! [A_1268] :
      ( v1_funct_2(k2_funct_1(A_1268),k1_relat_1(k2_funct_1(A_1268)),k1_relat_1(A_1268))
      | ~ v1_funct_1(k2_funct_1(A_1268))
      | ~ v1_relat_1(k2_funct_1(A_1268))
      | ~ v2_funct_1(A_1268)
      | ~ v1_funct_1(A_1268)
      | ~ v1_relat_1(A_1268) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21472,c_72])).

tff(c_47778,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_21168,c_47751])).

tff(c_47795,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_92,c_86,c_289,c_47778])).

tff(c_47798,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_47795])).

tff(c_47801,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_47798])).

tff(c_47805,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_92,c_47801])).

tff(c_47807,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_47795])).

tff(c_50282,plain,(
    ! [A_1288] :
      ( m1_subset_1(k2_funct_1(A_1288),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1288)),k1_relat_1(A_1288))))
      | ~ v1_funct_1(k2_funct_1(A_1288))
      | ~ v1_relat_1(k2_funct_1(A_1288))
      | ~ v2_funct_1(A_1288)
      | ~ v1_funct_1(A_1288)
      | ~ v1_relat_1(A_1288) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_21907])).

tff(c_50338,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_21168,c_50282])).

tff(c_50366,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_92,c_86,c_47807,c_289,c_21137,c_50338])).

tff(c_50368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37052,c_50366])).

tff(c_50369,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_50370,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_51305,plain,(
    ! [A_1370,B_1371,C_1372] :
      ( k1_relset_1(A_1370,B_1371,C_1372) = k1_relat_1(C_1372)
      | ~ m1_subset_1(C_1372,k1_zfmisc_1(k2_zfmisc_1(A_1370,B_1371))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_51337,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_50370,c_51305])).

tff(c_52480,plain,(
    ! [B_1438,C_1439,A_1440] :
      ( k1_xboole_0 = B_1438
      | v1_funct_2(C_1439,A_1440,B_1438)
      | k1_relset_1(A_1440,B_1438,C_1439) != A_1440
      | ~ m1_subset_1(C_1439,k1_zfmisc_1(k2_zfmisc_1(A_1440,B_1438))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_52492,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_50370,c_52480])).

tff(c_52514,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51337,c_52492])).

tff(c_52515,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_50369,c_52514])).

tff(c_52525,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_52515])).

tff(c_52528,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_52525])).

tff(c_52531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50557,c_92,c_86,c_51225,c_52528])).

tff(c_52532,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_52515])).

tff(c_52583,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52532,c_2])).

tff(c_52585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50712,c_52583])).

tff(c_52586,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_50707])).

tff(c_52593,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52586,c_293])).

tff(c_52620,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52593,c_52593,c_10])).

tff(c_52587,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_50707])).

tff(c_52600,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_52587,c_293])).

tff(c_52630,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52593,c_52600])).

tff(c_50391,plain,(
    ! [B_1295,A_1296] :
      ( v1_xboole_0(B_1295)
      | ~ m1_subset_1(B_1295,k1_zfmisc_1(A_1296))
      | ~ v1_xboole_0(A_1296) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50417,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50370,c_50391])).

tff(c_50507,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_50417])).

tff(c_52633,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52630,c_50507])).

tff(c_52825,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52586,c_52620,c_52633])).

tff(c_52827,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_50417])).

tff(c_52872,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_52827,c_293])).

tff(c_52910,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_52872,c_8])).

tff(c_52912,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_52910])).

tff(c_52953,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52912,c_2])).

tff(c_52951,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52912,c_52912,c_10])).

tff(c_50422,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_88,c_50391])).

tff(c_50457,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_50422])).

tff(c_53108,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52951,c_50457])).

tff(c_53112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52953,c_53108])).

tff(c_53113,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_52910])).

tff(c_53134,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53113,c_2])).

tff(c_53131,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_2',B_5) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53113,c_53113,c_12])).

tff(c_53222,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53131,c_50457])).

tff(c_53226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53134,c_53222])).

tff(c_53227,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_50422])).

tff(c_53234,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_53227,c_293])).

tff(c_50371,plain,(
    ! [A_1289] : m1_subset_1(k6_partfun1(A_1289),k1_zfmisc_1(k2_zfmisc_1(A_1289,A_1289))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_50375,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_50371])).

tff(c_50403,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_50375,c_50391])).

tff(c_50420,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_50403])).

tff(c_50430,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50420,c_293])).

tff(c_53249,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53234,c_53234,c_50430])).

tff(c_53276,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_53249,c_94])).

tff(c_14,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_53253,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53234,c_14])).

tff(c_55540,plain,(
    ! [A_1639,B_1640,C_1641] :
      ( k1_relset_1(A_1639,B_1640,C_1641) = k1_relat_1(C_1641)
      | ~ m1_subset_1(C_1641,k1_zfmisc_1(k2_zfmisc_1(A_1639,B_1640))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_55550,plain,(
    ! [A_1639,B_1640] : k1_relset_1(A_1639,B_1640,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_53253,c_55540])).

tff(c_55562,plain,(
    ! [A_1639,B_1640] : k1_relset_1(A_1639,B_1640,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53276,c_55550])).

tff(c_46,plain,(
    ! [C_34,B_33] :
      ( v1_funct_2(C_34,k1_xboole_0,B_33)
      | k1_relset_1(k1_xboole_0,B_33,C_34) != k1_xboole_0
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_97,plain,(
    ! [C_34,B_33] :
      ( v1_funct_2(C_34,k1_xboole_0,B_33)
      | k1_relset_1(k1_xboole_0,B_33,C_34) != k1_xboole_0
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_46])).

tff(c_56320,plain,(
    ! [C_1683,B_1684] :
      ( v1_funct_2(C_1683,'#skF_4',B_1684)
      | k1_relset_1('#skF_4',B_1684,C_1683) != '#skF_4'
      | ~ m1_subset_1(C_1683,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53234,c_53234,c_53234,c_53234,c_97])).

tff(c_56325,plain,(
    ! [B_1684] :
      ( v1_funct_2('#skF_4','#skF_4',B_1684)
      | k1_relset_1('#skF_4',B_1684,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_53253,c_56320])).

tff(c_56329,plain,(
    ! [B_1684] : v1_funct_2('#skF_4','#skF_4',B_1684) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55562,c_56325])).

tff(c_50442,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_50430,c_93])).

tff(c_53248,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53234,c_53234,c_50442])).

tff(c_54489,plain,(
    ! [A_1558,B_1559,C_1560] :
      ( k2_relset_1(A_1558,B_1559,C_1560) = k2_relat_1(C_1560)
      | ~ m1_subset_1(C_1560,k1_zfmisc_1(k2_zfmisc_1(A_1558,B_1559))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_54502,plain,(
    ! [A_1558,B_1559] : k2_relset_1(A_1558,B_1559,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_53253,c_54489])).

tff(c_54513,plain,(
    ! [A_1558,B_1559] : k2_relset_1(A_1558,B_1559,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53248,c_54502])).

tff(c_54517,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54513,c_84])).

tff(c_53451,plain,(
    ! [C_1490,A_1491,B_1492] :
      ( v1_xboole_0(C_1490)
      | ~ m1_subset_1(C_1490,k1_zfmisc_1(k2_zfmisc_1(A_1491,B_1492)))
      | ~ v1_xboole_0(A_1491) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_53479,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50370,c_53451])).

tff(c_53481,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_53479])).

tff(c_54529,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54517,c_53481])).

tff(c_54537,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53227,c_54529])).

tff(c_54538,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_53479])).

tff(c_53235,plain,(
    ! [A_2] :
      ( A_2 = '#skF_4'
      | ~ v1_xboole_0(A_2) ) ),
    inference(resolution,[status(thm)],[c_53227,c_6])).

tff(c_54620,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54538,c_53235])).

tff(c_54539,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_53479])).

tff(c_54545,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54539,c_53235])).

tff(c_54595,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54545,c_50369])).

tff(c_54675,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54620,c_54595])).

tff(c_56333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56329,c_54675])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:28:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.43/7.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.43/7.24  
% 15.43/7.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.43/7.24  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 15.43/7.24  
% 15.43/7.24  %Foreground sorts:
% 15.43/7.24  
% 15.43/7.24  
% 15.43/7.24  %Background operators:
% 15.43/7.24  
% 15.43/7.24  
% 15.43/7.24  %Foreground operators:
% 15.43/7.24  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 15.43/7.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.43/7.24  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 15.43/7.24  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 15.43/7.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.43/7.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.43/7.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.43/7.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.43/7.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.43/7.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.43/7.24  tff('#skF_2', type, '#skF_2': $i).
% 15.43/7.24  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 15.43/7.24  tff('#skF_3', type, '#skF_3': $i).
% 15.43/7.24  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 15.43/7.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 15.43/7.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.43/7.24  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 15.43/7.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.43/7.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.43/7.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.43/7.24  tff('#skF_4', type, '#skF_4': $i).
% 15.43/7.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 15.43/7.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.43/7.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 15.43/7.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.43/7.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.43/7.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.43/7.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.43/7.24  
% 15.43/7.27  tff(f_181, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 15.43/7.27  tff(f_99, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 15.43/7.27  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 15.43/7.27  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 15.43/7.27  tff(f_88, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 15.43/7.27  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 15.43/7.27  tff(f_152, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 15.43/7.27  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 15.43/7.27  tff(f_125, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 15.43/7.27  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 15.43/7.27  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 15.43/7.27  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 15.43/7.27  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 15.43/7.27  tff(f_129, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 15.43/7.27  tff(f_142, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 15.43/7.27  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 15.43/7.27  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 15.43/7.27  tff(c_88, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 15.43/7.27  tff(c_50681, plain, (![C_1322, A_1323, B_1324]: (v1_xboole_0(C_1322) | ~m1_subset_1(C_1322, k1_zfmisc_1(k2_zfmisc_1(A_1323, B_1324))) | ~v1_xboole_0(A_1323))), inference(cnfTransformation, [status(thm)], [f_99])).
% 15.43/7.27  tff(c_50707, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_88, c_50681])).
% 15.43/7.27  tff(c_50712, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_50707])).
% 15.43/7.27  tff(c_50532, plain, (![C_1304, A_1305, B_1306]: (v1_relat_1(C_1304) | ~m1_subset_1(C_1304, k1_zfmisc_1(k2_zfmisc_1(A_1305, B_1306))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.43/7.27  tff(c_50557, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_88, c_50532])).
% 15.43/7.27  tff(c_92, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 15.43/7.27  tff(c_86, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 15.43/7.27  tff(c_84, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_181])).
% 15.43/7.27  tff(c_51193, plain, (![A_1364, B_1365, C_1366]: (k2_relset_1(A_1364, B_1365, C_1366)=k2_relat_1(C_1366) | ~m1_subset_1(C_1366, k1_zfmisc_1(k2_zfmisc_1(A_1364, B_1365))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 15.43/7.27  tff(c_51208, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_88, c_51193])).
% 15.43/7.27  tff(c_51225, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_51208])).
% 15.43/7.27  tff(c_32, plain, (![A_18]: (k1_relat_1(k2_funct_1(A_18))=k2_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.43/7.27  tff(c_173, plain, (![A_64]: (v1_funct_1(k2_funct_1(A_64)) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_78])).
% 15.43/7.27  tff(c_82, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 15.43/7.27  tff(c_161, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_82])).
% 15.43/7.27  tff(c_176, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_173, c_161])).
% 15.43/7.27  tff(c_179, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_176])).
% 15.43/7.27  tff(c_263, plain, (![C_72, A_73, B_74]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.43/7.27  tff(c_272, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_88, c_263])).
% 15.43/7.27  tff(c_287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_179, c_272])).
% 15.43/7.27  tff(c_288, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_82])).
% 15.43/7.27  tff(c_300, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_288])).
% 15.43/7.27  tff(c_333, plain, (![C_87, A_88, B_89]: (v1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 15.43/7.27  tff(c_354, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_88, c_333])).
% 15.43/7.27  tff(c_1060, plain, (![A_145, B_146, C_147]: (k2_relset_1(A_145, B_146, C_147)=k2_relat_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 15.43/7.27  tff(c_1072, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_88, c_1060])).
% 15.43/7.27  tff(c_1088, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1072])).
% 15.43/7.27  tff(c_28, plain, (![A_17]: (v1_relat_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_78])).
% 15.43/7.27  tff(c_289, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_82])).
% 15.43/7.27  tff(c_789, plain, (![A_125]: (k1_relat_1(k2_funct_1(A_125))=k2_relat_1(A_125) | ~v2_funct_1(A_125) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125))), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.43/7.27  tff(c_72, plain, (![A_40]: (v1_funct_2(A_40, k1_relat_1(A_40), k2_relat_1(A_40)) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_152])).
% 15.43/7.27  tff(c_16892, plain, (![A_521]: (v1_funct_2(k2_funct_1(A_521), k2_relat_1(A_521), k2_relat_1(k2_funct_1(A_521))) | ~v1_funct_1(k2_funct_1(A_521)) | ~v1_relat_1(k2_funct_1(A_521)) | ~v2_funct_1(A_521) | ~v1_funct_1(A_521) | ~v1_relat_1(A_521))), inference(superposition, [status(thm), theory('equality')], [c_789, c_72])).
% 15.43/7.27  tff(c_16916, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1088, c_16892])).
% 15.43/7.27  tff(c_16944, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_354, c_92, c_86, c_289, c_16916])).
% 15.43/7.27  tff(c_16949, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_16944])).
% 15.43/7.27  tff(c_16952, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_16949])).
% 15.43/7.27  tff(c_16956, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_354, c_92, c_16952])).
% 15.43/7.27  tff(c_16958, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_16944])).
% 15.43/7.27  tff(c_90, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 15.43/7.27  tff(c_998, plain, (![A_139, B_140, C_141]: (k1_relset_1(A_139, B_140, C_141)=k1_relat_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 15.43/7.27  tff(c_1025, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_88, c_998])).
% 15.43/7.27  tff(c_2247, plain, (![B_219, A_220, C_221]: (k1_xboole_0=B_219 | k1_relset_1(A_220, B_219, C_221)=A_220 | ~v1_funct_2(C_221, A_220, B_219) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_220, B_219))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 15.43/7.27  tff(c_2265, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_88, c_2247])).
% 15.43/7.27  tff(c_2287, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1025, c_2265])).
% 15.43/7.27  tff(c_2291, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_2287])).
% 15.43/7.27  tff(c_30, plain, (![A_18]: (k2_relat_1(k2_funct_1(A_18))=k1_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.43/7.27  tff(c_869, plain, (![A_131]: (m1_subset_1(A_131, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_131), k2_relat_1(A_131)))) | ~v1_funct_1(A_131) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_152])).
% 15.43/7.27  tff(c_20129, plain, (![A_564]: (m1_subset_1(k2_funct_1(A_564), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_564)), k1_relat_1(A_564)))) | ~v1_funct_1(k2_funct_1(A_564)) | ~v1_relat_1(k2_funct_1(A_564)) | ~v2_funct_1(A_564) | ~v1_funct_1(A_564) | ~v1_relat_1(A_564))), inference(superposition, [status(thm), theory('equality')], [c_30, c_869])).
% 15.43/7.27  tff(c_20176, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2291, c_20129])).
% 15.43/7.27  tff(c_20217, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_354, c_92, c_86, c_16958, c_289, c_20176])).
% 15.43/7.27  tff(c_20254, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), '#skF_2'))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_32, c_20217])).
% 15.43/7.27  tff(c_20270, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_354, c_92, c_86, c_1088, c_20254])).
% 15.43/7.27  tff(c_20272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_300, c_20270])).
% 15.43/7.27  tff(c_20273, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2287])).
% 15.43/7.27  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 15.43/7.27  tff(c_20323, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20273, c_2])).
% 15.43/7.27  tff(c_10, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 15.43/7.27  tff(c_20321, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20273, c_20273, c_10])).
% 15.43/7.27  tff(c_70, plain, (![A_40]: (m1_subset_1(A_40, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_40), k2_relat_1(A_40)))) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_152])).
% 15.43/7.27  tff(c_1094, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1088, c_70])).
% 15.43/7.27  tff(c_1101, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_354, c_92, c_1094])).
% 15.43/7.27  tff(c_16, plain, (![B_9, A_7]: (v1_xboole_0(B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_7)) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.43/7.27  tff(c_1160, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_1101, c_16])).
% 15.43/7.27  tff(c_1188, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(splitLeft, [status(thm)], [c_1160])).
% 15.43/7.27  tff(c_20541, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20321, c_1188])).
% 15.43/7.27  tff(c_20548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20323, c_20541])).
% 15.43/7.27  tff(c_20549, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_1160])).
% 15.43/7.27  tff(c_290, plain, (![B_75, A_76]: (~v1_xboole_0(B_75) | B_75=A_76 | ~v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_36])).
% 15.43/7.27  tff(c_293, plain, (![A_76]: (k1_xboole_0=A_76 | ~v1_xboole_0(A_76))), inference(resolution, [status(thm)], [c_2, c_290])).
% 15.43/7.27  tff(c_20569, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_20549, c_293])).
% 15.43/7.27  tff(c_12, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 15.43/7.27  tff(c_302, plain, (![A_79]: (m1_subset_1(k6_partfun1(A_79), k1_zfmisc_1(k2_zfmisc_1(A_79, A_79))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 15.43/7.27  tff(c_306, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_302])).
% 15.43/7.27  tff(c_379, plain, (![B_92, A_93]: (v1_xboole_0(B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(A_93)) | ~v1_xboole_0(A_93))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.43/7.27  tff(c_391, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_306, c_379])).
% 15.43/7.27  tff(c_410, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_391])).
% 15.43/7.27  tff(c_420, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_410, c_293])).
% 15.43/7.27  tff(c_68, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_142])).
% 15.43/7.27  tff(c_20, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.43/7.27  tff(c_94, plain, (![A_13]: (k1_relat_1(k6_partfun1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_20])).
% 15.43/7.27  tff(c_440, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_420, c_94])).
% 15.43/7.27  tff(c_20589, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20569, c_20569, c_440])).
% 15.43/7.27  tff(c_36, plain, (![C_25, A_22, B_23]: (v1_xboole_0(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_99])).
% 15.43/7.27  tff(c_1156, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1101, c_36])).
% 15.43/7.27  tff(c_1183, plain, (~v1_xboole_0(k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1156])).
% 15.43/7.27  tff(c_20680, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20589, c_1183])).
% 15.43/7.27  tff(c_20683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20549, c_20680])).
% 15.43/7.27  tff(c_20684, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_1156])).
% 15.43/7.27  tff(c_20723, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_20684, c_293])).
% 15.43/7.27  tff(c_20755, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20723, c_20723, c_10])).
% 15.43/7.27  tff(c_22, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.43/7.27  tff(c_93, plain, (![A_13]: (k2_relat_1(k6_partfun1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_22])).
% 15.43/7.27  tff(c_434, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_420, c_93])).
% 15.43/7.27  tff(c_20746, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20723, c_20723, c_434])).
% 15.43/7.27  tff(c_20814, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20746, c_1088])).
% 15.43/7.27  tff(c_412, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_88, c_379])).
% 15.43/7.27  tff(c_450, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_412])).
% 15.43/7.27  tff(c_20834, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_20814, c_450])).
% 15.43/7.27  tff(c_21097, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20684, c_20755, c_20834])).
% 15.43/7.27  tff(c_21098, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_412])).
% 15.43/7.27  tff(c_21124, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_21098, c_293])).
% 15.43/7.27  tff(c_21136, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21124, c_21124, c_12])).
% 15.43/7.27  tff(c_21137, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21124, c_21124, c_10])).
% 15.43/7.27  tff(c_21099, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_412])).
% 15.43/7.27  tff(c_6, plain, (![B_3, A_2]: (~v1_xboole_0(B_3) | B_3=A_2 | ~v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 15.43/7.27  tff(c_21198, plain, (![A_593]: (A_593='#skF_4' | ~v1_xboole_0(A_593))), inference(resolution, [status(thm)], [c_21098, c_6])).
% 15.43/7.27  tff(c_21205, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_21099, c_21198])).
% 15.43/7.27  tff(c_8, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 15.43/7.27  tff(c_21968, plain, (![B_648, A_649]: (B_648='#skF_4' | A_649='#skF_4' | k2_zfmisc_1(A_649, B_648)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21124, c_21124, c_21124, c_8])).
% 15.43/7.27  tff(c_21978, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_21205, c_21968])).
% 15.43/7.27  tff(c_21983, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_21978])).
% 15.43/7.27  tff(c_21987, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_21983, c_300])).
% 15.43/7.27  tff(c_21992, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_21137, c_21987])).
% 15.43/7.27  tff(c_21126, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_21124, c_21124, c_434])).
% 15.43/7.27  tff(c_21506, plain, (![A_620]: (k1_relat_1(k2_funct_1(A_620))=k2_relat_1(A_620) | ~v2_funct_1(A_620) | ~v1_funct_1(A_620) | ~v1_relat_1(A_620))), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.43/7.27  tff(c_34209, plain, (![A_959]: (v1_funct_2(k2_funct_1(A_959), k2_relat_1(A_959), k2_relat_1(k2_funct_1(A_959))) | ~v1_funct_1(k2_funct_1(A_959)) | ~v1_relat_1(k2_funct_1(A_959)) | ~v2_funct_1(A_959) | ~v1_funct_1(A_959) | ~v1_relat_1(A_959))), inference(superposition, [status(thm), theory('equality')], [c_21506, c_72])).
% 15.43/7.27  tff(c_34236, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21126, c_34209])).
% 15.43/7.27  tff(c_34253, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_354, c_92, c_86, c_289, c_34236])).
% 15.43/7.27  tff(c_35404, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_34253])).
% 15.43/7.27  tff(c_35407, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_35404])).
% 15.43/7.27  tff(c_35411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_354, c_92, c_35407])).
% 15.43/7.27  tff(c_35413, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_34253])).
% 15.43/7.27  tff(c_21907, plain, (![A_644]: (m1_subset_1(A_644, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_644), k2_relat_1(A_644)))) | ~v1_funct_1(A_644) | ~v1_relat_1(A_644))), inference(cnfTransformation, [status(thm)], [f_152])).
% 15.43/7.27  tff(c_36955, plain, (![A_980]: (m1_subset_1(k2_funct_1(A_980), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_980), k2_relat_1(k2_funct_1(A_980))))) | ~v1_funct_1(k2_funct_1(A_980)) | ~v1_relat_1(k2_funct_1(A_980)) | ~v2_funct_1(A_980) | ~v1_funct_1(A_980) | ~v1_relat_1(A_980))), inference(superposition, [status(thm), theory('equality')], [c_32, c_21907])).
% 15.43/7.27  tff(c_37011, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21126, c_36955])).
% 15.43/7.27  tff(c_37039, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_354, c_92, c_86, c_35413, c_289, c_21136, c_37011])).
% 15.43/7.27  tff(c_37041, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21992, c_37039])).
% 15.43/7.27  tff(c_37042, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_21978])).
% 15.43/7.27  tff(c_37047, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_37042, c_300])).
% 15.43/7.27  tff(c_37052, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_21136, c_37047])).
% 15.43/7.27  tff(c_21168, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_21124, c_21124, c_440])).
% 15.43/7.27  tff(c_21472, plain, (![A_615]: (k2_relat_1(k2_funct_1(A_615))=k1_relat_1(A_615) | ~v2_funct_1(A_615) | ~v1_funct_1(A_615) | ~v1_relat_1(A_615))), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.43/7.27  tff(c_47751, plain, (![A_1268]: (v1_funct_2(k2_funct_1(A_1268), k1_relat_1(k2_funct_1(A_1268)), k1_relat_1(A_1268)) | ~v1_funct_1(k2_funct_1(A_1268)) | ~v1_relat_1(k2_funct_1(A_1268)) | ~v2_funct_1(A_1268) | ~v1_funct_1(A_1268) | ~v1_relat_1(A_1268))), inference(superposition, [status(thm), theory('equality')], [c_21472, c_72])).
% 15.43/7.27  tff(c_47778, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21168, c_47751])).
% 15.43/7.27  tff(c_47795, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_354, c_92, c_86, c_289, c_47778])).
% 15.43/7.27  tff(c_47798, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_47795])).
% 15.43/7.27  tff(c_47801, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_47798])).
% 15.43/7.27  tff(c_47805, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_354, c_92, c_47801])).
% 15.43/7.27  tff(c_47807, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_47795])).
% 15.43/7.27  tff(c_50282, plain, (![A_1288]: (m1_subset_1(k2_funct_1(A_1288), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1288)), k1_relat_1(A_1288)))) | ~v1_funct_1(k2_funct_1(A_1288)) | ~v1_relat_1(k2_funct_1(A_1288)) | ~v2_funct_1(A_1288) | ~v1_funct_1(A_1288) | ~v1_relat_1(A_1288))), inference(superposition, [status(thm), theory('equality')], [c_30, c_21907])).
% 15.43/7.27  tff(c_50338, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21168, c_50282])).
% 15.43/7.27  tff(c_50366, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_354, c_92, c_86, c_47807, c_289, c_21137, c_50338])).
% 15.43/7.27  tff(c_50368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37052, c_50366])).
% 15.43/7.27  tff(c_50369, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_288])).
% 15.43/7.27  tff(c_50370, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_288])).
% 15.43/7.27  tff(c_51305, plain, (![A_1370, B_1371, C_1372]: (k1_relset_1(A_1370, B_1371, C_1372)=k1_relat_1(C_1372) | ~m1_subset_1(C_1372, k1_zfmisc_1(k2_zfmisc_1(A_1370, B_1371))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 15.43/7.27  tff(c_51337, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_50370, c_51305])).
% 15.43/7.27  tff(c_52480, plain, (![B_1438, C_1439, A_1440]: (k1_xboole_0=B_1438 | v1_funct_2(C_1439, A_1440, B_1438) | k1_relset_1(A_1440, B_1438, C_1439)!=A_1440 | ~m1_subset_1(C_1439, k1_zfmisc_1(k2_zfmisc_1(A_1440, B_1438))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 15.43/7.27  tff(c_52492, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_50370, c_52480])).
% 15.43/7.27  tff(c_52514, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_51337, c_52492])).
% 15.43/7.27  tff(c_52515, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_50369, c_52514])).
% 15.43/7.27  tff(c_52525, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_52515])).
% 15.43/7.27  tff(c_52528, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_32, c_52525])).
% 15.43/7.27  tff(c_52531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50557, c_92, c_86, c_51225, c_52528])).
% 15.43/7.27  tff(c_52532, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_52515])).
% 15.43/7.27  tff(c_52583, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52532, c_2])).
% 15.43/7.27  tff(c_52585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50712, c_52583])).
% 15.43/7.27  tff(c_52586, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_50707])).
% 15.43/7.27  tff(c_52593, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_52586, c_293])).
% 15.43/7.27  tff(c_52620, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52593, c_52593, c_10])).
% 15.43/7.27  tff(c_52587, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_50707])).
% 15.43/7.27  tff(c_52600, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_52587, c_293])).
% 15.43/7.27  tff(c_52630, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52593, c_52600])).
% 15.43/7.27  tff(c_50391, plain, (![B_1295, A_1296]: (v1_xboole_0(B_1295) | ~m1_subset_1(B_1295, k1_zfmisc_1(A_1296)) | ~v1_xboole_0(A_1296))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.43/7.27  tff(c_50417, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_50370, c_50391])).
% 15.43/7.27  tff(c_50507, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_50417])).
% 15.43/7.27  tff(c_52633, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52630, c_50507])).
% 15.43/7.27  tff(c_52825, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52586, c_52620, c_52633])).
% 15.43/7.27  tff(c_52827, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_50417])).
% 15.43/7.27  tff(c_52872, plain, (k2_zfmisc_1('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_52827, c_293])).
% 15.43/7.27  tff(c_52910, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_52872, c_8])).
% 15.43/7.27  tff(c_52912, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_52910])).
% 15.43/7.27  tff(c_52953, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52912, c_2])).
% 15.43/7.27  tff(c_52951, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52912, c_52912, c_10])).
% 15.43/7.27  tff(c_50422, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_88, c_50391])).
% 15.43/7.27  tff(c_50457, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_50422])).
% 15.43/7.27  tff(c_53108, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52951, c_50457])).
% 15.43/7.27  tff(c_53112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52953, c_53108])).
% 15.43/7.27  tff(c_53113, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_52910])).
% 15.43/7.27  tff(c_53134, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_53113, c_2])).
% 15.43/7.27  tff(c_53131, plain, (![B_5]: (k2_zfmisc_1('#skF_2', B_5)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_53113, c_53113, c_12])).
% 15.43/7.27  tff(c_53222, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_53131, c_50457])).
% 15.43/7.27  tff(c_53226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53134, c_53222])).
% 15.43/7.27  tff(c_53227, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_50422])).
% 15.43/7.27  tff(c_53234, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_53227, c_293])).
% 15.43/7.27  tff(c_50371, plain, (![A_1289]: (m1_subset_1(k6_partfun1(A_1289), k1_zfmisc_1(k2_zfmisc_1(A_1289, A_1289))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 15.43/7.27  tff(c_50375, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_50371])).
% 15.43/7.27  tff(c_50403, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_50375, c_50391])).
% 15.43/7.27  tff(c_50420, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_50403])).
% 15.43/7.27  tff(c_50430, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_50420, c_293])).
% 15.43/7.27  tff(c_53249, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_53234, c_53234, c_50430])).
% 15.43/7.27  tff(c_53276, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_53249, c_94])).
% 15.43/7.27  tff(c_14, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 15.43/7.27  tff(c_53253, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_53234, c_14])).
% 15.43/7.27  tff(c_55540, plain, (![A_1639, B_1640, C_1641]: (k1_relset_1(A_1639, B_1640, C_1641)=k1_relat_1(C_1641) | ~m1_subset_1(C_1641, k1_zfmisc_1(k2_zfmisc_1(A_1639, B_1640))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 15.43/7.27  tff(c_55550, plain, (![A_1639, B_1640]: (k1_relset_1(A_1639, B_1640, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_53253, c_55540])).
% 15.43/7.27  tff(c_55562, plain, (![A_1639, B_1640]: (k1_relset_1(A_1639, B_1640, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_53276, c_55550])).
% 15.43/7.27  tff(c_46, plain, (![C_34, B_33]: (v1_funct_2(C_34, k1_xboole_0, B_33) | k1_relset_1(k1_xboole_0, B_33, C_34)!=k1_xboole_0 | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_33))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 15.43/7.27  tff(c_97, plain, (![C_34, B_33]: (v1_funct_2(C_34, k1_xboole_0, B_33) | k1_relset_1(k1_xboole_0, B_33, C_34)!=k1_xboole_0 | ~m1_subset_1(C_34, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_46])).
% 15.43/7.27  tff(c_56320, plain, (![C_1683, B_1684]: (v1_funct_2(C_1683, '#skF_4', B_1684) | k1_relset_1('#skF_4', B_1684, C_1683)!='#skF_4' | ~m1_subset_1(C_1683, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_53234, c_53234, c_53234, c_53234, c_97])).
% 15.43/7.27  tff(c_56325, plain, (![B_1684]: (v1_funct_2('#skF_4', '#skF_4', B_1684) | k1_relset_1('#skF_4', B_1684, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_53253, c_56320])).
% 15.43/7.27  tff(c_56329, plain, (![B_1684]: (v1_funct_2('#skF_4', '#skF_4', B_1684))), inference(demodulation, [status(thm), theory('equality')], [c_55562, c_56325])).
% 15.43/7.27  tff(c_50442, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_50430, c_93])).
% 15.43/7.27  tff(c_53248, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_53234, c_53234, c_50442])).
% 15.43/7.27  tff(c_54489, plain, (![A_1558, B_1559, C_1560]: (k2_relset_1(A_1558, B_1559, C_1560)=k2_relat_1(C_1560) | ~m1_subset_1(C_1560, k1_zfmisc_1(k2_zfmisc_1(A_1558, B_1559))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 15.43/7.27  tff(c_54502, plain, (![A_1558, B_1559]: (k2_relset_1(A_1558, B_1559, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_53253, c_54489])).
% 15.43/7.27  tff(c_54513, plain, (![A_1558, B_1559]: (k2_relset_1(A_1558, B_1559, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_53248, c_54502])).
% 15.43/7.27  tff(c_54517, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54513, c_84])).
% 15.43/7.27  tff(c_53451, plain, (![C_1490, A_1491, B_1492]: (v1_xboole_0(C_1490) | ~m1_subset_1(C_1490, k1_zfmisc_1(k2_zfmisc_1(A_1491, B_1492))) | ~v1_xboole_0(A_1491))), inference(cnfTransformation, [status(thm)], [f_99])).
% 15.43/7.27  tff(c_53479, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_50370, c_53451])).
% 15.43/7.27  tff(c_53481, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_53479])).
% 15.43/7.27  tff(c_54529, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54517, c_53481])).
% 15.43/7.27  tff(c_54537, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53227, c_54529])).
% 15.43/7.27  tff(c_54538, plain, (v1_xboole_0(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_53479])).
% 15.43/7.27  tff(c_53235, plain, (![A_2]: (A_2='#skF_4' | ~v1_xboole_0(A_2))), inference(resolution, [status(thm)], [c_53227, c_6])).
% 15.43/7.27  tff(c_54620, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_54538, c_53235])).
% 15.43/7.27  tff(c_54539, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_53479])).
% 15.43/7.27  tff(c_54545, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_54539, c_53235])).
% 15.43/7.27  tff(c_54595, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54545, c_50369])).
% 15.43/7.27  tff(c_54675, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54620, c_54595])).
% 15.43/7.27  tff(c_56333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56329, c_54675])).
% 15.43/7.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.43/7.27  
% 15.43/7.27  Inference rules
% 15.43/7.27  ----------------------
% 15.43/7.27  #Ref     : 0
% 15.43/7.27  #Sup     : 14636
% 15.43/7.27  #Fact    : 0
% 15.43/7.27  #Define  : 0
% 15.43/7.27  #Split   : 48
% 15.43/7.27  #Chain   : 0
% 15.43/7.27  #Close   : 0
% 15.43/7.27  
% 15.43/7.27  Ordering : KBO
% 15.43/7.27  
% 15.43/7.27  Simplification rules
% 15.43/7.27  ----------------------
% 15.43/7.27  #Subsume      : 3257
% 15.43/7.27  #Demod        : 16032
% 15.43/7.27  #Tautology    : 6864
% 15.43/7.27  #SimpNegUnit  : 82
% 15.43/7.27  #BackRed      : 421
% 15.43/7.27  
% 15.43/7.27  #Partial instantiations: 0
% 15.43/7.27  #Strategies tried      : 1
% 15.43/7.27  
% 15.43/7.27  Timing (in seconds)
% 15.43/7.27  ----------------------
% 15.43/7.28  Preprocessing        : 0.38
% 15.43/7.28  Parsing              : 0.20
% 15.43/7.28  CNF conversion       : 0.02
% 15.43/7.28  Main loop            : 6.03
% 15.43/7.28  Inferencing          : 1.32
% 15.43/7.28  Reduction            : 2.07
% 15.43/7.28  Demodulation         : 1.61
% 15.43/7.28  BG Simplification    : 0.15
% 15.43/7.28  Subsumption          : 2.13
% 15.43/7.28  Abstraction          : 0.23
% 15.43/7.28  MUC search           : 0.00
% 15.43/7.28  Cooper               : 0.00
% 15.43/7.28  Total                : 6.49
% 15.43/7.28  Index Insertion      : 0.00
% 15.43/7.28  Index Deletion       : 0.00
% 15.43/7.28  Index Matching       : 0.00
% 15.43/7.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
