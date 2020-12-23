%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:34 EST 2020

% Result     : Theorem 12.47s
% Output     : CNFRefutation 12.53s
% Verified   : 
% Statistics : Number of formulae       :  295 (2848 expanded)
%              Number of leaves         :   47 ( 958 expanded)
%              Depth                    :   21
%              Number of atoms          :  508 (7727 expanded)
%              Number of equality atoms :  157 (1626 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_180,negated_conjecture,(
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

tff(f_102,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_163,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_142,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_funct_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_82,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_30196,plain,(
    ! [C_1039,A_1040,B_1041] :
      ( v1_xboole_0(C_1039)
      | ~ m1_subset_1(C_1039,k1_zfmisc_1(k2_zfmisc_1(A_1040,B_1041)))
      | ~ v1_xboole_0(A_1040) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_30222,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_30196])).

tff(c_30227,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_30222])).

tff(c_227,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_243,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_227])).

tff(c_86,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_80,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_78,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_30703,plain,(
    ! [A_1075,B_1076,C_1077] :
      ( k2_relset_1(A_1075,B_1076,C_1077) = k2_relat_1(C_1077)
      | ~ m1_subset_1(C_1077,k1_zfmisc_1(k2_zfmisc_1(A_1075,B_1076))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_30718,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_30703])).

tff(c_30734,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_30718])).

tff(c_30,plain,(
    ! [A_17] :
      ( k1_relat_1(k2_funct_1(A_17)) = k2_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_22,plain,(
    ! [A_14] :
      ( v1_funct_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_76,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_137,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_140,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_137])).

tff(c_143,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_140])).

tff(c_181,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_190,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_181])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_190])).

tff(c_206,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_245,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_591,plain,(
    ! [A_115,B_116,C_117] :
      ( k2_relset_1(A_115,B_116,C_117) = k2_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_600,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_591])).

tff(c_614,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_600])).

tff(c_24,plain,(
    ! [A_14] :
      ( v1_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_519,plain,(
    ! [A_111] :
      ( k1_relat_1(k2_funct_1(A_111)) = k2_relat_1(A_111)
      | ~ v2_funct_1(A_111)
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_16,plain,(
    ! [A_9] :
      ( k9_relat_1(A_9,k1_relat_1(A_9)) = k2_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12671,plain,(
    ! [A_443] :
      ( k9_relat_1(k2_funct_1(A_443),k2_relat_1(A_443)) = k2_relat_1(k2_funct_1(A_443))
      | ~ v1_relat_1(k2_funct_1(A_443))
      | ~ v2_funct_1(A_443)
      | ~ v1_funct_1(A_443)
      | ~ v1_relat_1(A_443) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_16])).

tff(c_12714,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_12671])).

tff(c_12739,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_86,c_80,c_12714])).

tff(c_12740,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_12739])).

tff(c_12743,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_12740])).

tff(c_12747,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_86,c_12743])).

tff(c_12749,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_12739])).

tff(c_207,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_84,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_673,plain,(
    ! [A_120,B_121,C_122] :
      ( k1_relset_1(A_120,B_121,C_122) = k1_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_695,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_673])).

tff(c_1704,plain,(
    ! [B_197,A_198,C_199] :
      ( k1_xboole_0 = B_197
      | k1_relset_1(A_198,B_197,C_199) = A_198
      | ~ v1_funct_2(C_199,A_198,B_197)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_198,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1719,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_1704])).

tff(c_1739,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_695,c_1719])).

tff(c_1743,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1739])).

tff(c_18,plain,(
    ! [A_10] :
      ( k10_relat_1(A_10,k2_relat_1(A_10)) = k1_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_622,plain,
    ( k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_18])).

tff(c_628,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_622])).

tff(c_1750,plain,(
    k10_relat_1('#skF_4','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1743,c_628])).

tff(c_12748,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_12739])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( k9_relat_1(k2_funct_1(B_16),A_15) = k10_relat_1(B_16,A_15)
      | ~ v2_funct_1(B_16)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_12753,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k10_relat_1('#skF_4','#skF_3')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12748,c_26])).

tff(c_12760,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_86,c_80,c_1750,c_12753])).

tff(c_70,plain,(
    ! [A_41] :
      ( m1_subset_1(A_41,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_41),k2_relat_1(A_41))))
      | ~ v1_funct_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_12780,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12760,c_70])).

tff(c_12804,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12749,c_207,c_12780])).

tff(c_12963,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'),'#skF_2')))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_12804])).

tff(c_12982,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_86,c_80,c_614,c_12963])).

tff(c_12984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_245,c_12982])).

tff(c_12985,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1739])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_13026,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12985,c_12985,c_8])).

tff(c_13115,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13026,c_82])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_392,plain,(
    ! [C_100,A_101,B_102] :
      ( v1_xboole_0(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ v1_xboole_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_407,plain,(
    ! [C_100] :
      ( v1_xboole_0(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_392])).

tff(c_416,plain,(
    ! [C_100] :
      ( v1_xboole_0(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_407])).

tff(c_13368,plain,(
    ! [C_463] :
      ( v1_xboole_0(C_463)
      | ~ m1_subset_1(C_463,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12985,c_416])).

tff(c_13376,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_13115,c_13368])).

tff(c_125,plain,(
    ! [B_55,A_56] :
      ( ~ v1_xboole_0(B_55)
      | B_55 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_128,plain,(
    ! [A_56] :
      ( k1_xboole_0 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_2,c_125])).

tff(c_13024,plain,(
    ! [A_56] :
      ( A_56 = '#skF_3'
      | ~ v1_xboole_0(A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12985,c_128])).

tff(c_13398,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_13376,c_13024])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_696,plain,(
    ! [A_120,B_121] : k1_relset_1(A_120,B_121,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_673])).

tff(c_48,plain,(
    ! [C_36,B_35] :
      ( v1_funct_2(C_36,k1_xboole_0,B_35)
      | k1_relset_1(k1_xboole_0,B_35,C_36) != k1_xboole_0
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1346,plain,(
    ! [C_169,B_170] :
      ( v1_funct_2(C_169,k1_xboole_0,B_170)
      | k1_relset_1(k1_xboole_0,B_170,C_169) != k1_xboole_0
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_48])).

tff(c_1349,plain,(
    ! [B_170] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_170)
      | k1_relset_1(k1_xboole_0,B_170,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_1346])).

tff(c_1351,plain,(
    ! [B_170] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_170)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_1349])).

tff(c_1352,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1351])).

tff(c_58,plain,(
    ! [A_37] : m1_subset_1(k6_partfun1(A_37),k1_zfmisc_1(k2_zfmisc_1(A_37,A_37))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_421,plain,(
    ! [A_104] :
      ( v1_xboole_0(k6_partfun1(A_104))
      | ~ v1_xboole_0(A_104) ) ),
    inference(resolution,[status(thm)],[c_58,c_392])).

tff(c_429,plain,(
    ! [A_105] :
      ( k6_partfun1(A_105) = k1_xboole_0
      | ~ v1_xboole_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_421,c_128])).

tff(c_437,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_429])).

tff(c_56,plain,(
    ! [A_37] : v1_partfun1(k6_partfun1(A_37),A_37) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_471,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_56])).

tff(c_244,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_227])).

tff(c_208,plain,(
    ! [A_70] : m1_subset_1(k6_partfun1(A_70),k1_zfmisc_1(k2_zfmisc_1(A_70,A_70))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_212,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_208])).

tff(c_303,plain,(
    ! [B_84,A_85] :
      ( v1_funct_1(B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_85))
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_315,plain,
    ( v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_212,c_303])).

tff(c_335,plain,
    ( v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_315])).

tff(c_340,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_335])).

tff(c_339,plain,(
    ! [A_5] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_303])).

tff(c_342,plain,(
    ! [A_86] :
      ( ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(negUnitSimplification,[status(thm)],[c_340,c_339])).

tff(c_351,plain,(
    ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_243,c_342])).

tff(c_360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_351])).

tff(c_362,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_1359,plain,(
    ! [C_173,A_174,B_175] :
      ( v1_funct_2(C_173,A_174,B_175)
      | ~ v1_partfun1(C_173,A_174)
      | ~ v1_funct_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1384,plain,(
    ! [A_174,B_175] :
      ( v1_funct_2(k1_xboole_0,A_174,B_175)
      | ~ v1_partfun1(k1_xboole_0,A_174)
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_1359])).

tff(c_1401,plain,(
    ! [A_176,B_177] :
      ( v1_funct_2(k1_xboole_0,A_176,B_177)
      | ~ v1_partfun1(k1_xboole_0,A_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_1384])).

tff(c_52,plain,(
    ! [B_35,C_36] :
      ( k1_relset_1(k1_xboole_0,B_35,C_36) = k1_xboole_0
      | ~ v1_funct_2(C_36,k1_xboole_0,B_35)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_90,plain,(
    ! [B_35,C_36] :
      ( k1_relset_1(k1_xboole_0,B_35,C_36) = k1_xboole_0
      | ~ v1_funct_2(C_36,k1_xboole_0,B_35)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_52])).

tff(c_1404,plain,(
    ! [B_177] :
      ( k1_relset_1(k1_xboole_0,B_177,k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_partfun1(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1401,c_90])).

tff(c_1410,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_12,c_696,c_1404])).

tff(c_1412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1352,c_1410])).

tff(c_1414,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1351])).

tff(c_12997,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12985,c_12985,c_1414])).

tff(c_13426,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13398,c_13398,c_12997])).

tff(c_734,plain,(
    ! [A_129] :
      ( m1_subset_1(A_129,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_129),k2_relat_1(A_129))))
      | ~ v1_funct_1(A_129)
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_754,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_734])).

tff(c_768,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_86,c_754])).

tff(c_34,plain,(
    ! [C_24,A_21,B_22] :
      ( v1_xboole_0(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_837,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_768,c_34])).

tff(c_843,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_837])).

tff(c_13486,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13426,c_843])).

tff(c_13489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13376,c_13486])).

tff(c_13490,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_837])).

tff(c_13511,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_13490,c_128])).

tff(c_13535,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13511,c_13511,c_10])).

tff(c_13491,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_837])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_13647,plain,(
    ! [A_473] :
      ( A_473 = '#skF_4'
      | ~ v1_xboole_0(A_473) ) ),
    inference(resolution,[status(thm)],[c_13490,c_4])).

tff(c_13660,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_13491,c_13647])).

tff(c_13517,plain,(
    ! [A_120,B_121] : k1_relset_1(A_120,B_121,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13511,c_13511,c_696])).

tff(c_13871,plain,(
    ! [A_120,B_121] : k1_relset_1(A_120,B_121,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13660,c_13517])).

tff(c_13536,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13511,c_12])).

tff(c_54,plain,(
    ! [B_35,A_34,C_36] :
      ( k1_xboole_0 = B_35
      | k1_relset_1(A_34,B_35,C_36) = A_34
      | ~ v1_funct_2(C_36,A_34,B_35)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_13988,plain,(
    ! [B_499,A_500,C_501] :
      ( B_499 = '#skF_4'
      | k1_relset_1(A_500,B_499,C_501) = A_500
      | ~ v1_funct_2(C_501,A_500,B_499)
      | ~ m1_subset_1(C_501,k1_zfmisc_1(k2_zfmisc_1(A_500,B_499))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13511,c_54])).

tff(c_13995,plain,(
    ! [B_499,A_500] :
      ( B_499 = '#skF_4'
      | k1_relset_1(A_500,B_499,'#skF_4') = A_500
      | ~ v1_funct_2('#skF_4',A_500,B_499) ) ),
    inference(resolution,[status(thm)],[c_13536,c_13988])).

tff(c_14549,plain,(
    ! [B_539,A_540] :
      ( B_539 = '#skF_4'
      | A_540 = '#skF_4'
      | ~ v1_funct_2('#skF_4',A_540,B_539) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13871,c_13995])).

tff(c_14583,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_84,c_14549])).

tff(c_14584,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14583])).

tff(c_414,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_392])).

tff(c_419,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_414])).

tff(c_14585,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14584,c_419])).

tff(c_14590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13490,c_14585])).

tff(c_14591,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14583])).

tff(c_14600,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14591,c_245])).

tff(c_14603,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13535,c_14600])).

tff(c_438,plain,(
    ! [A_106] :
      ( k2_relat_1(k2_funct_1(A_106)) = k1_relat_1(A_106)
      | ~ v2_funct_1(A_106)
      | ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_19346,plain,(
    ! [A_685] :
      ( k10_relat_1(k2_funct_1(A_685),k1_relat_1(A_685)) = k1_relat_1(k2_funct_1(A_685))
      | ~ v1_relat_1(k2_funct_1(A_685))
      | ~ v2_funct_1(A_685)
      | ~ v1_funct_1(A_685)
      | ~ v1_relat_1(A_685) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_18])).

tff(c_19376,plain,
    ( k10_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13660,c_19346])).

tff(c_19397,plain,
    ( k10_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_86,c_80,c_19376])).

tff(c_19800,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_19397])).

tff(c_19803,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_19800])).

tff(c_19807,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_86,c_19803])).

tff(c_19809,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_19397])).

tff(c_13534,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13511,c_13511,c_8])).

tff(c_13669,plain,(
    k10_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13660,c_628])).

tff(c_14597,plain,(
    k10_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14591,c_13669])).

tff(c_14599,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14591,c_614])).

tff(c_20936,plain,(
    ! [A_711] :
      ( k9_relat_1(k2_funct_1(A_711),k2_relat_1(A_711)) = k2_relat_1(k2_funct_1(A_711))
      | ~ v1_relat_1(k2_funct_1(A_711))
      | ~ v2_funct_1(A_711)
      | ~ v1_funct_1(A_711)
      | ~ v1_relat_1(A_711) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_16])).

tff(c_20975,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_14599,c_20936])).

tff(c_21004,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k2_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_86,c_80,c_19809,c_20975])).

tff(c_21008,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k10_relat_1('#skF_4','#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_21004,c_26])).

tff(c_21015,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_86,c_80,c_14597,c_21008])).

tff(c_21035,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21015,c_70])).

tff(c_21059,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19809,c_207,c_13534,c_21035])).

tff(c_21061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14603,c_21059])).

tff(c_21062,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_414])).

tff(c_21069,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_21062,c_128])).

tff(c_21092,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21069,c_21069,c_8])).

tff(c_21063,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_414])).

tff(c_21076,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_21063,c_128])).

tff(c_21103,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21069,c_21076])).

tff(c_21106,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21103,c_245])).

tff(c_21461,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21092,c_21106])).

tff(c_21094,plain,(
    ! [A_5] : m1_subset_1('#skF_4',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21069,c_12])).

tff(c_21558,plain,(
    ! [A_746,B_747,C_748] :
      ( k2_relset_1(A_746,B_747,C_748) = k2_relat_1(C_748)
      | ~ m1_subset_1(C_748,k1_zfmisc_1(k2_zfmisc_1(A_746,B_747))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_21582,plain,(
    ! [A_749,B_750] : k2_relset_1(A_749,B_750,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_21094,c_21558])).

tff(c_21108,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21103,c_78])).

tff(c_21586,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_21582,c_21108])).

tff(c_21312,plain,(
    ! [A_725] :
      ( k1_relat_1(k2_funct_1(A_725)) = k2_relat_1(A_725)
      | ~ v2_funct_1(A_725)
      | ~ v1_funct_1(A_725)
      | ~ v1_relat_1(A_725) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_29892,plain,(
    ! [A_1011] :
      ( k9_relat_1(k2_funct_1(A_1011),k2_relat_1(A_1011)) = k2_relat_1(k2_funct_1(A_1011))
      | ~ v1_relat_1(k2_funct_1(A_1011))
      | ~ v2_funct_1(A_1011)
      | ~ v1_funct_1(A_1011)
      | ~ v1_relat_1(A_1011) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21312,c_16])).

tff(c_29938,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_21586,c_29892])).

tff(c_29965,plain,
    ( k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_86,c_80,c_29938])).

tff(c_29966,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_29965])).

tff(c_29969,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_29966])).

tff(c_29973,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_86,c_29969])).

tff(c_29975,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_29965])).

tff(c_21670,plain,(
    ! [A_755,B_756,C_757] :
      ( k1_relset_1(A_755,B_756,C_757) = k1_relat_1(C_757)
      | ~ m1_subset_1(C_757,k1_zfmisc_1(k2_zfmisc_1(A_755,B_756))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_21691,plain,(
    ! [A_755,B_756] : k1_relset_1(A_755,B_756,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_21094,c_21670])).

tff(c_89,plain,(
    ! [C_36,B_35] :
      ( v1_funct_2(C_36,k1_xboole_0,B_35)
      | k1_relset_1(k1_xboole_0,B_35,C_36) != k1_xboole_0
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_48])).

tff(c_21934,plain,(
    ! [C_773,B_774] :
      ( v1_funct_2(C_773,'#skF_4',B_774)
      | k1_relset_1('#skF_4',B_774,C_773) != '#skF_4'
      | ~ m1_subset_1(C_773,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21069,c_21069,c_21069,c_21069,c_89])).

tff(c_21937,plain,(
    ! [B_774] :
      ( v1_funct_2('#skF_4','#skF_4',B_774)
      | k1_relset_1('#skF_4',B_774,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_21094,c_21934])).

tff(c_21939,plain,(
    ! [B_774] :
      ( v1_funct_2('#skF_4','#skF_4',B_774)
      | k1_relat_1('#skF_4') != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21691,c_21937])).

tff(c_21940,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_21939])).

tff(c_21109,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21103,c_84])).

tff(c_22192,plain,(
    ! [B_797,C_798] :
      ( k1_relset_1('#skF_4',B_797,C_798) = '#skF_4'
      | ~ v1_funct_2(C_798,'#skF_4',B_797)
      | ~ m1_subset_1(C_798,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21069,c_21069,c_21069,c_21069,c_90])).

tff(c_22197,plain,
    ( k1_relset_1('#skF_4','#skF_3','#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_21109,c_22192])).

tff(c_22205,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21094,c_21691,c_22197])).

tff(c_22207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21940,c_22205])).

tff(c_22209,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_21939])).

tff(c_21603,plain,
    ( k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_21586,c_18])).

tff(c_21611,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_21603])).

tff(c_22211,plain,(
    k10_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22209,c_21611])).

tff(c_29974,plain,(
    k9_relat_1(k2_funct_1('#skF_4'),'#skF_3') = k2_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_29965])).

tff(c_29979,plain,
    ( k2_relat_1(k2_funct_1('#skF_4')) = k10_relat_1('#skF_4','#skF_3')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_29974,c_26])).

tff(c_29986,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_86,c_80,c_22211,c_29979])).

tff(c_30006,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_29986,c_70])).

tff(c_30030,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29975,c_207,c_21092,c_30006])).

tff(c_30032,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21461,c_30030])).

tff(c_30033,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_30034,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_30523,plain,(
    ! [A_1061,B_1062,C_1063] :
      ( k1_relset_1(A_1061,B_1062,C_1063) = k1_relat_1(C_1063)
      | ~ m1_subset_1(C_1063,k1_zfmisc_1(k2_zfmisc_1(A_1061,B_1062))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_30551,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_30034,c_30523])).

tff(c_31737,plain,(
    ! [B_1148,C_1149,A_1150] :
      ( k1_xboole_0 = B_1148
      | v1_funct_2(C_1149,A_1150,B_1148)
      | k1_relset_1(A_1150,B_1148,C_1149) != A_1150
      | ~ m1_subset_1(C_1149,k1_zfmisc_1(k2_zfmisc_1(A_1150,B_1148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_31749,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_30034,c_31737])).

tff(c_31772,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30551,c_31749])).

tff(c_31773,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_30033,c_31772])).

tff(c_31781,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_31773])).

tff(c_31784,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_31781])).

tff(c_31787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_86,c_80,c_30734,c_31784])).

tff(c_31788,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_31773])).

tff(c_31829,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31788,c_2])).

tff(c_31831,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30227,c_31829])).

tff(c_31832,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_30222])).

tff(c_31839,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_31832,c_128])).

tff(c_44,plain,(
    ! [A_34] :
      ( v1_funct_2(k1_xboole_0,A_34,k1_xboole_0)
      | k1_xboole_0 = A_34
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_34,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_88,plain,(
    ! [A_34] :
      ( v1_funct_2(k1_xboole_0,A_34,k1_xboole_0)
      | k1_xboole_0 = A_34 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_44])).

tff(c_31861,plain,(
    ! [A_34] :
      ( v1_funct_2('#skF_4',A_34,'#skF_4')
      | A_34 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31839,c_31839,c_31839,c_88])).

tff(c_31862,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31839,c_31839,c_8])).

tff(c_31833,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_30222])).

tff(c_31846,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_31833,c_128])).

tff(c_31873,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31839,c_31846])).

tff(c_31877,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31873,c_30034])).

tff(c_32194,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31862,c_31877])).

tff(c_30214,plain,(
    ! [C_1039] :
      ( v1_xboole_0(C_1039)
      | ~ m1_subset_1(C_1039,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_30196])).

tff(c_30224,plain,(
    ! [C_1039] :
      ( v1_xboole_0(C_1039)
      | ~ m1_subset_1(C_1039,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30214])).

tff(c_32073,plain,(
    ! [C_1039] :
      ( v1_xboole_0(C_1039)
      | ~ m1_subset_1(C_1039,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31839,c_30224])).

tff(c_32208,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_32194,c_32073])).

tff(c_31840,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_31832,c_4])).

tff(c_32222,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32208,c_31840])).

tff(c_31878,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31873,c_30033])).

tff(c_32226,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32222,c_31878])).

tff(c_32277,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_31861,c_32226])).

tff(c_30220,plain,
    ( v1_xboole_0(k2_funct_1('#skF_4'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30034,c_30196])).

tff(c_31982,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30220])).

tff(c_32299,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32277,c_31982])).

tff(c_32304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31832,c_32299])).

tff(c_32306,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_30220])).

tff(c_32312,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32306,c_31840])).

tff(c_31881,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31873,c_84])).

tff(c_32316,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32312,c_31881])).

tff(c_32305,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_30220])).

tff(c_32328,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32305,c_31840])).

tff(c_32400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32316,c_32328,c_32312,c_31878])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:28:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.47/4.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.53/4.68  
% 12.53/4.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.53/4.68  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 12.53/4.68  
% 12.53/4.68  %Foreground sorts:
% 12.53/4.68  
% 12.53/4.68  
% 12.53/4.68  %Background operators:
% 12.53/4.68  
% 12.53/4.68  
% 12.53/4.68  %Foreground operators:
% 12.53/4.68  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.53/4.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.53/4.68  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 12.53/4.68  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 12.53/4.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.53/4.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.53/4.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.53/4.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.53/4.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.53/4.68  tff('#skF_2', type, '#skF_2': $i).
% 12.53/4.68  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.53/4.68  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 12.53/4.68  tff('#skF_3', type, '#skF_3': $i).
% 12.53/4.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.53/4.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.53/4.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.53/4.68  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 12.53/4.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.53/4.68  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 12.53/4.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.53/4.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.53/4.68  tff('#skF_4', type, '#skF_4': $i).
% 12.53/4.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.53/4.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.53/4.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.53/4.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.53/4.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.53/4.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.53/4.68  
% 12.53/4.71  tff(f_180, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 12.53/4.71  tff(f_102, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 12.53/4.71  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.53/4.71  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.53/4.71  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 12.53/4.71  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 12.53/4.71  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 12.53/4.71  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.53/4.71  tff(f_138, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 12.53/4.71  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 12.53/4.71  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 12.53/4.71  tff(f_163, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 12.53/4.71  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 12.53/4.71  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 12.53/4.71  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 12.53/4.71  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 12.53/4.71  tff(f_142, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 12.53/4.71  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_funct_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_1)).
% 12.53/4.71  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 12.53/4.71  tff(c_82, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.53/4.71  tff(c_30196, plain, (![C_1039, A_1040, B_1041]: (v1_xboole_0(C_1039) | ~m1_subset_1(C_1039, k1_zfmisc_1(k2_zfmisc_1(A_1040, B_1041))) | ~v1_xboole_0(A_1040))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.53/4.71  tff(c_30222, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_82, c_30196])).
% 12.53/4.71  tff(c_30227, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_30222])).
% 12.53/4.71  tff(c_227, plain, (![C_72, A_73, B_74]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.53/4.71  tff(c_243, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_227])).
% 12.53/4.71  tff(c_86, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.53/4.71  tff(c_80, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.53/4.71  tff(c_78, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.53/4.71  tff(c_30703, plain, (![A_1075, B_1076, C_1077]: (k2_relset_1(A_1075, B_1076, C_1077)=k2_relat_1(C_1077) | ~m1_subset_1(C_1077, k1_zfmisc_1(k2_zfmisc_1(A_1075, B_1076))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 12.53/4.71  tff(c_30718, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_30703])).
% 12.53/4.71  tff(c_30734, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_30718])).
% 12.53/4.71  tff(c_30, plain, (![A_17]: (k1_relat_1(k2_funct_1(A_17))=k2_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.53/4.71  tff(c_22, plain, (![A_14]: (v1_funct_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.53/4.71  tff(c_76, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.53/4.71  tff(c_137, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_76])).
% 12.53/4.71  tff(c_140, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_137])).
% 12.53/4.71  tff(c_143, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_140])).
% 12.53/4.71  tff(c_181, plain, (![C_67, A_68, B_69]: (v1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.53/4.71  tff(c_190, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_181])).
% 12.53/4.71  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_190])).
% 12.53/4.71  tff(c_206, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_76])).
% 12.53/4.71  tff(c_245, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_206])).
% 12.53/4.71  tff(c_591, plain, (![A_115, B_116, C_117]: (k2_relset_1(A_115, B_116, C_117)=k2_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 12.53/4.71  tff(c_600, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_591])).
% 12.53/4.71  tff(c_614, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_600])).
% 12.53/4.71  tff(c_24, plain, (![A_14]: (v1_relat_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.53/4.71  tff(c_519, plain, (![A_111]: (k1_relat_1(k2_funct_1(A_111))=k2_relat_1(A_111) | ~v2_funct_1(A_111) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.53/4.71  tff(c_16, plain, (![A_9]: (k9_relat_1(A_9, k1_relat_1(A_9))=k2_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.53/4.71  tff(c_12671, plain, (![A_443]: (k9_relat_1(k2_funct_1(A_443), k2_relat_1(A_443))=k2_relat_1(k2_funct_1(A_443)) | ~v1_relat_1(k2_funct_1(A_443)) | ~v2_funct_1(A_443) | ~v1_funct_1(A_443) | ~v1_relat_1(A_443))), inference(superposition, [status(thm), theory('equality')], [c_519, c_16])).
% 12.53/4.71  tff(c_12714, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_614, c_12671])).
% 12.53/4.71  tff(c_12739, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_86, c_80, c_12714])).
% 12.53/4.71  tff(c_12740, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_12739])).
% 12.53/4.71  tff(c_12743, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_12740])).
% 12.53/4.71  tff(c_12747, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_243, c_86, c_12743])).
% 12.53/4.71  tff(c_12749, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_12739])).
% 12.53/4.71  tff(c_207, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_76])).
% 12.53/4.71  tff(c_84, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.53/4.71  tff(c_673, plain, (![A_120, B_121, C_122]: (k1_relset_1(A_120, B_121, C_122)=k1_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.53/4.71  tff(c_695, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_673])).
% 12.53/4.71  tff(c_1704, plain, (![B_197, A_198, C_199]: (k1_xboole_0=B_197 | k1_relset_1(A_198, B_197, C_199)=A_198 | ~v1_funct_2(C_199, A_198, B_197) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_198, B_197))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.53/4.71  tff(c_1719, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_82, c_1704])).
% 12.53/4.71  tff(c_1739, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_695, c_1719])).
% 12.53/4.71  tff(c_1743, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_1739])).
% 12.53/4.71  tff(c_18, plain, (![A_10]: (k10_relat_1(A_10, k2_relat_1(A_10))=k1_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.53/4.71  tff(c_622, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_614, c_18])).
% 12.53/4.71  tff(c_628, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_622])).
% 12.53/4.71  tff(c_1750, plain, (k10_relat_1('#skF_4', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1743, c_628])).
% 12.53/4.71  tff(c_12748, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_12739])).
% 12.53/4.71  tff(c_26, plain, (![B_16, A_15]: (k9_relat_1(k2_funct_1(B_16), A_15)=k10_relat_1(B_16, A_15) | ~v2_funct_1(B_16) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.53/4.71  tff(c_12753, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k10_relat_1('#skF_4', '#skF_3') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12748, c_26])).
% 12.53/4.71  tff(c_12760, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_243, c_86, c_80, c_1750, c_12753])).
% 12.53/4.71  tff(c_70, plain, (![A_41]: (m1_subset_1(A_41, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_41), k2_relat_1(A_41)))) | ~v1_funct_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_163])).
% 12.53/4.71  tff(c_12780, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12760, c_70])).
% 12.53/4.71  tff(c_12804, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_12749, c_207, c_12780])).
% 12.53/4.71  tff(c_12963, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_4'), '#skF_2'))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_30, c_12804])).
% 12.53/4.71  tff(c_12982, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_86, c_80, c_614, c_12963])).
% 12.53/4.71  tff(c_12984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_245, c_12982])).
% 12.53/4.71  tff(c_12985, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1739])).
% 12.53/4.71  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.53/4.71  tff(c_13026, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12985, c_12985, c_8])).
% 12.53/4.71  tff(c_13115, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_13026, c_82])).
% 12.53/4.71  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 12.53/4.71  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.53/4.71  tff(c_392, plain, (![C_100, A_101, B_102]: (v1_xboole_0(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | ~v1_xboole_0(A_101))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.53/4.71  tff(c_407, plain, (![C_100]: (v1_xboole_0(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_392])).
% 12.53/4.71  tff(c_416, plain, (![C_100]: (v1_xboole_0(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_407])).
% 12.53/4.71  tff(c_13368, plain, (![C_463]: (v1_xboole_0(C_463) | ~m1_subset_1(C_463, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_12985, c_416])).
% 12.53/4.71  tff(c_13376, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_13115, c_13368])).
% 12.53/4.71  tff(c_125, plain, (![B_55, A_56]: (~v1_xboole_0(B_55) | B_55=A_56 | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.53/4.71  tff(c_128, plain, (![A_56]: (k1_xboole_0=A_56 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_2, c_125])).
% 12.53/4.71  tff(c_13024, plain, (![A_56]: (A_56='#skF_3' | ~v1_xboole_0(A_56))), inference(demodulation, [status(thm), theory('equality')], [c_12985, c_128])).
% 12.53/4.71  tff(c_13398, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_13376, c_13024])).
% 12.53/4.71  tff(c_12, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.53/4.71  tff(c_696, plain, (![A_120, B_121]: (k1_relset_1(A_120, B_121, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_673])).
% 12.53/4.71  tff(c_48, plain, (![C_36, B_35]: (v1_funct_2(C_36, k1_xboole_0, B_35) | k1_relset_1(k1_xboole_0, B_35, C_36)!=k1_xboole_0 | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_35))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.53/4.71  tff(c_1346, plain, (![C_169, B_170]: (v1_funct_2(C_169, k1_xboole_0, B_170) | k1_relset_1(k1_xboole_0, B_170, C_169)!=k1_xboole_0 | ~m1_subset_1(C_169, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_48])).
% 12.53/4.71  tff(c_1349, plain, (![B_170]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_170) | k1_relset_1(k1_xboole_0, B_170, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_1346])).
% 12.53/4.71  tff(c_1351, plain, (![B_170]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_170) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_696, c_1349])).
% 12.53/4.71  tff(c_1352, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1351])).
% 12.53/4.71  tff(c_58, plain, (![A_37]: (m1_subset_1(k6_partfun1(A_37), k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 12.53/4.71  tff(c_421, plain, (![A_104]: (v1_xboole_0(k6_partfun1(A_104)) | ~v1_xboole_0(A_104))), inference(resolution, [status(thm)], [c_58, c_392])).
% 12.53/4.71  tff(c_429, plain, (![A_105]: (k6_partfun1(A_105)=k1_xboole_0 | ~v1_xboole_0(A_105))), inference(resolution, [status(thm)], [c_421, c_128])).
% 12.53/4.71  tff(c_437, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_429])).
% 12.53/4.71  tff(c_56, plain, (![A_37]: (v1_partfun1(k6_partfun1(A_37), A_37))), inference(cnfTransformation, [status(thm)], [f_142])).
% 12.53/4.71  tff(c_471, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_437, c_56])).
% 12.53/4.71  tff(c_244, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_227])).
% 12.53/4.71  tff(c_208, plain, (![A_70]: (m1_subset_1(k6_partfun1(A_70), k1_zfmisc_1(k2_zfmisc_1(A_70, A_70))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 12.53/4.71  tff(c_212, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_208])).
% 12.53/4.71  tff(c_303, plain, (![B_84, A_85]: (v1_funct_1(B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(A_85)) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.53/4.71  tff(c_315, plain, (v1_funct_1(k6_partfun1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_212, c_303])).
% 12.53/4.71  tff(c_335, plain, (v1_funct_1(k6_partfun1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_244, c_315])).
% 12.53/4.71  tff(c_340, plain, (~v1_funct_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_335])).
% 12.53/4.71  tff(c_339, plain, (![A_5]: (v1_funct_1(k1_xboole_0) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_12, c_303])).
% 12.53/4.71  tff(c_342, plain, (![A_86]: (~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(negUnitSimplification, [status(thm)], [c_340, c_339])).
% 12.53/4.71  tff(c_351, plain, (~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_243, c_342])).
% 12.53/4.71  tff(c_360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_351])).
% 12.53/4.71  tff(c_362, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_335])).
% 12.53/4.71  tff(c_1359, plain, (![C_173, A_174, B_175]: (v1_funct_2(C_173, A_174, B_175) | ~v1_partfun1(C_173, A_174) | ~v1_funct_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 12.53/4.71  tff(c_1384, plain, (![A_174, B_175]: (v1_funct_2(k1_xboole_0, A_174, B_175) | ~v1_partfun1(k1_xboole_0, A_174) | ~v1_funct_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_1359])).
% 12.53/4.71  tff(c_1401, plain, (![A_176, B_177]: (v1_funct_2(k1_xboole_0, A_176, B_177) | ~v1_partfun1(k1_xboole_0, A_176))), inference(demodulation, [status(thm), theory('equality')], [c_362, c_1384])).
% 12.53/4.71  tff(c_52, plain, (![B_35, C_36]: (k1_relset_1(k1_xboole_0, B_35, C_36)=k1_xboole_0 | ~v1_funct_2(C_36, k1_xboole_0, B_35) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_35))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.53/4.71  tff(c_90, plain, (![B_35, C_36]: (k1_relset_1(k1_xboole_0, B_35, C_36)=k1_xboole_0 | ~v1_funct_2(C_36, k1_xboole_0, B_35) | ~m1_subset_1(C_36, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_52])).
% 12.53/4.71  tff(c_1404, plain, (![B_177]: (k1_relset_1(k1_xboole_0, B_177, k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)) | ~v1_partfun1(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_1401, c_90])).
% 12.53/4.71  tff(c_1410, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_471, c_12, c_696, c_1404])).
% 12.53/4.71  tff(c_1412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1352, c_1410])).
% 12.53/4.71  tff(c_1414, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_1351])).
% 12.53/4.71  tff(c_12997, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12985, c_12985, c_1414])).
% 12.53/4.71  tff(c_13426, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13398, c_13398, c_12997])).
% 12.53/4.71  tff(c_734, plain, (![A_129]: (m1_subset_1(A_129, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_129), k2_relat_1(A_129)))) | ~v1_funct_1(A_129) | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_163])).
% 12.53/4.71  tff(c_754, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_614, c_734])).
% 12.53/4.71  tff(c_768, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_86, c_754])).
% 12.53/4.71  tff(c_34, plain, (![C_24, A_21, B_22]: (v1_xboole_0(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.53/4.71  tff(c_837, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_768, c_34])).
% 12.53/4.71  tff(c_843, plain, (~v1_xboole_0(k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_837])).
% 12.53/4.71  tff(c_13486, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13426, c_843])).
% 12.53/4.71  tff(c_13489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13376, c_13486])).
% 12.53/4.71  tff(c_13490, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_837])).
% 12.53/4.71  tff(c_13511, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_13490, c_128])).
% 12.53/4.71  tff(c_13535, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13511, c_13511, c_10])).
% 12.53/4.71  tff(c_13491, plain, (v1_xboole_0(k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_837])).
% 12.53/4.71  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.53/4.71  tff(c_13647, plain, (![A_473]: (A_473='#skF_4' | ~v1_xboole_0(A_473))), inference(resolution, [status(thm)], [c_13490, c_4])).
% 12.53/4.71  tff(c_13660, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_13491, c_13647])).
% 12.53/4.71  tff(c_13517, plain, (![A_120, B_121]: (k1_relset_1(A_120, B_121, '#skF_4')=k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13511, c_13511, c_696])).
% 12.53/4.71  tff(c_13871, plain, (![A_120, B_121]: (k1_relset_1(A_120, B_121, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13660, c_13517])).
% 12.53/4.71  tff(c_13536, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_13511, c_12])).
% 12.53/4.71  tff(c_54, plain, (![B_35, A_34, C_36]: (k1_xboole_0=B_35 | k1_relset_1(A_34, B_35, C_36)=A_34 | ~v1_funct_2(C_36, A_34, B_35) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.53/4.71  tff(c_13988, plain, (![B_499, A_500, C_501]: (B_499='#skF_4' | k1_relset_1(A_500, B_499, C_501)=A_500 | ~v1_funct_2(C_501, A_500, B_499) | ~m1_subset_1(C_501, k1_zfmisc_1(k2_zfmisc_1(A_500, B_499))))), inference(demodulation, [status(thm), theory('equality')], [c_13511, c_54])).
% 12.53/4.71  tff(c_13995, plain, (![B_499, A_500]: (B_499='#skF_4' | k1_relset_1(A_500, B_499, '#skF_4')=A_500 | ~v1_funct_2('#skF_4', A_500, B_499))), inference(resolution, [status(thm)], [c_13536, c_13988])).
% 12.53/4.71  tff(c_14549, plain, (![B_539, A_540]: (B_539='#skF_4' | A_540='#skF_4' | ~v1_funct_2('#skF_4', A_540, B_539))), inference(demodulation, [status(thm), theory('equality')], [c_13871, c_13995])).
% 12.53/4.71  tff(c_14583, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_84, c_14549])).
% 12.53/4.71  tff(c_14584, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_14583])).
% 12.53/4.71  tff(c_414, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_82, c_392])).
% 12.53/4.71  tff(c_419, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_414])).
% 12.53/4.71  tff(c_14585, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14584, c_419])).
% 12.53/4.71  tff(c_14590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13490, c_14585])).
% 12.53/4.71  tff(c_14591, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_14583])).
% 12.53/4.71  tff(c_14600, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_14591, c_245])).
% 12.53/4.71  tff(c_14603, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13535, c_14600])).
% 12.53/4.71  tff(c_438, plain, (![A_106]: (k2_relat_1(k2_funct_1(A_106))=k1_relat_1(A_106) | ~v2_funct_1(A_106) | ~v1_funct_1(A_106) | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.53/4.71  tff(c_19346, plain, (![A_685]: (k10_relat_1(k2_funct_1(A_685), k1_relat_1(A_685))=k1_relat_1(k2_funct_1(A_685)) | ~v1_relat_1(k2_funct_1(A_685)) | ~v2_funct_1(A_685) | ~v1_funct_1(A_685) | ~v1_relat_1(A_685))), inference(superposition, [status(thm), theory('equality')], [c_438, c_18])).
% 12.53/4.71  tff(c_19376, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13660, c_19346])).
% 12.53/4.71  tff(c_19397, plain, (k10_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_86, c_80, c_19376])).
% 12.53/4.71  tff(c_19800, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_19397])).
% 12.53/4.71  tff(c_19803, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_19800])).
% 12.53/4.71  tff(c_19807, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_243, c_86, c_19803])).
% 12.53/4.71  tff(c_19809, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_19397])).
% 12.53/4.71  tff(c_13534, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13511, c_13511, c_8])).
% 12.53/4.71  tff(c_13669, plain, (k10_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13660, c_628])).
% 12.53/4.71  tff(c_14597, plain, (k10_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14591, c_13669])).
% 12.53/4.71  tff(c_14599, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14591, c_614])).
% 12.53/4.71  tff(c_20936, plain, (![A_711]: (k9_relat_1(k2_funct_1(A_711), k2_relat_1(A_711))=k2_relat_1(k2_funct_1(A_711)) | ~v1_relat_1(k2_funct_1(A_711)) | ~v2_funct_1(A_711) | ~v1_funct_1(A_711) | ~v1_relat_1(A_711))), inference(superposition, [status(thm), theory('equality')], [c_519, c_16])).
% 12.53/4.71  tff(c_20975, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14599, c_20936])).
% 12.53/4.71  tff(c_21004, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k2_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_86, c_80, c_19809, c_20975])).
% 12.53/4.71  tff(c_21008, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k10_relat_1('#skF_4', '#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21004, c_26])).
% 12.53/4.71  tff(c_21015, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_243, c_86, c_80, c_14597, c_21008])).
% 12.53/4.71  tff(c_21035, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_21015, c_70])).
% 12.53/4.71  tff(c_21059, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_19809, c_207, c_13534, c_21035])).
% 12.53/4.71  tff(c_21061, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14603, c_21059])).
% 12.53/4.71  tff(c_21062, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_414])).
% 12.53/4.71  tff(c_21069, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_21062, c_128])).
% 12.53/4.71  tff(c_21092, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21069, c_21069, c_8])).
% 12.53/4.71  tff(c_21063, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_414])).
% 12.53/4.71  tff(c_21076, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_21063, c_128])).
% 12.53/4.71  tff(c_21103, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_21069, c_21076])).
% 12.53/4.71  tff(c_21106, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_21103, c_245])).
% 12.53/4.71  tff(c_21461, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_21092, c_21106])).
% 12.53/4.71  tff(c_21094, plain, (![A_5]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_21069, c_12])).
% 12.53/4.71  tff(c_21558, plain, (![A_746, B_747, C_748]: (k2_relset_1(A_746, B_747, C_748)=k2_relat_1(C_748) | ~m1_subset_1(C_748, k1_zfmisc_1(k2_zfmisc_1(A_746, B_747))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 12.53/4.71  tff(c_21582, plain, (![A_749, B_750]: (k2_relset_1(A_749, B_750, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_21094, c_21558])).
% 12.53/4.71  tff(c_21108, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_21103, c_78])).
% 12.53/4.71  tff(c_21586, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_21582, c_21108])).
% 12.53/4.71  tff(c_21312, plain, (![A_725]: (k1_relat_1(k2_funct_1(A_725))=k2_relat_1(A_725) | ~v2_funct_1(A_725) | ~v1_funct_1(A_725) | ~v1_relat_1(A_725))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.53/4.71  tff(c_29892, plain, (![A_1011]: (k9_relat_1(k2_funct_1(A_1011), k2_relat_1(A_1011))=k2_relat_1(k2_funct_1(A_1011)) | ~v1_relat_1(k2_funct_1(A_1011)) | ~v2_funct_1(A_1011) | ~v1_funct_1(A_1011) | ~v1_relat_1(A_1011))), inference(superposition, [status(thm), theory('equality')], [c_21312, c_16])).
% 12.53/4.71  tff(c_29938, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21586, c_29892])).
% 12.53/4.71  tff(c_29965, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_243, c_86, c_80, c_29938])).
% 12.53/4.71  tff(c_29966, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_29965])).
% 12.53/4.71  tff(c_29969, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_29966])).
% 12.53/4.71  tff(c_29973, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_243, c_86, c_29969])).
% 12.53/4.71  tff(c_29975, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_29965])).
% 12.53/4.71  tff(c_21670, plain, (![A_755, B_756, C_757]: (k1_relset_1(A_755, B_756, C_757)=k1_relat_1(C_757) | ~m1_subset_1(C_757, k1_zfmisc_1(k2_zfmisc_1(A_755, B_756))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.53/4.71  tff(c_21691, plain, (![A_755, B_756]: (k1_relset_1(A_755, B_756, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_21094, c_21670])).
% 12.53/4.71  tff(c_89, plain, (![C_36, B_35]: (v1_funct_2(C_36, k1_xboole_0, B_35) | k1_relset_1(k1_xboole_0, B_35, C_36)!=k1_xboole_0 | ~m1_subset_1(C_36, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_48])).
% 12.53/4.71  tff(c_21934, plain, (![C_773, B_774]: (v1_funct_2(C_773, '#skF_4', B_774) | k1_relset_1('#skF_4', B_774, C_773)!='#skF_4' | ~m1_subset_1(C_773, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_21069, c_21069, c_21069, c_21069, c_89])).
% 12.53/4.71  tff(c_21937, plain, (![B_774]: (v1_funct_2('#skF_4', '#skF_4', B_774) | k1_relset_1('#skF_4', B_774, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_21094, c_21934])).
% 12.53/4.71  tff(c_21939, plain, (![B_774]: (v1_funct_2('#skF_4', '#skF_4', B_774) | k1_relat_1('#skF_4')!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21691, c_21937])).
% 12.53/4.71  tff(c_21940, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_21939])).
% 12.53/4.71  tff(c_21109, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_21103, c_84])).
% 12.53/4.71  tff(c_22192, plain, (![B_797, C_798]: (k1_relset_1('#skF_4', B_797, C_798)='#skF_4' | ~v1_funct_2(C_798, '#skF_4', B_797) | ~m1_subset_1(C_798, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_21069, c_21069, c_21069, c_21069, c_90])).
% 12.53/4.71  tff(c_22197, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_21109, c_22192])).
% 12.53/4.71  tff(c_22205, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_21094, c_21691, c_22197])).
% 12.53/4.71  tff(c_22207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21940, c_22205])).
% 12.53/4.71  tff(c_22209, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_21939])).
% 12.53/4.71  tff(c_21603, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_21586, c_18])).
% 12.53/4.71  tff(c_21611, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_21603])).
% 12.53/4.71  tff(c_22211, plain, (k10_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22209, c_21611])).
% 12.53/4.71  tff(c_29974, plain, (k9_relat_1(k2_funct_1('#skF_4'), '#skF_3')=k2_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_29965])).
% 12.53/4.71  tff(c_29979, plain, (k2_relat_1(k2_funct_1('#skF_4'))=k10_relat_1('#skF_4', '#skF_3') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_29974, c_26])).
% 12.53/4.71  tff(c_29986, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_243, c_86, c_80, c_22211, c_29979])).
% 12.53/4.71  tff(c_30006, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_29986, c_70])).
% 12.53/4.71  tff(c_30030, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_29975, c_207, c_21092, c_30006])).
% 12.53/4.71  tff(c_30032, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21461, c_30030])).
% 12.53/4.71  tff(c_30033, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_206])).
% 12.53/4.71  tff(c_30034, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_206])).
% 12.53/4.71  tff(c_30523, plain, (![A_1061, B_1062, C_1063]: (k1_relset_1(A_1061, B_1062, C_1063)=k1_relat_1(C_1063) | ~m1_subset_1(C_1063, k1_zfmisc_1(k2_zfmisc_1(A_1061, B_1062))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 12.53/4.71  tff(c_30551, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_30034, c_30523])).
% 12.53/4.71  tff(c_31737, plain, (![B_1148, C_1149, A_1150]: (k1_xboole_0=B_1148 | v1_funct_2(C_1149, A_1150, B_1148) | k1_relset_1(A_1150, B_1148, C_1149)!=A_1150 | ~m1_subset_1(C_1149, k1_zfmisc_1(k2_zfmisc_1(A_1150, B_1148))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.53/4.71  tff(c_31749, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_30034, c_31737])).
% 12.53/4.71  tff(c_31772, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30551, c_31749])).
% 12.53/4.71  tff(c_31773, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_30033, c_31772])).
% 12.53/4.71  tff(c_31781, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_31773])).
% 12.53/4.71  tff(c_31784, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_30, c_31781])).
% 12.53/4.71  tff(c_31787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_243, c_86, c_80, c_30734, c_31784])).
% 12.53/4.71  tff(c_31788, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_31773])).
% 12.53/4.71  tff(c_31829, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_31788, c_2])).
% 12.53/4.71  tff(c_31831, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30227, c_31829])).
% 12.53/4.71  tff(c_31832, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_30222])).
% 12.53/4.71  tff(c_31839, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_31832, c_128])).
% 12.53/4.71  tff(c_44, plain, (![A_34]: (v1_funct_2(k1_xboole_0, A_34, k1_xboole_0) | k1_xboole_0=A_34 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_34, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.53/4.71  tff(c_88, plain, (![A_34]: (v1_funct_2(k1_xboole_0, A_34, k1_xboole_0) | k1_xboole_0=A_34)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_44])).
% 12.53/4.71  tff(c_31861, plain, (![A_34]: (v1_funct_2('#skF_4', A_34, '#skF_4') | A_34='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_31839, c_31839, c_31839, c_88])).
% 12.53/4.71  tff(c_31862, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_31839, c_31839, c_8])).
% 12.53/4.71  tff(c_31833, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_30222])).
% 12.53/4.71  tff(c_31846, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_31833, c_128])).
% 12.53/4.71  tff(c_31873, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_31839, c_31846])).
% 12.53/4.71  tff(c_31877, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_31873, c_30034])).
% 12.53/4.71  tff(c_32194, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_31862, c_31877])).
% 12.53/4.71  tff(c_30214, plain, (![C_1039]: (v1_xboole_0(C_1039) | ~m1_subset_1(C_1039, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_30196])).
% 12.53/4.71  tff(c_30224, plain, (![C_1039]: (v1_xboole_0(C_1039) | ~m1_subset_1(C_1039, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30214])).
% 12.53/4.71  tff(c_32073, plain, (![C_1039]: (v1_xboole_0(C_1039) | ~m1_subset_1(C_1039, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_31839, c_30224])).
% 12.53/4.71  tff(c_32208, plain, (v1_xboole_0(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_32194, c_32073])).
% 12.53/4.71  tff(c_31840, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_31832, c_4])).
% 12.53/4.71  tff(c_32222, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_32208, c_31840])).
% 12.53/4.71  tff(c_31878, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_31873, c_30033])).
% 12.53/4.71  tff(c_32226, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32222, c_31878])).
% 12.53/4.71  tff(c_32277, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_31861, c_32226])).
% 12.53/4.71  tff(c_30220, plain, (v1_xboole_0(k2_funct_1('#skF_4')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_30034, c_30196])).
% 12.53/4.71  tff(c_31982, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_30220])).
% 12.53/4.71  tff(c_32299, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32277, c_31982])).
% 12.53/4.71  tff(c_32304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31832, c_32299])).
% 12.53/4.71  tff(c_32306, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_30220])).
% 12.53/4.71  tff(c_32312, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_32306, c_31840])).
% 12.53/4.71  tff(c_31881, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31873, c_84])).
% 12.53/4.71  tff(c_32316, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32312, c_31881])).
% 12.53/4.71  tff(c_32305, plain, (v1_xboole_0(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_30220])).
% 12.53/4.71  tff(c_32328, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_32305, c_31840])).
% 12.53/4.71  tff(c_32400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32316, c_32328, c_32312, c_31878])).
% 12.53/4.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.53/4.71  
% 12.53/4.71  Inference rules
% 12.53/4.71  ----------------------
% 12.53/4.71  #Ref     : 0
% 12.53/4.71  #Sup     : 8271
% 12.53/4.71  #Fact    : 0
% 12.53/4.71  #Define  : 0
% 12.53/4.71  #Split   : 37
% 12.53/4.71  #Chain   : 0
% 12.53/4.71  #Close   : 0
% 12.53/4.71  
% 12.53/4.71  Ordering : KBO
% 12.53/4.71  
% 12.53/4.71  Simplification rules
% 12.53/4.71  ----------------------
% 12.53/4.71  #Subsume      : 1806
% 12.53/4.71  #Demod        : 7904
% 12.53/4.71  #Tautology    : 3887
% 12.53/4.71  #SimpNegUnit  : 78
% 12.53/4.71  #BackRed      : 291
% 12.53/4.71  
% 12.53/4.71  #Partial instantiations: 0
% 12.53/4.71  #Strategies tried      : 1
% 12.53/4.71  
% 12.53/4.71  Timing (in seconds)
% 12.53/4.71  ----------------------
% 12.53/4.71  Preprocessing        : 0.38
% 12.53/4.71  Parsing              : 0.20
% 12.53/4.71  CNF conversion       : 0.02
% 12.53/4.71  Main loop            : 3.51
% 12.53/4.71  Inferencing          : 0.90
% 12.53/4.72  Reduction            : 1.21
% 12.53/4.72  Demodulation         : 0.91
% 12.53/4.72  BG Simplification    : 0.12
% 12.53/4.72  Subsumption          : 1.05
% 12.53/4.72  Abstraction          : 0.15
% 12.53/4.72  MUC search           : 0.00
% 12.53/4.72  Cooper               : 0.00
% 12.53/4.72  Total                : 3.98
% 12.53/4.72  Index Insertion      : 0.00
% 12.53/4.72  Index Deletion       : 0.00
% 12.53/4.72  Index Matching       : 0.00
% 12.53/4.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
