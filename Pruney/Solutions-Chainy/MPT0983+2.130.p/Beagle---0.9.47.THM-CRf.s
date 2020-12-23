%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:20 EST 2020

% Result     : Theorem 6.63s
% Output     : CNFRefutation 6.71s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 813 expanded)
%              Number of leaves         :   46 ( 291 expanded)
%              Depth                    :   11
%              Number of atoms          :  236 (2250 expanded)
%              Number of equality atoms :   57 ( 325 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_181,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_122,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_78,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_116,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_120,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_161,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_76,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_75,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_139,axiom,(
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

tff(f_104,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_62,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_138,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_70,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_68,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_54,plain,(
    ! [A_40] : k6_relat_1(A_40) = k6_partfun1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_30,plain,(
    ! [A_20] : v2_funct_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_77,plain,(
    ! [A_20] : v2_funct_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_30])).

tff(c_46,plain,(
    ! [D_36,F_38,E_37,A_33,B_34,C_35] :
      ( m1_subset_1(k1_partfun1(A_33,B_34,C_35,D_36,E_37,F_38),k1_zfmisc_1(k2_zfmisc_1(A_33,D_36)))
      | ~ m1_subset_1(F_38,k1_zfmisc_1(k2_zfmisc_1(C_35,D_36)))
      | ~ v1_funct_1(F_38)
      | ~ m1_subset_1(E_37,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_1(E_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_52,plain,(
    ! [A_39] : m1_subset_1(k6_partfun1(A_39),k1_zfmisc_1(k2_zfmisc_1(A_39,A_39))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_64,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_2697,plain,(
    ! [D_352,C_353,A_354,B_355] :
      ( D_352 = C_353
      | ~ r2_relset_1(A_354,B_355,C_353,D_352)
      | ~ m1_subset_1(D_352,k1_zfmisc_1(k2_zfmisc_1(A_354,B_355)))
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_zfmisc_1(A_354,B_355))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2707,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_64,c_2697])).

tff(c_2726,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2707])).

tff(c_2753,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2726])).

tff(c_3114,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_2753])).

tff(c_3121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_3114])).

tff(c_3122,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2726])).

tff(c_3532,plain,(
    ! [E_476,D_478,C_479,B_477,A_480] :
      ( k1_xboole_0 = C_479
      | v2_funct_1(D_478)
      | ~ v2_funct_1(k1_partfun1(A_480,B_477,B_477,C_479,D_478,E_476))
      | ~ m1_subset_1(E_476,k1_zfmisc_1(k2_zfmisc_1(B_477,C_479)))
      | ~ v1_funct_2(E_476,B_477,C_479)
      | ~ v1_funct_1(E_476)
      | ~ m1_subset_1(D_478,k1_zfmisc_1(k2_zfmisc_1(A_480,B_477)))
      | ~ v1_funct_2(D_478,A_480,B_477)
      | ~ v1_funct_1(D_478) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_3534,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3122,c_3532])).

tff(c_3536,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_66,c_77,c_3534])).

tff(c_3537,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_3536])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_3573,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3537,c_2])).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3570,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3537,c_3537,c_10])).

tff(c_289,plain,(
    ! [B_80,A_81] :
      ( v1_xboole_0(B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_81))
      | ~ v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_314,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_289])).

tff(c_316,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_314])).

tff(c_3771,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3570,c_316])).

tff(c_3776,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3573,c_3771])).

tff(c_3778,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_314])).

tff(c_3777,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_314])).

tff(c_141,plain,(
    ! [B_61,A_62] :
      ( ~ v1_xboole_0(B_61)
      | B_61 = A_62
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_144,plain,(
    ! [A_62] :
      ( k1_xboole_0 = A_62
      | ~ v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_2,c_141])).

tff(c_3784,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3777,c_144])).

tff(c_3890,plain,(
    ! [A_497] :
      ( A_497 = '#skF_5'
      | ~ v1_xboole_0(A_497) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3784,c_144])).

tff(c_3897,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3778,c_3890])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k1_xboole_0 = B_7
      | k1_xboole_0 = A_6
      | k2_zfmisc_1(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4383,plain,(
    ! [B_547,A_548] :
      ( B_547 = '#skF_5'
      | A_548 = '#skF_5'
      | k2_zfmisc_1(A_548,B_547) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3784,c_3784,c_3784,c_8])).

tff(c_4393,plain,
    ( '#skF_5' = '#skF_2'
    | '#skF_5' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_3897,c_4383])).

tff(c_4398,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4393])).

tff(c_4425,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4398,c_3777])).

tff(c_3795,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3784,c_3784,c_10])).

tff(c_4415,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4398,c_4398,c_3795])).

tff(c_315,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_289])).

tff(c_3786,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_315])).

tff(c_4567,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4415,c_3786])).

tff(c_4572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4425,c_4567])).

tff(c_4573,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4393])).

tff(c_4601,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4573,c_3777])).

tff(c_12,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3796,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_5',B_7) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3784,c_3784,c_12])).

tff(c_4592,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_2',B_7) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4573,c_4573,c_3796])).

tff(c_4776,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4592,c_3786])).

tff(c_4781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4601,c_4776])).

tff(c_4782,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_4789,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4782,c_144])).

tff(c_4812,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4789,c_3784])).

tff(c_114,plain,(
    ! [A_59] : k6_relat_1(A_59) = k6_partfun1(A_59) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_28,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_120,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_28])).

tff(c_134,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_77])).

tff(c_4796,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3784,c_134])).

tff(c_4817,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4812,c_4796])).

tff(c_4826,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_4817])).

tff(c_4827,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_26,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4901,plain,(
    ! [B_591,A_592] :
      ( v1_relat_1(B_591)
      | ~ m1_subset_1(B_591,k1_zfmisc_1(A_592))
      | ~ v1_relat_1(A_592) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4916,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_4901])).

tff(c_4930,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_4916])).

tff(c_5015,plain,(
    ! [C_602,B_603,A_604] :
      ( v5_relat_1(C_602,B_603)
      | ~ m1_subset_1(C_602,k1_zfmisc_1(k2_zfmisc_1(A_604,B_603))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5042,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_5015])).

tff(c_6179,plain,(
    ! [A_736,B_737,D_738] :
      ( r2_relset_1(A_736,B_737,D_738,D_738)
      | ~ m1_subset_1(D_738,k1_zfmisc_1(k2_zfmisc_1(A_736,B_737))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6198,plain,(
    ! [A_39] : r2_relset_1(A_39,A_39,k6_partfun1(A_39),k6_partfun1(A_39)) ),
    inference(resolution,[status(thm)],[c_52,c_6179])).

tff(c_6251,plain,(
    ! [A_744,B_745,C_746] :
      ( k2_relset_1(A_744,B_745,C_746) = k2_relat_1(C_746)
      | ~ m1_subset_1(C_746,k1_zfmisc_1(k2_zfmisc_1(A_744,B_745))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6278,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_6251])).

tff(c_6324,plain,(
    ! [D_754,C_755,A_756,B_757] :
      ( D_754 = C_755
      | ~ r2_relset_1(A_756,B_757,C_755,D_754)
      | ~ m1_subset_1(D_754,k1_zfmisc_1(k2_zfmisc_1(A_756,B_757)))
      | ~ m1_subset_1(C_755,k1_zfmisc_1(k2_zfmisc_1(A_756,B_757))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6334,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_64,c_6324])).

tff(c_6353,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6334])).

tff(c_6367,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_6353])).

tff(c_6747,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_6367])).

tff(c_6754,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_6747])).

tff(c_6755,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_6353])).

tff(c_7309,plain,(
    ! [A_888,B_889,C_890,D_891] :
      ( k2_relset_1(A_888,B_889,C_890) = B_889
      | ~ r2_relset_1(B_889,B_889,k1_partfun1(B_889,A_888,A_888,B_889,D_891,C_890),k6_partfun1(B_889))
      | ~ m1_subset_1(D_891,k1_zfmisc_1(k2_zfmisc_1(B_889,A_888)))
      | ~ v1_funct_2(D_891,B_889,A_888)
      | ~ v1_funct_1(D_891)
      | ~ m1_subset_1(C_890,k1_zfmisc_1(k2_zfmisc_1(A_888,B_889)))
      | ~ v1_funct_2(C_890,A_888,B_889)
      | ~ v1_funct_1(C_890) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_7312,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6755,c_7309])).

tff(c_7317,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_76,c_74,c_72,c_6198,c_6278,c_7312])).

tff(c_42,plain,(
    ! [B_32] :
      ( v2_funct_2(B_32,k2_relat_1(B_32))
      | ~ v5_relat_1(B_32,k2_relat_1(B_32))
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_7326,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7317,c_42])).

tff(c_7333,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4930,c_5042,c_7317,c_7326])).

tff(c_7335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4827,c_7333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:48:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.63/2.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.71/2.44  
% 6.71/2.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.71/2.44  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 6.71/2.44  
% 6.71/2.44  %Foreground sorts:
% 6.71/2.44  
% 6.71/2.44  
% 6.71/2.44  %Background operators:
% 6.71/2.44  
% 6.71/2.44  
% 6.71/2.44  %Foreground operators:
% 6.71/2.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.71/2.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.71/2.44  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.71/2.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.71/2.44  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.71/2.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.71/2.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.71/2.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.71/2.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.71/2.44  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.71/2.44  tff('#skF_5', type, '#skF_5': $i).
% 6.71/2.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.71/2.44  tff('#skF_2', type, '#skF_2': $i).
% 6.71/2.44  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.71/2.44  tff('#skF_3', type, '#skF_3': $i).
% 6.71/2.44  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.71/2.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.71/2.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.71/2.44  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.71/2.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.71/2.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.71/2.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.71/2.44  tff('#skF_4', type, '#skF_4': $i).
% 6.71/2.44  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.71/2.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.71/2.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.71/2.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.71/2.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.71/2.44  
% 6.71/2.46  tff(f_181, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 6.71/2.46  tff(f_122, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.71/2.46  tff(f_78, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 6.71/2.46  tff(f_116, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.71/2.46  tff(f_120, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 6.71/2.46  tff(f_96, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.71/2.46  tff(f_161, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 6.71/2.46  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.71/2.46  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.71/2.46  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 6.71/2.46  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 6.71/2.46  tff(f_76, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 6.71/2.46  tff(f_75, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.71/2.46  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.71/2.46  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.71/2.46  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.71/2.46  tff(f_139, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 6.71/2.46  tff(f_104, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.71/2.46  tff(c_62, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.71/2.46  tff(c_138, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_62])).
% 6.71/2.46  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.71/2.46  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.71/2.46  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.71/2.46  tff(c_70, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.71/2.46  tff(c_68, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.71/2.46  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.71/2.46  tff(c_54, plain, (![A_40]: (k6_relat_1(A_40)=k6_partfun1(A_40))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.71/2.46  tff(c_30, plain, (![A_20]: (v2_funct_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.71/2.46  tff(c_77, plain, (![A_20]: (v2_funct_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_30])).
% 6.71/2.46  tff(c_46, plain, (![D_36, F_38, E_37, A_33, B_34, C_35]: (m1_subset_1(k1_partfun1(A_33, B_34, C_35, D_36, E_37, F_38), k1_zfmisc_1(k2_zfmisc_1(A_33, D_36))) | ~m1_subset_1(F_38, k1_zfmisc_1(k2_zfmisc_1(C_35, D_36))) | ~v1_funct_1(F_38) | ~m1_subset_1(E_37, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_1(E_37))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.71/2.46  tff(c_52, plain, (![A_39]: (m1_subset_1(k6_partfun1(A_39), k1_zfmisc_1(k2_zfmisc_1(A_39, A_39))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.71/2.46  tff(c_64, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 6.71/2.46  tff(c_2697, plain, (![D_352, C_353, A_354, B_355]: (D_352=C_353 | ~r2_relset_1(A_354, B_355, C_353, D_352) | ~m1_subset_1(D_352, k1_zfmisc_1(k2_zfmisc_1(A_354, B_355))) | ~m1_subset_1(C_353, k1_zfmisc_1(k2_zfmisc_1(A_354, B_355))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.71/2.46  tff(c_2707, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_64, c_2697])).
% 6.71/2.46  tff(c_2726, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2707])).
% 6.71/2.46  tff(c_2753, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2726])).
% 6.71/2.46  tff(c_3114, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_2753])).
% 6.71/2.46  tff(c_3121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_3114])).
% 6.71/2.46  tff(c_3122, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2726])).
% 6.71/2.46  tff(c_3532, plain, (![E_476, D_478, C_479, B_477, A_480]: (k1_xboole_0=C_479 | v2_funct_1(D_478) | ~v2_funct_1(k1_partfun1(A_480, B_477, B_477, C_479, D_478, E_476)) | ~m1_subset_1(E_476, k1_zfmisc_1(k2_zfmisc_1(B_477, C_479))) | ~v1_funct_2(E_476, B_477, C_479) | ~v1_funct_1(E_476) | ~m1_subset_1(D_478, k1_zfmisc_1(k2_zfmisc_1(A_480, B_477))) | ~v1_funct_2(D_478, A_480, B_477) | ~v1_funct_1(D_478))), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.71/2.46  tff(c_3534, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3122, c_3532])).
% 6.71/2.46  tff(c_3536, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_66, c_77, c_3534])).
% 6.71/2.46  tff(c_3537, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_138, c_3536])).
% 6.71/2.46  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.71/2.46  tff(c_3573, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3537, c_2])).
% 6.71/2.46  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.71/2.46  tff(c_3570, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3537, c_3537, c_10])).
% 6.71/2.46  tff(c_289, plain, (![B_80, A_81]: (v1_xboole_0(B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(A_81)) | ~v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.71/2.46  tff(c_314, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_289])).
% 6.71/2.46  tff(c_316, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_314])).
% 6.71/2.46  tff(c_3771, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3570, c_316])).
% 6.71/2.46  tff(c_3776, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3573, c_3771])).
% 6.71/2.46  tff(c_3778, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_314])).
% 6.71/2.46  tff(c_3777, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_314])).
% 6.71/2.46  tff(c_141, plain, (![B_61, A_62]: (~v1_xboole_0(B_61) | B_61=A_62 | ~v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.71/2.46  tff(c_144, plain, (![A_62]: (k1_xboole_0=A_62 | ~v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_2, c_141])).
% 6.71/2.46  tff(c_3784, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3777, c_144])).
% 6.71/2.46  tff(c_3890, plain, (![A_497]: (A_497='#skF_5' | ~v1_xboole_0(A_497))), inference(demodulation, [status(thm), theory('equality')], [c_3784, c_144])).
% 6.71/2.46  tff(c_3897, plain, (k2_zfmisc_1('#skF_3', '#skF_2')='#skF_5'), inference(resolution, [status(thm)], [c_3778, c_3890])).
% 6.71/2.46  tff(c_8, plain, (![B_7, A_6]: (k1_xboole_0=B_7 | k1_xboole_0=A_6 | k2_zfmisc_1(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.71/2.46  tff(c_4383, plain, (![B_547, A_548]: (B_547='#skF_5' | A_548='#skF_5' | k2_zfmisc_1(A_548, B_547)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3784, c_3784, c_3784, c_8])).
% 6.71/2.46  tff(c_4393, plain, ('#skF_5'='#skF_2' | '#skF_5'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_3897, c_4383])).
% 6.71/2.46  tff(c_4398, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_4393])).
% 6.71/2.46  tff(c_4425, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4398, c_3777])).
% 6.71/2.46  tff(c_3795, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3784, c_3784, c_10])).
% 6.71/2.46  tff(c_4415, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4398, c_4398, c_3795])).
% 6.71/2.46  tff(c_315, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_289])).
% 6.71/2.46  tff(c_3786, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_315])).
% 6.71/2.46  tff(c_4567, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4415, c_3786])).
% 6.71/2.46  tff(c_4572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4425, c_4567])).
% 6.71/2.46  tff(c_4573, plain, ('#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_4393])).
% 6.71/2.46  tff(c_4601, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4573, c_3777])).
% 6.71/2.46  tff(c_12, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.71/2.46  tff(c_3796, plain, (![B_7]: (k2_zfmisc_1('#skF_5', B_7)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3784, c_3784, c_12])).
% 6.71/2.46  tff(c_4592, plain, (![B_7]: (k2_zfmisc_1('#skF_2', B_7)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4573, c_4573, c_3796])).
% 6.71/2.46  tff(c_4776, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4592, c_3786])).
% 6.71/2.46  tff(c_4781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4601, c_4776])).
% 6.71/2.46  tff(c_4782, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_315])).
% 6.71/2.46  tff(c_4789, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4782, c_144])).
% 6.71/2.46  tff(c_4812, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4789, c_3784])).
% 6.71/2.46  tff(c_114, plain, (![A_59]: (k6_relat_1(A_59)=k6_partfun1(A_59))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.71/2.46  tff(c_28, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.71/2.46  tff(c_120, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_114, c_28])).
% 6.71/2.46  tff(c_134, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_120, c_77])).
% 6.71/2.46  tff(c_4796, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3784, c_134])).
% 6.71/2.46  tff(c_4817, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4812, c_4796])).
% 6.71/2.46  tff(c_4826, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_4817])).
% 6.71/2.46  tff(c_4827, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_62])).
% 6.71/2.46  tff(c_26, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.71/2.46  tff(c_4901, plain, (![B_591, A_592]: (v1_relat_1(B_591) | ~m1_subset_1(B_591, k1_zfmisc_1(A_592)) | ~v1_relat_1(A_592))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.71/2.46  tff(c_4916, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_4901])).
% 6.71/2.46  tff(c_4930, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_4916])).
% 6.71/2.46  tff(c_5015, plain, (![C_602, B_603, A_604]: (v5_relat_1(C_602, B_603) | ~m1_subset_1(C_602, k1_zfmisc_1(k2_zfmisc_1(A_604, B_603))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.71/2.46  tff(c_5042, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_5015])).
% 6.71/2.46  tff(c_6179, plain, (![A_736, B_737, D_738]: (r2_relset_1(A_736, B_737, D_738, D_738) | ~m1_subset_1(D_738, k1_zfmisc_1(k2_zfmisc_1(A_736, B_737))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.71/2.46  tff(c_6198, plain, (![A_39]: (r2_relset_1(A_39, A_39, k6_partfun1(A_39), k6_partfun1(A_39)))), inference(resolution, [status(thm)], [c_52, c_6179])).
% 6.71/2.46  tff(c_6251, plain, (![A_744, B_745, C_746]: (k2_relset_1(A_744, B_745, C_746)=k2_relat_1(C_746) | ~m1_subset_1(C_746, k1_zfmisc_1(k2_zfmisc_1(A_744, B_745))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.71/2.46  tff(c_6278, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_6251])).
% 6.71/2.46  tff(c_6324, plain, (![D_754, C_755, A_756, B_757]: (D_754=C_755 | ~r2_relset_1(A_756, B_757, C_755, D_754) | ~m1_subset_1(D_754, k1_zfmisc_1(k2_zfmisc_1(A_756, B_757))) | ~m1_subset_1(C_755, k1_zfmisc_1(k2_zfmisc_1(A_756, B_757))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.71/2.46  tff(c_6334, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_64, c_6324])).
% 6.71/2.46  tff(c_6353, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6334])).
% 6.71/2.46  tff(c_6367, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_6353])).
% 6.71/2.46  tff(c_6747, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_6367])).
% 6.71/2.46  tff(c_6754, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_6747])).
% 6.71/2.46  tff(c_6755, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_6353])).
% 6.71/2.46  tff(c_7309, plain, (![A_888, B_889, C_890, D_891]: (k2_relset_1(A_888, B_889, C_890)=B_889 | ~r2_relset_1(B_889, B_889, k1_partfun1(B_889, A_888, A_888, B_889, D_891, C_890), k6_partfun1(B_889)) | ~m1_subset_1(D_891, k1_zfmisc_1(k2_zfmisc_1(B_889, A_888))) | ~v1_funct_2(D_891, B_889, A_888) | ~v1_funct_1(D_891) | ~m1_subset_1(C_890, k1_zfmisc_1(k2_zfmisc_1(A_888, B_889))) | ~v1_funct_2(C_890, A_888, B_889) | ~v1_funct_1(C_890))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.71/2.46  tff(c_7312, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6755, c_7309])).
% 6.71/2.46  tff(c_7317, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_76, c_74, c_72, c_6198, c_6278, c_7312])).
% 6.71/2.46  tff(c_42, plain, (![B_32]: (v2_funct_2(B_32, k2_relat_1(B_32)) | ~v5_relat_1(B_32, k2_relat_1(B_32)) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.71/2.46  tff(c_7326, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7317, c_42])).
% 6.71/2.46  tff(c_7333, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4930, c_5042, c_7317, c_7326])).
% 6.71/2.46  tff(c_7335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4827, c_7333])).
% 6.71/2.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.71/2.46  
% 6.71/2.46  Inference rules
% 6.71/2.46  ----------------------
% 6.71/2.46  #Ref     : 0
% 6.71/2.46  #Sup     : 1585
% 6.71/2.46  #Fact    : 0
% 6.71/2.46  #Define  : 0
% 6.71/2.46  #Split   : 31
% 6.71/2.46  #Chain   : 0
% 6.71/2.46  #Close   : 0
% 6.71/2.46  
% 6.71/2.46  Ordering : KBO
% 6.71/2.46  
% 6.71/2.46  Simplification rules
% 6.71/2.46  ----------------------
% 6.71/2.46  #Subsume      : 167
% 6.71/2.46  #Demod        : 1418
% 6.71/2.46  #Tautology    : 671
% 6.71/2.46  #SimpNegUnit  : 11
% 6.71/2.46  #BackRed      : 314
% 6.71/2.46  
% 6.71/2.46  #Partial instantiations: 0
% 6.71/2.46  #Strategies tried      : 1
% 6.71/2.46  
% 6.71/2.46  Timing (in seconds)
% 6.71/2.46  ----------------------
% 6.71/2.46  Preprocessing        : 0.36
% 6.71/2.46  Parsing              : 0.20
% 6.71/2.46  CNF conversion       : 0.02
% 6.71/2.46  Main loop            : 1.32
% 6.71/2.46  Inferencing          : 0.45
% 6.71/2.46  Reduction            : 0.46
% 6.71/2.46  Demodulation         : 0.33
% 6.71/2.46  BG Simplification    : 0.05
% 6.71/2.46  Subsumption          : 0.23
% 6.71/2.46  Abstraction          : 0.05
% 6.71/2.46  MUC search           : 0.00
% 6.71/2.46  Cooper               : 0.00
% 6.71/2.46  Total                : 1.72
% 6.71/2.46  Index Insertion      : 0.00
% 6.71/2.46  Index Deletion       : 0.00
% 6.71/2.46  Index Matching       : 0.00
% 6.71/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
