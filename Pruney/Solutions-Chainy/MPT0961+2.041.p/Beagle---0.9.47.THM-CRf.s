%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:47 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 248 expanded)
%              Number of leaves         :   28 (  91 expanded)
%              Depth                    :    9
%              Number of atoms          :  147 ( 574 expanded)
%              Number of equality atoms :   64 ( 239 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k6_subset_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_84,axiom,(
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

tff(f_46,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_43,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_41,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_744,plain,(
    ! [C_131,A_132,B_133] :
      ( m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133)))
      | ~ r1_tarski(k2_relat_1(C_131),B_133)
      | ~ r1_tarski(k1_relat_1(C_131),A_132)
      | ~ v1_relat_1(C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_197,plain,(
    ! [C_47,A_48,B_49] :
      ( m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ r1_tarski(k2_relat_1(C_47),B_49)
      | ~ r1_tarski(k1_relat_1(C_47),A_48)
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28,plain,(
    ! [A_11,B_12,C_13] :
      ( k1_relset_1(A_11,B_12,C_13) = k1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_323,plain,(
    ! [A_68,B_69,C_70] :
      ( k1_relset_1(A_68,B_69,C_70) = k1_relat_1(C_70)
      | ~ r1_tarski(k2_relat_1(C_70),B_69)
      | ~ r1_tarski(k1_relat_1(C_70),A_68)
      | ~ v1_relat_1(C_70) ) ),
    inference(resolution,[status(thm)],[c_197,c_28])).

tff(c_332,plain,(
    ! [A_71,C_72] :
      ( k1_relset_1(A_71,k2_relat_1(C_72),C_72) = k1_relat_1(C_72)
      | ~ r1_tarski(k1_relat_1(C_72),A_71)
      | ~ v1_relat_1(C_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_323])).

tff(c_339,plain,(
    ! [C_72] :
      ( k1_relset_1(k1_relat_1(C_72),k2_relat_1(C_72),C_72) = k1_relat_1(C_72)
      | ~ v1_relat_1(C_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_332])).

tff(c_115,plain,(
    ! [A_29] :
      ( k2_relat_1(A_29) != k1_xboole_0
      | k1_xboole_0 = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_119,plain,
    ( k2_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_115])).

tff(c_120,plain,(
    k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_30,plain,(
    ! [C_16,A_14,B_15] :
      ( m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ r1_tarski(k2_relat_1(C_16),B_15)
      | ~ r1_tarski(k1_relat_1(C_16),A_14)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_300,plain,(
    ! [B_63,C_64,A_65] :
      ( k1_xboole_0 = B_63
      | v1_funct_2(C_64,A_65,B_63)
      | k1_relset_1(A_65,B_63,C_64) != A_65
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_412,plain,(
    ! [B_83,C_84,A_85] :
      ( k1_xboole_0 = B_83
      | v1_funct_2(C_84,A_85,B_83)
      | k1_relset_1(A_85,B_83,C_84) != A_85
      | ~ r1_tarski(k2_relat_1(C_84),B_83)
      | ~ r1_tarski(k1_relat_1(C_84),A_85)
      | ~ v1_relat_1(C_84) ) ),
    inference(resolution,[status(thm)],[c_30,c_300])).

tff(c_420,plain,(
    ! [C_86,A_87] :
      ( k2_relat_1(C_86) = k1_xboole_0
      | v1_funct_2(C_86,A_87,k2_relat_1(C_86))
      | k1_relset_1(A_87,k2_relat_1(C_86),C_86) != A_87
      | ~ r1_tarski(k1_relat_1(C_86),A_87)
      | ~ v1_relat_1(C_86) ) ),
    inference(resolution,[status(thm)],[c_6,c_412])).

tff(c_46,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_99,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_428,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_420,c_99])).

tff(c_438,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6,c_428])).

tff(c_439,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_438])).

tff(c_443,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_439])).

tff(c_447,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_443])).

tff(c_448,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_458,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_448,c_22])).

tff(c_109,plain,(
    ! [A_28] :
      ( k1_relat_1(A_28) != k1_xboole_0
      | k1_xboole_0 = A_28
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_113,plain,
    ( k1_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_109])).

tff(c_114,plain,(
    k1_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_450,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_114])).

tff(c_477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_450])).

tff(c_478,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_479,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_491,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_479])).

tff(c_8,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_8,B_9] : k6_subset_1(A_8,B_9) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_6,B_7] : m1_subset_1(k6_subset_1(A_6,B_7),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_95,plain,(
    ! [A_24,B_25] : m1_subset_1(k4_xboole_0(A_24,B_25),k1_zfmisc_1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16])).

tff(c_98,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_95])).

tff(c_481,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_478,c_98])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_484,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_478,c_14])).

tff(c_580,plain,(
    ! [A_100,B_101,C_102] :
      ( k1_relset_1(A_100,B_101,C_102) = k1_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_592,plain,(
    ! [B_103,C_104] :
      ( k1_relset_1('#skF_1',B_103,C_104) = k1_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_484,c_580])).

tff(c_594,plain,(
    ! [B_103] : k1_relset_1('#skF_1',B_103,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_481,c_592])).

tff(c_599,plain,(
    ! [B_103] : k1_relset_1('#skF_1',B_103,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_594])).

tff(c_36,plain,(
    ! [C_19,B_18] :
      ( v1_funct_2(C_19,k1_xboole_0,B_18)
      | k1_relset_1(k1_xboole_0,B_18,C_19) != k1_xboole_0
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_53,plain,(
    ! [C_19,B_18] :
      ( v1_funct_2(C_19,k1_xboole_0,B_18)
      | k1_relset_1(k1_xboole_0,B_18,C_19) != k1_xboole_0
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_36])).

tff(c_656,plain,(
    ! [C_114,B_115] :
      ( v1_funct_2(C_114,'#skF_1',B_115)
      | k1_relset_1('#skF_1',B_115,C_114) != '#skF_1'
      | ~ m1_subset_1(C_114,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_478,c_478,c_478,c_53])).

tff(c_658,plain,(
    ! [B_115] :
      ( v1_funct_2('#skF_1','#skF_1',B_115)
      | k1_relset_1('#skF_1',B_115,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_481,c_656])).

tff(c_664,plain,(
    ! [B_115] : v1_funct_2('#skF_1','#skF_1',B_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_599,c_658])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_485,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_478,c_20])).

tff(c_492,plain,(
    ~ v1_funct_2('#skF_1','#skF_1',k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_99])).

tff(c_544,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_492])).

tff(c_670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_664,c_544])).

tff(c_671,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_750,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_744,c_671])).

tff(c_761,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6,c_6,c_750])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:49:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.66  
% 2.85/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.66  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k6_subset_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.85/1.66  
% 2.85/1.66  %Foreground sorts:
% 2.85/1.66  
% 2.85/1.66  
% 2.85/1.66  %Background operators:
% 2.85/1.66  
% 2.85/1.66  
% 2.85/1.66  %Foreground operators:
% 2.85/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.85/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.85/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.85/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.85/1.66  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.85/1.66  tff('#skF_1', type, '#skF_1': $i).
% 2.85/1.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.85/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.85/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.85/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.85/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.85/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.85/1.66  
% 2.85/1.67  tff(f_95, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 2.85/1.67  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.85/1.67  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.85/1.67  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.85/1.67  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.85/1.67  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.85/1.67  tff(f_46, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.85/1.67  tff(f_33, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.85/1.67  tff(f_43, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.85/1.67  tff(f_41, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 2.85/1.67  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.85/1.67  tff(c_48, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.85/1.67  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.85/1.67  tff(c_744, plain, (![C_131, A_132, B_133]: (m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))) | ~r1_tarski(k2_relat_1(C_131), B_133) | ~r1_tarski(k1_relat_1(C_131), A_132) | ~v1_relat_1(C_131))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.85/1.67  tff(c_197, plain, (![C_47, A_48, B_49]: (m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~r1_tarski(k2_relat_1(C_47), B_49) | ~r1_tarski(k1_relat_1(C_47), A_48) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.85/1.67  tff(c_28, plain, (![A_11, B_12, C_13]: (k1_relset_1(A_11, B_12, C_13)=k1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.85/1.67  tff(c_323, plain, (![A_68, B_69, C_70]: (k1_relset_1(A_68, B_69, C_70)=k1_relat_1(C_70) | ~r1_tarski(k2_relat_1(C_70), B_69) | ~r1_tarski(k1_relat_1(C_70), A_68) | ~v1_relat_1(C_70))), inference(resolution, [status(thm)], [c_197, c_28])).
% 2.85/1.67  tff(c_332, plain, (![A_71, C_72]: (k1_relset_1(A_71, k2_relat_1(C_72), C_72)=k1_relat_1(C_72) | ~r1_tarski(k1_relat_1(C_72), A_71) | ~v1_relat_1(C_72))), inference(resolution, [status(thm)], [c_6, c_323])).
% 2.85/1.67  tff(c_339, plain, (![C_72]: (k1_relset_1(k1_relat_1(C_72), k2_relat_1(C_72), C_72)=k1_relat_1(C_72) | ~v1_relat_1(C_72))), inference(resolution, [status(thm)], [c_6, c_332])).
% 2.85/1.67  tff(c_115, plain, (![A_29]: (k2_relat_1(A_29)!=k1_xboole_0 | k1_xboole_0=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.85/1.67  tff(c_119, plain, (k2_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_115])).
% 2.85/1.67  tff(c_120, plain, (k2_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_119])).
% 2.85/1.67  tff(c_30, plain, (![C_16, A_14, B_15]: (m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~r1_tarski(k2_relat_1(C_16), B_15) | ~r1_tarski(k1_relat_1(C_16), A_14) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.85/1.67  tff(c_300, plain, (![B_63, C_64, A_65]: (k1_xboole_0=B_63 | v1_funct_2(C_64, A_65, B_63) | k1_relset_1(A_65, B_63, C_64)!=A_65 | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_63))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.85/1.67  tff(c_412, plain, (![B_83, C_84, A_85]: (k1_xboole_0=B_83 | v1_funct_2(C_84, A_85, B_83) | k1_relset_1(A_85, B_83, C_84)!=A_85 | ~r1_tarski(k2_relat_1(C_84), B_83) | ~r1_tarski(k1_relat_1(C_84), A_85) | ~v1_relat_1(C_84))), inference(resolution, [status(thm)], [c_30, c_300])).
% 2.85/1.67  tff(c_420, plain, (![C_86, A_87]: (k2_relat_1(C_86)=k1_xboole_0 | v1_funct_2(C_86, A_87, k2_relat_1(C_86)) | k1_relset_1(A_87, k2_relat_1(C_86), C_86)!=A_87 | ~r1_tarski(k1_relat_1(C_86), A_87) | ~v1_relat_1(C_86))), inference(resolution, [status(thm)], [c_6, c_412])).
% 2.85/1.67  tff(c_46, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.85/1.67  tff(c_44, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.85/1.67  tff(c_50, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 2.85/1.67  tff(c_99, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_50])).
% 2.85/1.67  tff(c_428, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_420, c_99])).
% 2.85/1.67  tff(c_438, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6, c_428])).
% 2.85/1.67  tff(c_439, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_120, c_438])).
% 2.85/1.67  tff(c_443, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_339, c_439])).
% 2.85/1.67  tff(c_447, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_443])).
% 2.85/1.67  tff(c_448, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_119])).
% 2.85/1.67  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.85/1.67  tff(c_458, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_448, c_448, c_22])).
% 2.85/1.67  tff(c_109, plain, (![A_28]: (k1_relat_1(A_28)!=k1_xboole_0 | k1_xboole_0=A_28 | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.85/1.67  tff(c_113, plain, (k1_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_109])).
% 2.85/1.67  tff(c_114, plain, (k1_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_113])).
% 2.85/1.67  tff(c_450, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_448, c_114])).
% 2.85/1.67  tff(c_477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_458, c_450])).
% 2.85/1.67  tff(c_478, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_113])).
% 2.85/1.67  tff(c_479, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_113])).
% 2.85/1.67  tff(c_491, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_478, c_479])).
% 2.85/1.67  tff(c_8, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.85/1.67  tff(c_18, plain, (![A_8, B_9]: (k6_subset_1(A_8, B_9)=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.85/1.67  tff(c_16, plain, (![A_6, B_7]: (m1_subset_1(k6_subset_1(A_6, B_7), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.85/1.67  tff(c_95, plain, (![A_24, B_25]: (m1_subset_1(k4_xboole_0(A_24, B_25), k1_zfmisc_1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16])).
% 2.85/1.67  tff(c_98, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_95])).
% 2.85/1.67  tff(c_481, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_478, c_98])).
% 2.85/1.67  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.85/1.67  tff(c_484, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_478, c_478, c_14])).
% 2.85/1.67  tff(c_580, plain, (![A_100, B_101, C_102]: (k1_relset_1(A_100, B_101, C_102)=k1_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.85/1.67  tff(c_592, plain, (![B_103, C_104]: (k1_relset_1('#skF_1', B_103, C_104)=k1_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_484, c_580])).
% 2.85/1.67  tff(c_594, plain, (![B_103]: (k1_relset_1('#skF_1', B_103, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_481, c_592])).
% 2.85/1.67  tff(c_599, plain, (![B_103]: (k1_relset_1('#skF_1', B_103, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_491, c_594])).
% 2.85/1.67  tff(c_36, plain, (![C_19, B_18]: (v1_funct_2(C_19, k1_xboole_0, B_18) | k1_relset_1(k1_xboole_0, B_18, C_19)!=k1_xboole_0 | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.85/1.67  tff(c_53, plain, (![C_19, B_18]: (v1_funct_2(C_19, k1_xboole_0, B_18) | k1_relset_1(k1_xboole_0, B_18, C_19)!=k1_xboole_0 | ~m1_subset_1(C_19, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_36])).
% 2.85/1.67  tff(c_656, plain, (![C_114, B_115]: (v1_funct_2(C_114, '#skF_1', B_115) | k1_relset_1('#skF_1', B_115, C_114)!='#skF_1' | ~m1_subset_1(C_114, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_478, c_478, c_478, c_53])).
% 2.85/1.67  tff(c_658, plain, (![B_115]: (v1_funct_2('#skF_1', '#skF_1', B_115) | k1_relset_1('#skF_1', B_115, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_481, c_656])).
% 2.85/1.67  tff(c_664, plain, (![B_115]: (v1_funct_2('#skF_1', '#skF_1', B_115))), inference(demodulation, [status(thm), theory('equality')], [c_599, c_658])).
% 2.85/1.67  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.85/1.67  tff(c_485, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_478, c_478, c_20])).
% 2.85/1.67  tff(c_492, plain, (~v1_funct_2('#skF_1', '#skF_1', k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_491, c_99])).
% 2.85/1.67  tff(c_544, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_485, c_492])).
% 2.85/1.67  tff(c_670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_664, c_544])).
% 2.85/1.67  tff(c_671, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_50])).
% 2.85/1.67  tff(c_750, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_744, c_671])).
% 2.85/1.67  tff(c_761, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_6, c_6, c_750])).
% 2.85/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.67  
% 2.85/1.67  Inference rules
% 2.85/1.67  ----------------------
% 2.85/1.67  #Ref     : 0
% 2.85/1.67  #Sup     : 147
% 2.85/1.68  #Fact    : 0
% 2.85/1.68  #Define  : 0
% 2.85/1.68  #Split   : 6
% 2.85/1.68  #Chain   : 0
% 2.85/1.68  #Close   : 0
% 2.85/1.68  
% 2.85/1.68  Ordering : KBO
% 2.85/1.68  
% 2.85/1.68  Simplification rules
% 2.85/1.68  ----------------------
% 2.85/1.68  #Subsume      : 10
% 2.85/1.68  #Demod        : 203
% 2.85/1.68  #Tautology    : 97
% 2.85/1.68  #SimpNegUnit  : 1
% 2.85/1.68  #BackRed      : 19
% 2.85/1.68  
% 2.85/1.68  #Partial instantiations: 0
% 2.85/1.68  #Strategies tried      : 1
% 2.85/1.68  
% 2.85/1.68  Timing (in seconds)
% 2.85/1.68  ----------------------
% 2.85/1.68  Preprocessing        : 0.41
% 2.85/1.68  Parsing              : 0.23
% 2.85/1.68  CNF conversion       : 0.02
% 2.85/1.68  Main loop            : 0.35
% 2.85/1.68  Inferencing          : 0.12
% 2.85/1.68  Reduction            : 0.12
% 2.85/1.68  Demodulation         : 0.08
% 2.85/1.68  BG Simplification    : 0.02
% 2.85/1.68  Subsumption          : 0.06
% 2.85/1.68  Abstraction          : 0.02
% 2.85/1.68  MUC search           : 0.00
% 2.85/1.68  Cooper               : 0.00
% 2.85/1.68  Total                : 0.80
% 2.85/1.68  Index Insertion      : 0.00
% 2.85/1.68  Index Deletion       : 0.00
% 2.85/1.68  Index Matching       : 0.00
% 2.85/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
