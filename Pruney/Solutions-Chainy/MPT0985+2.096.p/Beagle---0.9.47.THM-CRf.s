%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:41 EST 2020

% Result     : Theorem 6.97s
% Output     : CNFRefutation 7.25s
% Verified   : 
% Statistics : Number of formulae       :  177 (4334 expanded)
%              Number of leaves         :   33 (1483 expanded)
%              Depth                    :   17
%              Number of atoms          :  346 (14775 expanded)
%              Number of equality atoms :   95 (5273 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
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

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_119,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_18,plain,(
    ! [A_11] :
      ( v1_funct_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_62,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_121,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_124,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_121])).

tff(c_127,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_124])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_134,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_141,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_134])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_141])).

tff(c_151,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_255,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_159,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_172,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_159])).

tff(c_66,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_409,plain,(
    ! [A_83,B_84,C_85] :
      ( k1_relset_1(A_83,B_84,C_85) = k1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_428,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_409])).

tff(c_882,plain,(
    ! [B_125,A_126,C_127] :
      ( k1_xboole_0 = B_125
      | k1_relset_1(A_126,B_125,C_127) = A_126
      | ~ v1_funct_2(C_127,A_126,B_125)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_898,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_882])).

tff(c_915,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_428,c_898])).

tff(c_917,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_915])).

tff(c_22,plain,(
    ! [A_12] :
      ( k2_relat_1(k2_funct_1(A_12)) = k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_152,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_64,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_529,plain,(
    ! [A_97,B_98,C_99] :
      ( k2_relset_1(A_97,B_98,C_99) = k2_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_542,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_529])).

tff(c_553,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_542])).

tff(c_397,plain,(
    ! [A_82] :
      ( k1_relat_1(k2_funct_1(A_82)) = k2_relat_1(A_82)
      | ~ v2_funct_1(A_82)
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_58,plain,(
    ! [A_28] :
      ( v1_funct_2(A_28,k1_relat_1(A_28),k2_relat_1(A_28))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2095,plain,(
    ! [A_196] :
      ( v1_funct_2(k2_funct_1(A_196),k2_relat_1(A_196),k2_relat_1(k2_funct_1(A_196)))
      | ~ v1_funct_1(k2_funct_1(A_196))
      | ~ v1_relat_1(k2_funct_1(A_196))
      | ~ v2_funct_1(A_196)
      | ~ v1_funct_1(A_196)
      | ~ v1_relat_1(A_196) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_58])).

tff(c_2101,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_2095])).

tff(c_2111,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_72,c_66,c_152,c_2101])).

tff(c_2112,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2111])).

tff(c_2115,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_2112])).

tff(c_2119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_72,c_2115])).

tff(c_2121,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2111])).

tff(c_24,plain,(
    ! [A_12] :
      ( k1_relat_1(k2_funct_1(A_12)) = k2_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_442,plain,(
    ! [A_88] :
      ( m1_subset_1(A_88,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_88),k2_relat_1(A_88))))
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2578,plain,(
    ! [A_209] :
      ( m1_subset_1(k2_funct_1(A_209),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_209),k2_relat_1(k2_funct_1(A_209)))))
      | ~ v1_funct_1(k2_funct_1(A_209))
      | ~ v1_relat_1(k2_funct_1(A_209))
      | ~ v2_funct_1(A_209)
      | ~ v1_funct_1(A_209)
      | ~ v1_relat_1(A_209) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_442])).

tff(c_2605,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_2578])).

tff(c_2624,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_72,c_66,c_2121,c_152,c_2605])).

tff(c_2648,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_relat_1('#skF_4'))))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2624])).

tff(c_2663,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_72,c_66,c_917,c_2648])).

tff(c_2665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_2663])).

tff(c_2666,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_915])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2701,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2666,c_2666,c_6])).

tff(c_116,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_120,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_68,c_116])).

tff(c_2732,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2701,c_120])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_467,plain,(
    ! [B_89,C_90] :
      ( k1_relset_1(k1_xboole_0,B_89,C_90) = k1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_409])).

tff(c_480,plain,(
    ! [B_89,A_4] :
      ( k1_relset_1(k1_xboole_0,B_89,A_4) = k1_relat_1(A_4)
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_467])).

tff(c_3279,plain,(
    ! [B_249,A_250] :
      ( k1_relset_1('#skF_3',B_249,A_250) = k1_relat_1(A_250)
      | ~ r1_tarski(A_250,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2666,c_2666,c_480])).

tff(c_3292,plain,(
    ! [B_249] : k1_relset_1('#skF_3',B_249,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2732,c_3279])).

tff(c_2733,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2701,c_68])).

tff(c_36,plain,(
    ! [C_24,B_23] :
      ( v1_funct_2(C_24,k1_xboole_0,B_23)
      | k1_relset_1(k1_xboole_0,B_23,C_24) != k1_xboole_0
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_74,plain,(
    ! [C_24,B_23] :
      ( v1_funct_2(C_24,k1_xboole_0,B_23)
      | k1_relset_1(k1_xboole_0,B_23,C_24) != k1_xboole_0
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_36])).

tff(c_2760,plain,(
    ! [C_24,B_23] :
      ( v1_funct_2(C_24,'#skF_3',B_23)
      | k1_relset_1('#skF_3',B_23,C_24) != '#skF_3'
      | ~ m1_subset_1(C_24,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2666,c_2666,c_2666,c_2666,c_74])).

tff(c_2784,plain,(
    ! [B_23] :
      ( v1_funct_2('#skF_4','#skF_3',B_23)
      | k1_relset_1('#skF_3',B_23,'#skF_4') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_2733,c_2760])).

tff(c_3295,plain,(
    ! [B_23] :
      ( v1_funct_2('#skF_4','#skF_3',B_23)
      | k1_relat_1('#skF_4') != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3292,c_2784])).

tff(c_3342,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3295])).

tff(c_560,plain,
    ( v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_58])).

tff(c_566,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_72,c_560])).

tff(c_34,plain,(
    ! [C_24,A_22] :
      ( k1_xboole_0 = C_24
      | ~ v1_funct_2(C_24,A_22,k1_xboole_0)
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_75,plain,(
    ! [C_24,A_22] :
      ( k1_xboole_0 = C_24
      | ~ v1_funct_2(C_24,A_22,k1_xboole_0)
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_34])).

tff(c_3926,plain,(
    ! [C_288,A_289] :
      ( C_288 = '#skF_3'
      | ~ v1_funct_2(C_288,A_289,'#skF_3')
      | A_289 = '#skF_3'
      | ~ m1_subset_1(C_288,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2666,c_2666,c_2666,c_2666,c_75])).

tff(c_3933,plain,
    ( '#skF_3' = '#skF_4'
    | k1_relat_1('#skF_4') = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_566,c_3926])).

tff(c_3947,plain,
    ( '#skF_3' = '#skF_4'
    | k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2733,c_3933])).

tff(c_3948,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3342,c_3947])).

tff(c_2700,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_3',B_3) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2666,c_2666,c_8])).

tff(c_2792,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2700,c_255])).

tff(c_3995,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3948,c_2792])).

tff(c_4010,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3948,c_553])).

tff(c_4828,plain,(
    ! [A_343] :
      ( v1_funct_2(k2_funct_1(A_343),k2_relat_1(A_343),k2_relat_1(k2_funct_1(A_343)))
      | ~ v1_funct_1(k2_funct_1(A_343))
      | ~ v1_relat_1(k2_funct_1(A_343))
      | ~ v2_funct_1(A_343)
      | ~ v1_funct_1(A_343)
      | ~ v1_relat_1(A_343) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_58])).

tff(c_4834,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4010,c_4828])).

tff(c_4844,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_72,c_66,c_152,c_4834])).

tff(c_4892,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4844])).

tff(c_4895,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_4892])).

tff(c_4899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_72,c_4895])).

tff(c_4901,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4844])).

tff(c_3998,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_4',B_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3948,c_3948,c_2700])).

tff(c_5240,plain,(
    ! [A_368] :
      ( m1_subset_1(k2_funct_1(A_368),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_368),k2_relat_1(k2_funct_1(A_368)))))
      | ~ v1_funct_1(k2_funct_1(A_368))
      | ~ v1_relat_1(k2_funct_1(A_368))
      | ~ v2_funct_1(A_368)
      | ~ v1_funct_1(A_368)
      | ~ v1_relat_1(A_368) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_442])).

tff(c_5267,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4010,c_5240])).

tff(c_5286,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_72,c_66,c_4901,c_152,c_3998,c_5267])).

tff(c_5288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3995,c_5286])).

tff(c_5290,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3295])).

tff(c_2667,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_915])).

tff(c_5293,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5290,c_2667])).

tff(c_6839,plain,(
    ! [C_455,A_456] :
      ( C_455 = '#skF_3'
      | ~ v1_funct_2(C_455,A_456,'#skF_3')
      | A_456 = '#skF_3'
      | ~ m1_subset_1(C_455,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2666,c_2666,c_2666,c_2666,c_75])).

tff(c_6855,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_70,c_6839])).

tff(c_6875,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2733,c_6855])).

tff(c_6876,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_5293,c_6875])).

tff(c_6923,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6876,c_2792])).

tff(c_6937,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6876,c_553])).

tff(c_7701,plain,(
    ! [A_501] :
      ( v1_funct_2(k2_funct_1(A_501),k2_relat_1(A_501),k2_relat_1(k2_funct_1(A_501)))
      | ~ v1_funct_1(k2_funct_1(A_501))
      | ~ v1_relat_1(k2_funct_1(A_501))
      | ~ v2_funct_1(A_501)
      | ~ v1_funct_1(A_501)
      | ~ v1_relat_1(A_501) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_58])).

tff(c_7707,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6937,c_7701])).

tff(c_7717,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_4',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_72,c_66,c_152,c_7707])).

tff(c_7750,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7717])).

tff(c_7753,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_7750])).

tff(c_7757,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_72,c_7753])).

tff(c_7759,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7717])).

tff(c_6926,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_4',B_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6876,c_6876,c_2700])).

tff(c_7960,plain,(
    ! [A_524] :
      ( m1_subset_1(k2_funct_1(A_524),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_524),k2_relat_1(k2_funct_1(A_524)))))
      | ~ v1_funct_1(k2_funct_1(A_524))
      | ~ v1_relat_1(k2_funct_1(A_524))
      | ~ v2_funct_1(A_524)
      | ~ v1_funct_1(A_524)
      | ~ v1_relat_1(A_524) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_442])).

tff(c_7987,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_4')))))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6937,c_7960])).

tff(c_8006,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_72,c_66,c_7759,c_152,c_6926,c_7987])).

tff(c_8008,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6923,c_8006])).

tff(c_8009,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_8319,plain,(
    ! [A_552,B_553,C_554] :
      ( k2_relset_1(A_552,B_553,C_554) = k2_relat_1(C_554)
      | ~ m1_subset_1(C_554,k1_zfmisc_1(k2_zfmisc_1(A_552,B_553))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8335,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_8319])).

tff(c_8347,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_8335])).

tff(c_8010,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_8227,plain,(
    ! [A_540,B_541,C_542] :
      ( k1_relset_1(A_540,B_541,C_542) = k1_relat_1(C_542)
      | ~ m1_subset_1(C_542,k1_zfmisc_1(k2_zfmisc_1(A_540,B_541))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8251,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8010,c_8227])).

tff(c_8511,plain,(
    ! [B_561,C_562,A_563] :
      ( k1_xboole_0 = B_561
      | v1_funct_2(C_562,A_563,B_561)
      | k1_relset_1(A_563,B_561,C_562) != A_563
      | ~ m1_subset_1(C_562,k1_zfmisc_1(k2_zfmisc_1(A_563,B_561))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_8520,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_8010,c_8511])).

tff(c_8542,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8251,c_8520])).

tff(c_8543,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_8009,c_8542])).

tff(c_8551,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_8543])).

tff(c_8554,plain,
    ( k2_relat_1('#skF_4') != '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_8551])).

tff(c_8557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_72,c_66,c_8347,c_8554])).

tff(c_8558,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_8543])).

tff(c_8582,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_2',B_3) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8558,c_8558,c_8])).

tff(c_8655,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8582,c_68])).

tff(c_8254,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_8227])).

tff(c_40,plain,(
    ! [B_23,C_24] :
      ( k1_relset_1(k1_xboole_0,B_23,C_24) = k1_xboole_0
      | ~ v1_funct_2(C_24,k1_xboole_0,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_73,plain,(
    ! [B_23,C_24] :
      ( k1_relset_1(k1_xboole_0,B_23,C_24) = k1_xboole_0
      | ~ v1_funct_2(C_24,k1_xboole_0,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_40])).

tff(c_8590,plain,(
    ! [B_565,C_566] :
      ( k1_relset_1('#skF_2',B_565,C_566) = '#skF_2'
      | ~ v1_funct_2(C_566,'#skF_2',B_565)
      | ~ m1_subset_1(C_566,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8558,c_8558,c_8558,c_8558,c_73])).

tff(c_8595,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_8590])).

tff(c_8599,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8254,c_8595])).

tff(c_8612,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_8599])).

tff(c_8754,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8655,c_8612])).

tff(c_8755,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_8599])).

tff(c_26,plain,(
    ! [C_15,A_13,B_14] :
      ( v1_relat_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8023,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8010,c_26])).

tff(c_8559,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8543])).

tff(c_8869,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8559,c_58])).

tff(c_8882,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k2_relat_1(k2_funct_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8023,c_152,c_8869])).

tff(c_9191,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),'#skF_3',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_8882])).

tff(c_9193,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_72,c_66,c_8755,c_9191])).

tff(c_9195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8009,c_9193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:57:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.97/2.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.25/2.55  
% 7.25/2.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.25/2.55  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.25/2.55  
% 7.25/2.55  %Foreground sorts:
% 7.25/2.55  
% 7.25/2.55  
% 7.25/2.55  %Background operators:
% 7.25/2.55  
% 7.25/2.55  
% 7.25/2.55  %Foreground operators:
% 7.25/2.55  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.25/2.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.25/2.55  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.25/2.55  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.25/2.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.25/2.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.25/2.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.25/2.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.25/2.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.25/2.55  tff('#skF_2', type, '#skF_2': $i).
% 7.25/2.55  tff('#skF_3', type, '#skF_3': $i).
% 7.25/2.55  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.25/2.55  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.25/2.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.25/2.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.25/2.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.25/2.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.25/2.55  tff('#skF_4', type, '#skF_4': $i).
% 7.25/2.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.25/2.55  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.25/2.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.25/2.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.25/2.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.25/2.55  
% 7.25/2.58  tff(f_136, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 7.25/2.58  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.25/2.58  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.25/2.58  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.25/2.58  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.25/2.58  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 7.25/2.58  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.25/2.58  tff(f_119, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 7.25/2.58  tff(f_33, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.25/2.58  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.25/2.58  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.25/2.58  tff(c_18, plain, (![A_11]: (v1_funct_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.25/2.58  tff(c_62, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.25/2.58  tff(c_121, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_62])).
% 7.25/2.58  tff(c_124, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_121])).
% 7.25/2.58  tff(c_127, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_124])).
% 7.25/2.58  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.25/2.58  tff(c_134, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.25/2.58  tff(c_141, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_134])).
% 7.25/2.58  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_141])).
% 7.25/2.58  tff(c_151, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_62])).
% 7.25/2.58  tff(c_255, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_151])).
% 7.25/2.58  tff(c_159, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.25/2.58  tff(c_172, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_159])).
% 7.25/2.58  tff(c_66, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.25/2.58  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.25/2.58  tff(c_409, plain, (![A_83, B_84, C_85]: (k1_relset_1(A_83, B_84, C_85)=k1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.25/2.58  tff(c_428, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_409])).
% 7.25/2.58  tff(c_882, plain, (![B_125, A_126, C_127]: (k1_xboole_0=B_125 | k1_relset_1(A_126, B_125, C_127)=A_126 | ~v1_funct_2(C_127, A_126, B_125) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.25/2.58  tff(c_898, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_68, c_882])).
% 7.25/2.58  tff(c_915, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_428, c_898])).
% 7.25/2.58  tff(c_917, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_915])).
% 7.25/2.58  tff(c_22, plain, (![A_12]: (k2_relat_1(k2_funct_1(A_12))=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.25/2.58  tff(c_20, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.25/2.58  tff(c_152, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_62])).
% 7.25/2.58  tff(c_64, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.25/2.58  tff(c_529, plain, (![A_97, B_98, C_99]: (k2_relset_1(A_97, B_98, C_99)=k2_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.25/2.58  tff(c_542, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_529])).
% 7.25/2.58  tff(c_553, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_542])).
% 7.25/2.58  tff(c_397, plain, (![A_82]: (k1_relat_1(k2_funct_1(A_82))=k2_relat_1(A_82) | ~v2_funct_1(A_82) | ~v1_funct_1(A_82) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.25/2.58  tff(c_58, plain, (![A_28]: (v1_funct_2(A_28, k1_relat_1(A_28), k2_relat_1(A_28)) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.25/2.58  tff(c_2095, plain, (![A_196]: (v1_funct_2(k2_funct_1(A_196), k2_relat_1(A_196), k2_relat_1(k2_funct_1(A_196))) | ~v1_funct_1(k2_funct_1(A_196)) | ~v1_relat_1(k2_funct_1(A_196)) | ~v2_funct_1(A_196) | ~v1_funct_1(A_196) | ~v1_relat_1(A_196))), inference(superposition, [status(thm), theory('equality')], [c_397, c_58])).
% 7.25/2.58  tff(c_2101, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_553, c_2095])).
% 7.25/2.58  tff(c_2111, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_72, c_66, c_152, c_2101])).
% 7.25/2.58  tff(c_2112, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_2111])).
% 7.25/2.58  tff(c_2115, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_2112])).
% 7.25/2.58  tff(c_2119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_172, c_72, c_2115])).
% 7.25/2.58  tff(c_2121, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2111])).
% 7.25/2.58  tff(c_24, plain, (![A_12]: (k1_relat_1(k2_funct_1(A_12))=k2_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.25/2.58  tff(c_442, plain, (![A_88]: (m1_subset_1(A_88, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_88), k2_relat_1(A_88)))) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.25/2.58  tff(c_2578, plain, (![A_209]: (m1_subset_1(k2_funct_1(A_209), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_209), k2_relat_1(k2_funct_1(A_209))))) | ~v1_funct_1(k2_funct_1(A_209)) | ~v1_relat_1(k2_funct_1(A_209)) | ~v2_funct_1(A_209) | ~v1_funct_1(A_209) | ~v1_relat_1(A_209))), inference(superposition, [status(thm), theory('equality')], [c_24, c_442])).
% 7.25/2.58  tff(c_2605, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_553, c_2578])).
% 7.25/2.58  tff(c_2624, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_72, c_66, c_2121, c_152, c_2605])).
% 7.25/2.58  tff(c_2648, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_relat_1('#skF_4')))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_22, c_2624])).
% 7.25/2.58  tff(c_2663, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_72, c_66, c_917, c_2648])).
% 7.25/2.58  tff(c_2665, plain, $false, inference(negUnitSimplification, [status(thm)], [c_255, c_2663])).
% 7.25/2.58  tff(c_2666, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_915])).
% 7.25/2.58  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.25/2.58  tff(c_2701, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2666, c_2666, c_6])).
% 7.25/2.58  tff(c_116, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.25/2.58  tff(c_120, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_68, c_116])).
% 7.25/2.58  tff(c_2732, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2701, c_120])).
% 7.25/2.58  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.25/2.58  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.25/2.58  tff(c_467, plain, (![B_89, C_90]: (k1_relset_1(k1_xboole_0, B_89, C_90)=k1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_409])).
% 7.25/2.58  tff(c_480, plain, (![B_89, A_4]: (k1_relset_1(k1_xboole_0, B_89, A_4)=k1_relat_1(A_4) | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_467])).
% 7.25/2.58  tff(c_3279, plain, (![B_249, A_250]: (k1_relset_1('#skF_3', B_249, A_250)=k1_relat_1(A_250) | ~r1_tarski(A_250, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2666, c_2666, c_480])).
% 7.25/2.58  tff(c_3292, plain, (![B_249]: (k1_relset_1('#skF_3', B_249, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2732, c_3279])).
% 7.25/2.58  tff(c_2733, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2701, c_68])).
% 7.25/2.58  tff(c_36, plain, (![C_24, B_23]: (v1_funct_2(C_24, k1_xboole_0, B_23) | k1_relset_1(k1_xboole_0, B_23, C_24)!=k1_xboole_0 | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_23))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.25/2.58  tff(c_74, plain, (![C_24, B_23]: (v1_funct_2(C_24, k1_xboole_0, B_23) | k1_relset_1(k1_xboole_0, B_23, C_24)!=k1_xboole_0 | ~m1_subset_1(C_24, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_36])).
% 7.25/2.58  tff(c_2760, plain, (![C_24, B_23]: (v1_funct_2(C_24, '#skF_3', B_23) | k1_relset_1('#skF_3', B_23, C_24)!='#skF_3' | ~m1_subset_1(C_24, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2666, c_2666, c_2666, c_2666, c_74])).
% 7.25/2.58  tff(c_2784, plain, (![B_23]: (v1_funct_2('#skF_4', '#skF_3', B_23) | k1_relset_1('#skF_3', B_23, '#skF_4')!='#skF_3')), inference(resolution, [status(thm)], [c_2733, c_2760])).
% 7.25/2.58  tff(c_3295, plain, (![B_23]: (v1_funct_2('#skF_4', '#skF_3', B_23) | k1_relat_1('#skF_4')!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3292, c_2784])).
% 7.25/2.58  tff(c_3342, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_3295])).
% 7.25/2.58  tff(c_560, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_553, c_58])).
% 7.25/2.58  tff(c_566, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_72, c_560])).
% 7.25/2.58  tff(c_34, plain, (![C_24, A_22]: (k1_xboole_0=C_24 | ~v1_funct_2(C_24, A_22, k1_xboole_0) | k1_xboole_0=A_22 | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.25/2.58  tff(c_75, plain, (![C_24, A_22]: (k1_xboole_0=C_24 | ~v1_funct_2(C_24, A_22, k1_xboole_0) | k1_xboole_0=A_22 | ~m1_subset_1(C_24, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_34])).
% 7.25/2.58  tff(c_3926, plain, (![C_288, A_289]: (C_288='#skF_3' | ~v1_funct_2(C_288, A_289, '#skF_3') | A_289='#skF_3' | ~m1_subset_1(C_288, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2666, c_2666, c_2666, c_2666, c_75])).
% 7.25/2.58  tff(c_3933, plain, ('#skF_3'='#skF_4' | k1_relat_1('#skF_4')='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_566, c_3926])).
% 7.25/2.58  tff(c_3947, plain, ('#skF_3'='#skF_4' | k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2733, c_3933])).
% 7.25/2.58  tff(c_3948, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_3342, c_3947])).
% 7.25/2.58  tff(c_2700, plain, (![B_3]: (k2_zfmisc_1('#skF_3', B_3)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2666, c_2666, c_8])).
% 7.25/2.58  tff(c_2792, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2700, c_255])).
% 7.25/2.58  tff(c_3995, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3948, c_2792])).
% 7.25/2.58  tff(c_4010, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3948, c_553])).
% 7.25/2.58  tff(c_4828, plain, (![A_343]: (v1_funct_2(k2_funct_1(A_343), k2_relat_1(A_343), k2_relat_1(k2_funct_1(A_343))) | ~v1_funct_1(k2_funct_1(A_343)) | ~v1_relat_1(k2_funct_1(A_343)) | ~v2_funct_1(A_343) | ~v1_funct_1(A_343) | ~v1_relat_1(A_343))), inference(superposition, [status(thm), theory('equality')], [c_397, c_58])).
% 7.25/2.58  tff(c_4834, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4010, c_4828])).
% 7.25/2.58  tff(c_4844, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_72, c_66, c_152, c_4834])).
% 7.25/2.58  tff(c_4892, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_4844])).
% 7.25/2.58  tff(c_4895, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_4892])).
% 7.25/2.58  tff(c_4899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_172, c_72, c_4895])).
% 7.25/2.58  tff(c_4901, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4844])).
% 7.25/2.58  tff(c_3998, plain, (![B_3]: (k2_zfmisc_1('#skF_4', B_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3948, c_3948, c_2700])).
% 7.25/2.58  tff(c_5240, plain, (![A_368]: (m1_subset_1(k2_funct_1(A_368), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_368), k2_relat_1(k2_funct_1(A_368))))) | ~v1_funct_1(k2_funct_1(A_368)) | ~v1_relat_1(k2_funct_1(A_368)) | ~v2_funct_1(A_368) | ~v1_funct_1(A_368) | ~v1_relat_1(A_368))), inference(superposition, [status(thm), theory('equality')], [c_24, c_442])).
% 7.25/2.58  tff(c_5267, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4010, c_5240])).
% 7.25/2.58  tff(c_5286, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_72, c_66, c_4901, c_152, c_3998, c_5267])).
% 7.25/2.58  tff(c_5288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3995, c_5286])).
% 7.25/2.58  tff(c_5290, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_3295])).
% 7.25/2.58  tff(c_2667, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitRight, [status(thm)], [c_915])).
% 7.25/2.58  tff(c_5293, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5290, c_2667])).
% 7.25/2.58  tff(c_6839, plain, (![C_455, A_456]: (C_455='#skF_3' | ~v1_funct_2(C_455, A_456, '#skF_3') | A_456='#skF_3' | ~m1_subset_1(C_455, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2666, c_2666, c_2666, c_2666, c_75])).
% 7.25/2.58  tff(c_6855, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_70, c_6839])).
% 7.25/2.58  tff(c_6875, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2733, c_6855])).
% 7.25/2.58  tff(c_6876, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_5293, c_6875])).
% 7.25/2.58  tff(c_6923, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6876, c_2792])).
% 7.25/2.58  tff(c_6937, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6876, c_553])).
% 7.25/2.58  tff(c_7701, plain, (![A_501]: (v1_funct_2(k2_funct_1(A_501), k2_relat_1(A_501), k2_relat_1(k2_funct_1(A_501))) | ~v1_funct_1(k2_funct_1(A_501)) | ~v1_relat_1(k2_funct_1(A_501)) | ~v2_funct_1(A_501) | ~v1_funct_1(A_501) | ~v1_relat_1(A_501))), inference(superposition, [status(thm), theory('equality')], [c_397, c_58])).
% 7.25/2.58  tff(c_7707, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6937, c_7701])).
% 7.25/2.58  tff(c_7717, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_72, c_66, c_152, c_7707])).
% 7.25/2.58  tff(c_7750, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_7717])).
% 7.25/2.58  tff(c_7753, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_7750])).
% 7.25/2.58  tff(c_7757, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_172, c_72, c_7753])).
% 7.25/2.58  tff(c_7759, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_7717])).
% 7.25/2.58  tff(c_6926, plain, (![B_3]: (k2_zfmisc_1('#skF_4', B_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6876, c_6876, c_2700])).
% 7.25/2.58  tff(c_7960, plain, (![A_524]: (m1_subset_1(k2_funct_1(A_524), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_524), k2_relat_1(k2_funct_1(A_524))))) | ~v1_funct_1(k2_funct_1(A_524)) | ~v1_relat_1(k2_funct_1(A_524)) | ~v2_funct_1(A_524) | ~v1_funct_1(A_524) | ~v1_relat_1(A_524))), inference(superposition, [status(thm), theory('equality')], [c_24, c_442])).
% 7.25/2.58  tff(c_7987, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_4'))))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6937, c_7960])).
% 7.25/2.58  tff(c_8006, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_72, c_66, c_7759, c_152, c_6926, c_7987])).
% 7.25/2.58  tff(c_8008, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6923, c_8006])).
% 7.25/2.58  tff(c_8009, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_151])).
% 7.25/2.58  tff(c_8319, plain, (![A_552, B_553, C_554]: (k2_relset_1(A_552, B_553, C_554)=k2_relat_1(C_554) | ~m1_subset_1(C_554, k1_zfmisc_1(k2_zfmisc_1(A_552, B_553))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.25/2.58  tff(c_8335, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_8319])).
% 7.25/2.58  tff(c_8347, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_8335])).
% 7.25/2.58  tff(c_8010, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_151])).
% 7.25/2.58  tff(c_8227, plain, (![A_540, B_541, C_542]: (k1_relset_1(A_540, B_541, C_542)=k1_relat_1(C_542) | ~m1_subset_1(C_542, k1_zfmisc_1(k2_zfmisc_1(A_540, B_541))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.25/2.58  tff(c_8251, plain, (k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_8010, c_8227])).
% 7.25/2.58  tff(c_8511, plain, (![B_561, C_562, A_563]: (k1_xboole_0=B_561 | v1_funct_2(C_562, A_563, B_561) | k1_relset_1(A_563, B_561, C_562)!=A_563 | ~m1_subset_1(C_562, k1_zfmisc_1(k2_zfmisc_1(A_563, B_561))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.25/2.58  tff(c_8520, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k2_funct_1('#skF_4'))!='#skF_3'), inference(resolution, [status(thm)], [c_8010, c_8511])).
% 7.25/2.58  tff(c_8542, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8251, c_8520])).
% 7.25/2.58  tff(c_8543, plain, (k1_xboole_0='#skF_2' | k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_8009, c_8542])).
% 7.25/2.58  tff(c_8551, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_8543])).
% 7.25/2.58  tff(c_8554, plain, (k2_relat_1('#skF_4')!='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_24, c_8551])).
% 7.25/2.58  tff(c_8557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_172, c_72, c_66, c_8347, c_8554])).
% 7.25/2.58  tff(c_8558, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_8543])).
% 7.25/2.58  tff(c_8582, plain, (![B_3]: (k2_zfmisc_1('#skF_2', B_3)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8558, c_8558, c_8])).
% 7.25/2.58  tff(c_8655, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8582, c_68])).
% 7.25/2.58  tff(c_8254, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_8227])).
% 7.25/2.58  tff(c_40, plain, (![B_23, C_24]: (k1_relset_1(k1_xboole_0, B_23, C_24)=k1_xboole_0 | ~v1_funct_2(C_24, k1_xboole_0, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_23))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.25/2.58  tff(c_73, plain, (![B_23, C_24]: (k1_relset_1(k1_xboole_0, B_23, C_24)=k1_xboole_0 | ~v1_funct_2(C_24, k1_xboole_0, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_40])).
% 7.25/2.58  tff(c_8590, plain, (![B_565, C_566]: (k1_relset_1('#skF_2', B_565, C_566)='#skF_2' | ~v1_funct_2(C_566, '#skF_2', B_565) | ~m1_subset_1(C_566, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_8558, c_8558, c_8558, c_8558, c_73])).
% 7.25/2.58  tff(c_8595, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_70, c_8590])).
% 7.25/2.58  tff(c_8599, plain, (k1_relat_1('#skF_4')='#skF_2' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8254, c_8595])).
% 7.25/2.58  tff(c_8612, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_8599])).
% 7.25/2.58  tff(c_8754, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8655, c_8612])).
% 7.25/2.58  tff(c_8755, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_8599])).
% 7.25/2.58  tff(c_26, plain, (![C_15, A_13, B_14]: (v1_relat_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.25/2.58  tff(c_8023, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_8010, c_26])).
% 7.25/2.58  tff(c_8559, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3'), inference(splitRight, [status(thm)], [c_8543])).
% 7.25/2.58  tff(c_8869, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8559, c_58])).
% 7.25/2.58  tff(c_8882, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k2_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_8023, c_152, c_8869])).
% 7.25/2.58  tff(c_9191, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_22, c_8882])).
% 7.25/2.58  tff(c_9193, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_72, c_66, c_8755, c_9191])).
% 7.25/2.58  tff(c_9195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8009, c_9193])).
% 7.25/2.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.25/2.58  
% 7.25/2.58  Inference rules
% 7.25/2.58  ----------------------
% 7.25/2.58  #Ref     : 0
% 7.25/2.58  #Sup     : 1910
% 7.25/2.58  #Fact    : 0
% 7.25/2.58  #Define  : 0
% 7.25/2.58  #Split   : 21
% 7.25/2.58  #Chain   : 0
% 7.25/2.58  #Close   : 0
% 7.25/2.58  
% 7.25/2.58  Ordering : KBO
% 7.25/2.58  
% 7.25/2.58  Simplification rules
% 7.25/2.58  ----------------------
% 7.25/2.58  #Subsume      : 228
% 7.25/2.58  #Demod        : 2410
% 7.25/2.58  #Tautology    : 1362
% 7.25/2.58  #SimpNegUnit  : 23
% 7.25/2.58  #BackRed      : 274
% 7.25/2.58  
% 7.25/2.58  #Partial instantiations: 0
% 7.25/2.58  #Strategies tried      : 1
% 7.25/2.58  
% 7.25/2.58  Timing (in seconds)
% 7.25/2.58  ----------------------
% 7.25/2.58  Preprocessing        : 0.33
% 7.25/2.58  Parsing              : 0.18
% 7.25/2.58  CNF conversion       : 0.02
% 7.25/2.58  Main loop            : 1.46
% 7.25/2.58  Inferencing          : 0.50
% 7.25/2.58  Reduction            : 0.54
% 7.25/2.58  Demodulation         : 0.39
% 7.25/2.58  BG Simplification    : 0.06
% 7.25/2.58  Subsumption          : 0.24
% 7.25/2.58  Abstraction          : 0.07
% 7.25/2.58  MUC search           : 0.00
% 7.25/2.58  Cooper               : 0.00
% 7.25/2.58  Total                : 1.86
% 7.25/2.58  Index Insertion      : 0.00
% 7.25/2.58  Index Deletion       : 0.00
% 7.25/2.58  Index Matching       : 0.00
% 7.25/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
