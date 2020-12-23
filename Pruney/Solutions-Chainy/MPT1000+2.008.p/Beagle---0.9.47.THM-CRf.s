%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:55 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 660 expanded)
%              Number of leaves         :   43 ( 209 expanded)
%              Depth                    :   14
%              Number of atoms          :  203 (1555 expanded)
%              Number of equality atoms :   72 ( 799 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_127,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_60,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_114,axiom,(
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

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_72,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_18,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_92,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_95,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_92])).

tff(c_98,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_95])).

tff(c_124,plain,(
    ! [C_55,B_56,A_57] :
      ( v5_relat_1(C_55,B_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_128,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_124])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_147,plain,(
    ! [B_62,A_63] :
      ( k5_relat_1(B_62,k6_relat_1(A_63)) = B_62
      | ~ r1_tarski(k2_relat_1(B_62),A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_157,plain,(
    ! [B_12,A_11] :
      ( k5_relat_1(B_12,k6_relat_1(A_11)) = B_12
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(resolution,[status(thm)],[c_14,c_147])).

tff(c_16,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_201,plain,(
    ! [A_72,B_73] :
      ( k10_relat_1(A_72,k1_relat_1(B_73)) = k1_relat_1(k5_relat_1(A_72,B_73))
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_210,plain,(
    ! [A_72,A_19] :
      ( k1_relat_1(k5_relat_1(A_72,k6_relat_1(A_19))) = k10_relat_1(A_72,A_19)
      | ~ v1_relat_1(k6_relat_1(A_19))
      | ~ v1_relat_1(A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_201])).

tff(c_218,plain,(
    ! [A_74,A_75] :
      ( k1_relat_1(k5_relat_1(A_74,k6_relat_1(A_75))) = k10_relat_1(A_74,A_75)
      | ~ v1_relat_1(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_210])).

tff(c_273,plain,(
    ! [B_83,A_84] :
      ( k10_relat_1(B_83,A_84) = k1_relat_1(B_83)
      | ~ v1_relat_1(B_83)
      | ~ v5_relat_1(B_83,A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_218])).

tff(c_279,plain,
    ( k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_128,c_273])).

tff(c_285,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_279])).

tff(c_238,plain,(
    ! [A_76,B_77,C_78,D_79] :
      ( k8_relset_1(A_76,B_77,C_78,D_79) = k10_relat_1(C_78,D_79)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_241,plain,(
    ! [D_79] : k8_relset_1('#skF_2','#skF_3','#skF_4',D_79) = k10_relat_1('#skF_4',D_79) ),
    inference(resolution,[status(thm)],[c_56,c_238])).

tff(c_52,plain,(
    k8_relset_1('#skF_2','#skF_3','#skF_4','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_242,plain,(
    k10_relat_1('#skF_4','#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_52])).

tff(c_286,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_242])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_191,plain,(
    ! [A_68,B_69,C_70] :
      ( k1_relset_1(A_68,B_69,C_70) = k1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_195,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_191])).

tff(c_329,plain,(
    ! [B_93,A_94,C_95] :
      ( k1_xboole_0 = B_93
      | k1_relset_1(A_94,B_93,C_95) = A_94
      | ~ v1_funct_2(C_95,A_94,B_93)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_94,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_332,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_329])).

tff(c_335,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_195,c_332])).

tff(c_337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_286,c_80,c_335])).

tff(c_339,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_379,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_4])).

tff(c_338,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_347,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_338])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_342,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_2])).

tff(c_352,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_342])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( v1_xboole_0(k2_zfmisc_1(A_3,B_4))
      | ~ v1_xboole_0(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_378,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_56])).

tff(c_466,plain,(
    ! [C_121,B_122,A_123] :
      ( ~ v1_xboole_0(C_121)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(C_121))
      | ~ r2_hidden(A_123,B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_469,plain,(
    ! [A_123] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_3'))
      | ~ r2_hidden(A_123,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_378,c_466])).

tff(c_490,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_469])).

tff(c_493,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_490])).

tff(c_497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_493])).

tff(c_500,plain,(
    ! [A_127] : ~ r2_hidden(A_127,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_469])).

tff(c_505,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_379,c_500])).

tff(c_389,plain,(
    ! [C_102,B_103,A_104] :
      ( v5_relat_1(C_102,B_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_104,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_393,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_378,c_389])).

tff(c_510,plain,(
    v5_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_393])).

tff(c_382,plain,(
    ! [B_100,A_101] :
      ( v1_relat_1(B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_101))
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_385,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_378,c_382])).

tff(c_388,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_385])).

tff(c_428,plain,(
    ! [C_116,B_117,A_118] :
      ( ~ v1_xboole_0(C_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(C_116))
      | ~ r2_hidden(A_118,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_431,plain,(
    ! [A_118] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_3'))
      | ~ r2_hidden(A_118,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_378,c_428])).

tff(c_432,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_431])).

tff(c_435,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_432])).

tff(c_439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_435])).

tff(c_442,plain,(
    ! [A_119] : ~ r2_hidden(A_119,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_431])).

tff(c_447,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_379,c_442])).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_340,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_338,c_22])).

tff(c_358,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_347,c_340])).

tff(c_399,plain,(
    ! [B_108,A_109] :
      ( r1_tarski(k2_relat_1(B_108),A_109)
      | ~ v5_relat_1(B_108,A_109)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_405,plain,(
    ! [A_109] :
      ( r1_tarski('#skF_3',A_109)
      | ~ v5_relat_1('#skF_3',A_109)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_399])).

tff(c_409,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_448,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_409])).

tff(c_462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_448])).

tff(c_463,plain,(
    ! [A_109] :
      ( r1_tarski('#skF_3',A_109)
      | ~ v5_relat_1('#skF_3',A_109) ) ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_596,plain,(
    ! [A_132] :
      ( r1_tarski('#skF_4',A_132)
      | ~ v5_relat_1('#skF_4',A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_505,c_463])).

tff(c_604,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_510,c_596])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_341,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_338,c_24])).

tff(c_363,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_347,c_341])).

tff(c_515,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_505,c_363])).

tff(c_516,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_505,c_358])).

tff(c_547,plain,(
    ! [B_128,A_129] :
      ( k5_relat_1(B_128,k6_relat_1(A_129)) = B_128
      | ~ r1_tarski(k2_relat_1(B_128),A_129)
      | ~ v1_relat_1(B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_550,plain,(
    ! [A_129] :
      ( k5_relat_1('#skF_4',k6_relat_1(A_129)) = '#skF_4'
      | ~ r1_tarski('#skF_4',A_129)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_516,c_547])).

tff(c_558,plain,(
    ! [A_129] :
      ( k5_relat_1('#skF_4',k6_relat_1(A_129)) = '#skF_4'
      | ~ r1_tarski('#skF_4',A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_550])).

tff(c_646,plain,(
    ! [A_142,B_143] :
      ( k10_relat_1(A_142,k1_relat_1(B_143)) = k1_relat_1(k5_relat_1(A_142,B_143))
      | ~ v1_relat_1(B_143)
      | ~ v1_relat_1(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_658,plain,(
    ! [A_142,A_19] :
      ( k1_relat_1(k5_relat_1(A_142,k6_relat_1(A_19))) = k10_relat_1(A_142,A_19)
      | ~ v1_relat_1(k6_relat_1(A_19))
      | ~ v1_relat_1(A_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_646])).

tff(c_712,plain,(
    ! [A_147,A_148] :
      ( k1_relat_1(k5_relat_1(A_147,k6_relat_1(A_148))) = k10_relat_1(A_147,A_148)
      | ~ v1_relat_1(A_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_658])).

tff(c_730,plain,(
    ! [A_129] :
      ( k10_relat_1('#skF_4',A_129) = k1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_4',A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_712])).

tff(c_741,plain,(
    ! [A_153] :
      ( k10_relat_1('#skF_4',A_153) = '#skF_4'
      | ~ r1_tarski('#skF_4',A_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_515,c_730])).

tff(c_745,plain,(
    k10_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_604,c_741])).

tff(c_512,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_505,c_378])).

tff(c_737,plain,(
    ! [A_149,B_150,C_151,D_152] :
      ( k8_relset_1(A_149,B_150,C_151,D_152) = k10_relat_1(C_151,D_152)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_740,plain,(
    ! [D_152] : k8_relset_1('#skF_4','#skF_4','#skF_4',D_152) = k10_relat_1('#skF_4',D_152) ),
    inference(resolution,[status(thm)],[c_512,c_737])).

tff(c_368,plain,(
    k8_relset_1('#skF_3','#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_347,c_52])).

tff(c_514,plain,(
    k8_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_505,c_505,c_505,c_368])).

tff(c_771,plain,(
    k10_relat_1('#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_514])).

tff(c_774,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_771])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:03:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.42  
% 2.86/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.42  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.86/1.42  
% 2.86/1.42  %Foreground sorts:
% 2.86/1.42  
% 2.86/1.42  
% 2.86/1.42  %Background operators:
% 2.86/1.42  
% 2.86/1.42  
% 2.86/1.42  %Foreground operators:
% 2.86/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.86/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.42  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.86/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.86/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.86/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.86/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.86/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.86/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.86/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.86/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.42  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.86/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.86/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.86/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.86/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.86/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.86/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.86/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.86/1.42  
% 2.86/1.44  tff(f_62, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.86/1.44  tff(f_127, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 2.86/1.44  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.86/1.44  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.86/1.44  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.86/1.44  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.86/1.44  tff(f_60, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.86/1.44  tff(f_76, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.86/1.44  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.86/1.44  tff(f_96, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.86/1.44  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.86/1.44  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.86/1.44  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.86/1.44  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.86/1.44  tff(f_38, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 2.86/1.44  tff(f_45, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.86/1.44  tff(f_72, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.86/1.44  tff(c_18, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.86/1.44  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.86/1.44  tff(c_92, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.86/1.44  tff(c_95, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_92])).
% 2.86/1.44  tff(c_98, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_95])).
% 2.86/1.44  tff(c_124, plain, (![C_55, B_56, A_57]: (v5_relat_1(C_55, B_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.86/1.44  tff(c_128, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_124])).
% 2.86/1.44  tff(c_14, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.86/1.44  tff(c_147, plain, (![B_62, A_63]: (k5_relat_1(B_62, k6_relat_1(A_63))=B_62 | ~r1_tarski(k2_relat_1(B_62), A_63) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.86/1.44  tff(c_157, plain, (![B_12, A_11]: (k5_relat_1(B_12, k6_relat_1(A_11))=B_12 | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(resolution, [status(thm)], [c_14, c_147])).
% 2.86/1.44  tff(c_16, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.86/1.44  tff(c_26, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.86/1.44  tff(c_201, plain, (![A_72, B_73]: (k10_relat_1(A_72, k1_relat_1(B_73))=k1_relat_1(k5_relat_1(A_72, B_73)) | ~v1_relat_1(B_73) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.86/1.44  tff(c_210, plain, (![A_72, A_19]: (k1_relat_1(k5_relat_1(A_72, k6_relat_1(A_19)))=k10_relat_1(A_72, A_19) | ~v1_relat_1(k6_relat_1(A_19)) | ~v1_relat_1(A_72))), inference(superposition, [status(thm), theory('equality')], [c_26, c_201])).
% 2.86/1.44  tff(c_218, plain, (![A_74, A_75]: (k1_relat_1(k5_relat_1(A_74, k6_relat_1(A_75)))=k10_relat_1(A_74, A_75) | ~v1_relat_1(A_74))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_210])).
% 2.86/1.44  tff(c_273, plain, (![B_83, A_84]: (k10_relat_1(B_83, A_84)=k1_relat_1(B_83) | ~v1_relat_1(B_83) | ~v5_relat_1(B_83, A_84) | ~v1_relat_1(B_83))), inference(superposition, [status(thm), theory('equality')], [c_157, c_218])).
% 2.86/1.44  tff(c_279, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_128, c_273])).
% 2.86/1.44  tff(c_285, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_279])).
% 2.86/1.44  tff(c_238, plain, (![A_76, B_77, C_78, D_79]: (k8_relset_1(A_76, B_77, C_78, D_79)=k10_relat_1(C_78, D_79) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.86/1.44  tff(c_241, plain, (![D_79]: (k8_relset_1('#skF_2', '#skF_3', '#skF_4', D_79)=k10_relat_1('#skF_4', D_79))), inference(resolution, [status(thm)], [c_56, c_238])).
% 2.86/1.44  tff(c_52, plain, (k8_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.86/1.44  tff(c_242, plain, (k10_relat_1('#skF_4', '#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_241, c_52])).
% 2.86/1.44  tff(c_286, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_285, c_242])).
% 2.86/1.44  tff(c_54, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.86/1.44  tff(c_80, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_54])).
% 2.86/1.44  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 2.86/1.44  tff(c_191, plain, (![A_68, B_69, C_70]: (k1_relset_1(A_68, B_69, C_70)=k1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.86/1.44  tff(c_195, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_191])).
% 2.86/1.44  tff(c_329, plain, (![B_93, A_94, C_95]: (k1_xboole_0=B_93 | k1_relset_1(A_94, B_93, C_95)=A_94 | ~v1_funct_2(C_95, A_94, B_93) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_94, B_93))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.86/1.44  tff(c_332, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_329])).
% 2.86/1.44  tff(c_335, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_195, c_332])).
% 2.86/1.44  tff(c_337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_286, c_80, c_335])).
% 2.86/1.44  tff(c_339, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_54])).
% 2.86/1.44  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.86/1.44  tff(c_379, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_4])).
% 2.86/1.44  tff(c_338, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_54])).
% 2.86/1.44  tff(c_347, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_339, c_338])).
% 2.86/1.44  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.86/1.44  tff(c_342, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_338, c_2])).
% 2.86/1.44  tff(c_352, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_347, c_342])).
% 2.86/1.44  tff(c_6, plain, (![A_3, B_4]: (v1_xboole_0(k2_zfmisc_1(A_3, B_4)) | ~v1_xboole_0(B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.86/1.44  tff(c_378, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_56])).
% 2.86/1.44  tff(c_466, plain, (![C_121, B_122, A_123]: (~v1_xboole_0(C_121) | ~m1_subset_1(B_122, k1_zfmisc_1(C_121)) | ~r2_hidden(A_123, B_122))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.86/1.44  tff(c_469, plain, (![A_123]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_3')) | ~r2_hidden(A_123, '#skF_4'))), inference(resolution, [status(thm)], [c_378, c_466])).
% 2.86/1.44  tff(c_490, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(splitLeft, [status(thm)], [c_469])).
% 2.86/1.44  tff(c_493, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_6, c_490])).
% 2.86/1.44  tff(c_497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_352, c_493])).
% 2.86/1.44  tff(c_500, plain, (![A_127]: (~r2_hidden(A_127, '#skF_4'))), inference(splitRight, [status(thm)], [c_469])).
% 2.86/1.44  tff(c_505, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_379, c_500])).
% 2.86/1.44  tff(c_389, plain, (![C_102, B_103, A_104]: (v5_relat_1(C_102, B_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_104, B_103))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.86/1.44  tff(c_393, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_378, c_389])).
% 2.86/1.44  tff(c_510, plain, (v5_relat_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_505, c_393])).
% 2.86/1.44  tff(c_382, plain, (![B_100, A_101]: (v1_relat_1(B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(A_101)) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.86/1.44  tff(c_385, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_378, c_382])).
% 2.86/1.44  tff(c_388, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_385])).
% 2.86/1.44  tff(c_428, plain, (![C_116, B_117, A_118]: (~v1_xboole_0(C_116) | ~m1_subset_1(B_117, k1_zfmisc_1(C_116)) | ~r2_hidden(A_118, B_117))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.86/1.44  tff(c_431, plain, (![A_118]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_3')) | ~r2_hidden(A_118, '#skF_4'))), inference(resolution, [status(thm)], [c_378, c_428])).
% 2.86/1.44  tff(c_432, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(splitLeft, [status(thm)], [c_431])).
% 2.86/1.44  tff(c_435, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_6, c_432])).
% 2.86/1.44  tff(c_439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_352, c_435])).
% 2.86/1.44  tff(c_442, plain, (![A_119]: (~r2_hidden(A_119, '#skF_4'))), inference(splitRight, [status(thm)], [c_431])).
% 2.86/1.44  tff(c_447, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_379, c_442])).
% 2.86/1.44  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.86/1.44  tff(c_340, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_338, c_338, c_22])).
% 2.86/1.44  tff(c_358, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_347, c_347, c_340])).
% 2.86/1.44  tff(c_399, plain, (![B_108, A_109]: (r1_tarski(k2_relat_1(B_108), A_109) | ~v5_relat_1(B_108, A_109) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.86/1.44  tff(c_405, plain, (![A_109]: (r1_tarski('#skF_3', A_109) | ~v5_relat_1('#skF_3', A_109) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_358, c_399])).
% 2.86/1.44  tff(c_409, plain, (~v1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_405])).
% 2.86/1.44  tff(c_448, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_447, c_409])).
% 2.86/1.44  tff(c_462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_388, c_448])).
% 2.86/1.44  tff(c_463, plain, (![A_109]: (r1_tarski('#skF_3', A_109) | ~v5_relat_1('#skF_3', A_109))), inference(splitRight, [status(thm)], [c_405])).
% 2.86/1.44  tff(c_596, plain, (![A_132]: (r1_tarski('#skF_4', A_132) | ~v5_relat_1('#skF_4', A_132))), inference(demodulation, [status(thm), theory('equality')], [c_505, c_505, c_463])).
% 2.86/1.44  tff(c_604, plain, (r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_510, c_596])).
% 2.86/1.44  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.86/1.44  tff(c_341, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_338, c_338, c_24])).
% 2.86/1.44  tff(c_363, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_347, c_347, c_341])).
% 2.86/1.44  tff(c_515, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_505, c_505, c_363])).
% 2.86/1.44  tff(c_516, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_505, c_505, c_358])).
% 2.86/1.44  tff(c_547, plain, (![B_128, A_129]: (k5_relat_1(B_128, k6_relat_1(A_129))=B_128 | ~r1_tarski(k2_relat_1(B_128), A_129) | ~v1_relat_1(B_128))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.86/1.44  tff(c_550, plain, (![A_129]: (k5_relat_1('#skF_4', k6_relat_1(A_129))='#skF_4' | ~r1_tarski('#skF_4', A_129) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_516, c_547])).
% 2.86/1.44  tff(c_558, plain, (![A_129]: (k5_relat_1('#skF_4', k6_relat_1(A_129))='#skF_4' | ~r1_tarski('#skF_4', A_129))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_550])).
% 2.86/1.44  tff(c_646, plain, (![A_142, B_143]: (k10_relat_1(A_142, k1_relat_1(B_143))=k1_relat_1(k5_relat_1(A_142, B_143)) | ~v1_relat_1(B_143) | ~v1_relat_1(A_142))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.86/1.44  tff(c_658, plain, (![A_142, A_19]: (k1_relat_1(k5_relat_1(A_142, k6_relat_1(A_19)))=k10_relat_1(A_142, A_19) | ~v1_relat_1(k6_relat_1(A_19)) | ~v1_relat_1(A_142))), inference(superposition, [status(thm), theory('equality')], [c_26, c_646])).
% 2.86/1.44  tff(c_712, plain, (![A_147, A_148]: (k1_relat_1(k5_relat_1(A_147, k6_relat_1(A_148)))=k10_relat_1(A_147, A_148) | ~v1_relat_1(A_147))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_658])).
% 2.86/1.44  tff(c_730, plain, (![A_129]: (k10_relat_1('#skF_4', A_129)=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_4', A_129))), inference(superposition, [status(thm), theory('equality')], [c_558, c_712])).
% 2.86/1.44  tff(c_741, plain, (![A_153]: (k10_relat_1('#skF_4', A_153)='#skF_4' | ~r1_tarski('#skF_4', A_153))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_515, c_730])).
% 2.86/1.44  tff(c_745, plain, (k10_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_604, c_741])).
% 2.86/1.44  tff(c_512, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_505, c_505, c_378])).
% 2.86/1.44  tff(c_737, plain, (![A_149, B_150, C_151, D_152]: (k8_relset_1(A_149, B_150, C_151, D_152)=k10_relat_1(C_151, D_152) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.86/1.44  tff(c_740, plain, (![D_152]: (k8_relset_1('#skF_4', '#skF_4', '#skF_4', D_152)=k10_relat_1('#skF_4', D_152))), inference(resolution, [status(thm)], [c_512, c_737])).
% 2.86/1.44  tff(c_368, plain, (k8_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_347, c_347, c_52])).
% 2.86/1.44  tff(c_514, plain, (k8_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_505, c_505, c_505, c_505, c_368])).
% 2.86/1.44  tff(c_771, plain, (k10_relat_1('#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_740, c_514])).
% 2.86/1.44  tff(c_774, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_745, c_771])).
% 2.86/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.44  
% 2.86/1.44  Inference rules
% 2.86/1.44  ----------------------
% 2.86/1.44  #Ref     : 0
% 2.86/1.44  #Sup     : 148
% 2.86/1.44  #Fact    : 0
% 2.86/1.44  #Define  : 0
% 2.86/1.44  #Split   : 6
% 2.86/1.44  #Chain   : 0
% 2.86/1.44  #Close   : 0
% 2.86/1.44  
% 2.86/1.44  Ordering : KBO
% 2.86/1.44  
% 2.86/1.44  Simplification rules
% 2.86/1.44  ----------------------
% 2.86/1.44  #Subsume      : 11
% 2.86/1.44  #Demod        : 130
% 2.86/1.44  #Tautology    : 88
% 2.86/1.44  #SimpNegUnit  : 1
% 2.86/1.44  #BackRed      : 35
% 2.86/1.44  
% 2.86/1.44  #Partial instantiations: 0
% 2.86/1.44  #Strategies tried      : 1
% 2.86/1.44  
% 2.86/1.44  Timing (in seconds)
% 2.86/1.44  ----------------------
% 2.86/1.44  Preprocessing        : 0.33
% 2.86/1.44  Parsing              : 0.18
% 2.86/1.44  CNF conversion       : 0.02
% 2.86/1.44  Main loop            : 0.32
% 2.86/1.44  Inferencing          : 0.12
% 2.86/1.44  Reduction            : 0.10
% 2.86/1.44  Demodulation         : 0.07
% 2.86/1.44  BG Simplification    : 0.02
% 2.86/1.44  Subsumption          : 0.04
% 2.86/1.44  Abstraction          : 0.01
% 2.86/1.44  MUC search           : 0.00
% 2.86/1.44  Cooper               : 0.00
% 2.86/1.44  Total                : 0.69
% 2.86/1.44  Index Insertion      : 0.00
% 2.86/1.44  Index Deletion       : 0.00
% 2.86/1.44  Index Matching       : 0.00
% 2.86/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
