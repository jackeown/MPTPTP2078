%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:54 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 200 expanded)
%              Number of leaves         :   34 (  78 expanded)
%              Depth                    :    9
%              Number of atoms          :  144 ( 464 expanded)
%              Number of equality atoms :   62 ( 243 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_88,axiom,(
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

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_70,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_74,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_70])).

tff(c_92,plain,(
    ! [C_39,B_40,A_41] :
      ( v5_relat_1(C_39,B_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_41,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_96,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_92])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [B_47,A_48] :
      ( k5_relat_1(B_47,k6_relat_1(A_48)) = B_47
      | ~ r1_tarski(k2_relat_1(B_47),A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_114,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_relat_1(A_1)) = B_2
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_107])).

tff(c_14,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_6] : k1_relat_1(k6_relat_1(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_148,plain,(
    ! [A_53,B_54] :
      ( k10_relat_1(A_53,k1_relat_1(B_54)) = k1_relat_1(k5_relat_1(A_53,B_54))
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_157,plain,(
    ! [A_53,A_6] :
      ( k1_relat_1(k5_relat_1(A_53,k6_relat_1(A_6))) = k10_relat_1(A_53,A_6)
      | ~ v1_relat_1(k6_relat_1(A_6))
      | ~ v1_relat_1(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_148])).

tff(c_162,plain,(
    ! [A_55,A_56] :
      ( k1_relat_1(k5_relat_1(A_55,k6_relat_1(A_56))) = k10_relat_1(A_55,A_56)
      | ~ v1_relat_1(A_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_157])).

tff(c_214,plain,(
    ! [B_65,A_66] :
      ( k10_relat_1(B_65,A_66) = k1_relat_1(B_65)
      | ~ v1_relat_1(B_65)
      | ~ v5_relat_1(B_65,A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_162])).

tff(c_220,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_96,c_214])).

tff(c_226,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_220])).

tff(c_266,plain,(
    ! [A_69,B_70,C_71,D_72] :
      ( k8_relset_1(A_69,B_70,C_71,D_72) = k10_relat_1(C_71,D_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_269,plain,(
    ! [D_72] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_72) = k10_relat_1('#skF_3',D_72) ),
    inference(resolution,[status(thm)],[c_44,c_266])).

tff(c_40,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_271,plain,(
    k10_relat_1('#skF_3','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_40])).

tff(c_272,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_271])).

tff(c_42,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_51,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_46,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_182,plain,(
    ! [A_57,B_58,C_59] :
      ( k1_relset_1(A_57,B_58,C_59) = k1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_186,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_182])).

tff(c_283,plain,(
    ! [B_78,A_79,C_80] :
      ( k1_xboole_0 = B_78
      | k1_relset_1(A_79,B_78,C_80) = A_79
      | ~ v1_funct_2(C_80,A_79,B_78)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_286,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_283])).

tff(c_289,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_186,c_286])).

tff(c_291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_51,c_289])).

tff(c_292,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_293,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_298,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_293])).

tff(c_323,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_44])).

tff(c_324,plain,(
    ! [C_83,A_84,B_85] :
      ( v1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_328,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_323,c_324])).

tff(c_341,plain,(
    ! [C_93,B_94,A_95] :
      ( v5_relat_1(C_93,B_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_345,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_323,c_341])).

tff(c_361,plain,(
    ! [B_100,A_101] :
      ( k5_relat_1(B_100,k6_relat_1(A_101)) = B_100
      | ~ r1_tarski(k2_relat_1(B_100),A_101)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_368,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_relat_1(A_1)) = B_2
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_361])).

tff(c_411,plain,(
    ! [A_109,B_110] :
      ( k10_relat_1(A_109,k1_relat_1(B_110)) = k1_relat_1(k5_relat_1(A_109,B_110))
      | ~ v1_relat_1(B_110)
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_420,plain,(
    ! [A_109,A_6] :
      ( k1_relat_1(k5_relat_1(A_109,k6_relat_1(A_6))) = k10_relat_1(A_109,A_6)
      | ~ v1_relat_1(k6_relat_1(A_6))
      | ~ v1_relat_1(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_411])).

tff(c_425,plain,(
    ! [A_111,A_112] :
      ( k1_relat_1(k5_relat_1(A_111,k6_relat_1(A_112))) = k10_relat_1(A_111,A_112)
      | ~ v1_relat_1(A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_420])).

tff(c_468,plain,(
    ! [B_116,A_117] :
      ( k10_relat_1(B_116,A_117) = k1_relat_1(B_116)
      | ~ v1_relat_1(B_116)
      | ~ v5_relat_1(B_116,A_117)
      | ~ v1_relat_1(B_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_425])).

tff(c_471,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_345,c_468])).

tff(c_477,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_471])).

tff(c_529,plain,(
    ! [A_122,B_123,C_124,D_125] :
      ( k8_relset_1(A_122,B_123,C_124,D_125) = k10_relat_1(C_124,D_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_532,plain,(
    ! [D_125] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_125) = k10_relat_1('#skF_3',D_125) ),
    inference(resolution,[status(thm)],[c_323,c_529])).

tff(c_322,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_298,c_40])).

tff(c_533,plain,(
    k10_relat_1('#skF_3','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_322])).

tff(c_534,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_533])).

tff(c_303,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_46])).

tff(c_380,plain,(
    ! [A_104,B_105,C_106] :
      ( k1_relset_1(A_104,B_105,C_106) = k1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_384,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_323,c_380])).

tff(c_36,plain,(
    ! [B_24,C_25] :
      ( k1_relset_1(k1_xboole_0,B_24,C_25) = k1_xboole_0
      | ~ v1_funct_2(C_25,k1_xboole_0,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_545,plain,(
    ! [B_127,C_128] :
      ( k1_relset_1('#skF_1',B_127,C_128) = '#skF_1'
      | ~ v1_funct_2(C_128,'#skF_1',B_127)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_127))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_292,c_292,c_292,c_292,c_36])).

tff(c_548,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_323,c_545])).

tff(c_551,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_384,c_548])).

tff(c_553,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_534,c_551])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:19:02 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.36  
% 2.54/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.36  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.54/1.36  
% 2.54/1.36  %Foreground sorts:
% 2.54/1.36  
% 2.54/1.36  
% 2.54/1.36  %Background operators:
% 2.54/1.36  
% 2.54/1.36  
% 2.54/1.36  %Foreground operators:
% 2.54/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.54/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.36  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.54/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.54/1.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.54/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.54/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.54/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.54/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.54/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.54/1.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.54/1.36  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.54/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.36  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.54/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.54/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.54/1.36  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.54/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.36  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.54/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.54/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.36  
% 2.54/1.38  tff(f_101, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 2.54/1.38  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.54/1.38  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.54/1.38  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.54/1.38  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.54/1.38  tff(f_52, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.54/1.38  tff(f_42, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.54/1.38  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.54/1.38  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.54/1.38  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.54/1.38  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.54/1.38  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.54/1.38  tff(c_70, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.54/1.38  tff(c_74, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_70])).
% 2.54/1.38  tff(c_92, plain, (![C_39, B_40, A_41]: (v5_relat_1(C_39, B_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_41, B_40))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.54/1.38  tff(c_96, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_92])).
% 2.54/1.38  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.54/1.38  tff(c_107, plain, (![B_47, A_48]: (k5_relat_1(B_47, k6_relat_1(A_48))=B_47 | ~r1_tarski(k2_relat_1(B_47), A_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.54/1.38  tff(c_114, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_relat_1(A_1))=B_2 | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_107])).
% 2.54/1.38  tff(c_14, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.54/1.38  tff(c_8, plain, (![A_6]: (k1_relat_1(k6_relat_1(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.54/1.38  tff(c_148, plain, (![A_53, B_54]: (k10_relat_1(A_53, k1_relat_1(B_54))=k1_relat_1(k5_relat_1(A_53, B_54)) | ~v1_relat_1(B_54) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.54/1.38  tff(c_157, plain, (![A_53, A_6]: (k1_relat_1(k5_relat_1(A_53, k6_relat_1(A_6)))=k10_relat_1(A_53, A_6) | ~v1_relat_1(k6_relat_1(A_6)) | ~v1_relat_1(A_53))), inference(superposition, [status(thm), theory('equality')], [c_8, c_148])).
% 2.54/1.38  tff(c_162, plain, (![A_55, A_56]: (k1_relat_1(k5_relat_1(A_55, k6_relat_1(A_56)))=k10_relat_1(A_55, A_56) | ~v1_relat_1(A_55))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_157])).
% 2.54/1.38  tff(c_214, plain, (![B_65, A_66]: (k10_relat_1(B_65, A_66)=k1_relat_1(B_65) | ~v1_relat_1(B_65) | ~v5_relat_1(B_65, A_66) | ~v1_relat_1(B_65))), inference(superposition, [status(thm), theory('equality')], [c_114, c_162])).
% 2.54/1.38  tff(c_220, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_96, c_214])).
% 2.54/1.38  tff(c_226, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_220])).
% 2.54/1.38  tff(c_266, plain, (![A_69, B_70, C_71, D_72]: (k8_relset_1(A_69, B_70, C_71, D_72)=k10_relat_1(C_71, D_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.54/1.38  tff(c_269, plain, (![D_72]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_72)=k10_relat_1('#skF_3', D_72))), inference(resolution, [status(thm)], [c_44, c_266])).
% 2.54/1.38  tff(c_40, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.54/1.38  tff(c_271, plain, (k10_relat_1('#skF_3', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_269, c_40])).
% 2.54/1.38  tff(c_272, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_226, c_271])).
% 2.54/1.38  tff(c_42, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.54/1.38  tff(c_51, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_42])).
% 2.54/1.38  tff(c_46, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.54/1.38  tff(c_182, plain, (![A_57, B_58, C_59]: (k1_relset_1(A_57, B_58, C_59)=k1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.54/1.38  tff(c_186, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_182])).
% 2.54/1.38  tff(c_283, plain, (![B_78, A_79, C_80]: (k1_xboole_0=B_78 | k1_relset_1(A_79, B_78, C_80)=A_79 | ~v1_funct_2(C_80, A_79, B_78) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.54/1.38  tff(c_286, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_283])).
% 2.54/1.38  tff(c_289, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_186, c_286])).
% 2.54/1.38  tff(c_291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_272, c_51, c_289])).
% 2.54/1.38  tff(c_292, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_42])).
% 2.54/1.38  tff(c_293, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_42])).
% 2.54/1.38  tff(c_298, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_292, c_293])).
% 2.54/1.38  tff(c_323, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_298, c_44])).
% 2.54/1.38  tff(c_324, plain, (![C_83, A_84, B_85]: (v1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.54/1.38  tff(c_328, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_323, c_324])).
% 2.54/1.38  tff(c_341, plain, (![C_93, B_94, A_95]: (v5_relat_1(C_93, B_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.54/1.38  tff(c_345, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_323, c_341])).
% 2.54/1.38  tff(c_361, plain, (![B_100, A_101]: (k5_relat_1(B_100, k6_relat_1(A_101))=B_100 | ~r1_tarski(k2_relat_1(B_100), A_101) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.54/1.38  tff(c_368, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_relat_1(A_1))=B_2 | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_361])).
% 2.54/1.38  tff(c_411, plain, (![A_109, B_110]: (k10_relat_1(A_109, k1_relat_1(B_110))=k1_relat_1(k5_relat_1(A_109, B_110)) | ~v1_relat_1(B_110) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.54/1.38  tff(c_420, plain, (![A_109, A_6]: (k1_relat_1(k5_relat_1(A_109, k6_relat_1(A_6)))=k10_relat_1(A_109, A_6) | ~v1_relat_1(k6_relat_1(A_6)) | ~v1_relat_1(A_109))), inference(superposition, [status(thm), theory('equality')], [c_8, c_411])).
% 2.54/1.38  tff(c_425, plain, (![A_111, A_112]: (k1_relat_1(k5_relat_1(A_111, k6_relat_1(A_112)))=k10_relat_1(A_111, A_112) | ~v1_relat_1(A_111))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_420])).
% 2.54/1.38  tff(c_468, plain, (![B_116, A_117]: (k10_relat_1(B_116, A_117)=k1_relat_1(B_116) | ~v1_relat_1(B_116) | ~v5_relat_1(B_116, A_117) | ~v1_relat_1(B_116))), inference(superposition, [status(thm), theory('equality')], [c_368, c_425])).
% 2.54/1.38  tff(c_471, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_345, c_468])).
% 2.54/1.38  tff(c_477, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_328, c_471])).
% 2.54/1.38  tff(c_529, plain, (![A_122, B_123, C_124, D_125]: (k8_relset_1(A_122, B_123, C_124, D_125)=k10_relat_1(C_124, D_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.54/1.38  tff(c_532, plain, (![D_125]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_125)=k10_relat_1('#skF_3', D_125))), inference(resolution, [status(thm)], [c_323, c_529])).
% 2.54/1.38  tff(c_322, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_298, c_298, c_40])).
% 2.54/1.38  tff(c_533, plain, (k10_relat_1('#skF_3', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_532, c_322])).
% 2.54/1.38  tff(c_534, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_477, c_533])).
% 2.54/1.38  tff(c_303, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_298, c_46])).
% 2.54/1.38  tff(c_380, plain, (![A_104, B_105, C_106]: (k1_relset_1(A_104, B_105, C_106)=k1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.54/1.38  tff(c_384, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_323, c_380])).
% 2.54/1.38  tff(c_36, plain, (![B_24, C_25]: (k1_relset_1(k1_xboole_0, B_24, C_25)=k1_xboole_0 | ~v1_funct_2(C_25, k1_xboole_0, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_24))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.54/1.38  tff(c_545, plain, (![B_127, C_128]: (k1_relset_1('#skF_1', B_127, C_128)='#skF_1' | ~v1_funct_2(C_128, '#skF_1', B_127) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_127))))), inference(demodulation, [status(thm), theory('equality')], [c_292, c_292, c_292, c_292, c_36])).
% 2.54/1.38  tff(c_548, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_323, c_545])).
% 2.54/1.38  tff(c_551, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_303, c_384, c_548])).
% 2.54/1.38  tff(c_553, plain, $false, inference(negUnitSimplification, [status(thm)], [c_534, c_551])).
% 2.54/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.38  
% 2.54/1.38  Inference rules
% 2.54/1.38  ----------------------
% 2.54/1.38  #Ref     : 0
% 2.54/1.38  #Sup     : 103
% 2.54/1.38  #Fact    : 0
% 2.54/1.38  #Define  : 0
% 2.54/1.38  #Split   : 1
% 2.54/1.38  #Chain   : 0
% 2.54/1.38  #Close   : 0
% 2.54/1.38  
% 2.54/1.38  Ordering : KBO
% 2.54/1.38  
% 2.54/1.38  Simplification rules
% 2.54/1.38  ----------------------
% 2.54/1.38  #Subsume      : 8
% 2.54/1.38  #Demod        : 79
% 2.54/1.38  #Tautology    : 61
% 2.54/1.38  #SimpNegUnit  : 2
% 2.54/1.38  #BackRed      : 2
% 2.54/1.38  
% 2.54/1.38  #Partial instantiations: 0
% 2.54/1.38  #Strategies tried      : 1
% 2.54/1.38  
% 2.54/1.38  Timing (in seconds)
% 2.54/1.38  ----------------------
% 2.54/1.39  Preprocessing        : 0.32
% 2.54/1.39  Parsing              : 0.17
% 2.54/1.39  CNF conversion       : 0.02
% 2.54/1.39  Main loop            : 0.27
% 2.54/1.39  Inferencing          : 0.11
% 2.54/1.39  Reduction            : 0.08
% 2.54/1.39  Demodulation         : 0.06
% 2.54/1.39  BG Simplification    : 0.02
% 2.54/1.39  Subsumption          : 0.04
% 2.54/1.39  Abstraction          : 0.01
% 2.54/1.39  MUC search           : 0.00
% 2.54/1.39  Cooper               : 0.00
% 2.54/1.39  Total                : 0.63
% 2.54/1.39  Index Insertion      : 0.00
% 2.54/1.39  Index Deletion       : 0.00
% 2.54/1.39  Index Matching       : 0.00
% 2.54/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
