%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:54 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 200 expanded)
%              Number of leaves         :   34 (  78 expanded)
%              Depth                    :    9
%              Number of atoms          :  143 ( 462 expanded)
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

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_86,axiom,(
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

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_67,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_71,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_67])).

tff(c_99,plain,(
    ! [C_43,B_44,A_45] :
      ( v5_relat_1(C_43,B_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_45,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_103,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_99])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [B_46,A_47] :
      ( k5_relat_1(B_46,k6_relat_1(A_47)) = B_46
      | ~ r1_tarski(k2_relat_1(B_46),A_47)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_111,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_relat_1(A_1)) = B_2
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_104])).

tff(c_6,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7] : k1_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_155,plain,(
    ! [A_56,B_57] :
      ( k10_relat_1(A_56,k1_relat_1(B_57)) = k1_relat_1(k5_relat_1(A_56,B_57))
      | ~ v1_relat_1(B_57)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_164,plain,(
    ! [A_56,A_7] :
      ( k1_relat_1(k5_relat_1(A_56,k6_relat_1(A_7))) = k10_relat_1(A_56,A_7)
      | ~ v1_relat_1(k6_relat_1(A_7))
      | ~ v1_relat_1(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_155])).

tff(c_169,plain,(
    ! [A_58,A_59] :
      ( k1_relat_1(k5_relat_1(A_58,k6_relat_1(A_59))) = k10_relat_1(A_58,A_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_164])).

tff(c_210,plain,(
    ! [B_62,A_63] :
      ( k10_relat_1(B_62,A_63) = k1_relat_1(B_62)
      | ~ v1_relat_1(B_62)
      | ~ v5_relat_1(B_62,A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_169])).

tff(c_213,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_103,c_210])).

tff(c_219,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_213])).

tff(c_262,plain,(
    ! [A_66,B_67,C_68,D_69] :
      ( k8_relset_1(A_66,B_67,C_68,D_69) = k10_relat_1(C_68,D_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_265,plain,(
    ! [D_69] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_69) = k10_relat_1('#skF_3',D_69) ),
    inference(resolution,[status(thm)],[c_42,c_262])).

tff(c_38,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_266,plain,(
    k10_relat_1('#skF_3','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_38])).

tff(c_267,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_266])).

tff(c_40,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_44,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_146,plain,(
    ! [A_53,B_54,C_55] :
      ( k1_relset_1(A_53,B_54,C_55) = k1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_150,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_146])).

tff(c_287,plain,(
    ! [B_80,A_81,C_82] :
      ( k1_xboole_0 = B_80
      | k1_relset_1(A_81,B_80,C_82) = A_81
      | ~ v1_funct_2(C_82,A_81,B_80)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_290,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_287])).

tff(c_293,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_150,c_290])).

tff(c_295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_267,c_48,c_293])).

tff(c_296,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_297,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_302,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_297])).

tff(c_327,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_42])).

tff(c_328,plain,(
    ! [C_85,A_86,B_87] :
      ( v1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_332,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_327,c_328])).

tff(c_338,plain,(
    ! [C_91,B_92,A_93] :
      ( v5_relat_1(C_91,B_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_342,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_327,c_338])).

tff(c_365,plain,(
    ! [B_102,A_103] :
      ( k5_relat_1(B_102,k6_relat_1(A_103)) = B_102
      | ~ r1_tarski(k2_relat_1(B_102),A_103)
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_372,plain,(
    ! [B_2,A_1] :
      ( k5_relat_1(B_2,k6_relat_1(A_1)) = B_2
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_365])).

tff(c_417,plain,(
    ! [A_112,B_113] :
      ( k10_relat_1(A_112,k1_relat_1(B_113)) = k1_relat_1(k5_relat_1(A_112,B_113))
      | ~ v1_relat_1(B_113)
      | ~ v1_relat_1(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_426,plain,(
    ! [A_112,A_7] :
      ( k1_relat_1(k5_relat_1(A_112,k6_relat_1(A_7))) = k10_relat_1(A_112,A_7)
      | ~ v1_relat_1(k6_relat_1(A_7))
      | ~ v1_relat_1(A_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_417])).

tff(c_431,plain,(
    ! [A_114,A_115] :
      ( k1_relat_1(k5_relat_1(A_114,k6_relat_1(A_115))) = k10_relat_1(A_114,A_115)
      | ~ v1_relat_1(A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_426])).

tff(c_495,plain,(
    ! [B_125,A_126] :
      ( k10_relat_1(B_125,A_126) = k1_relat_1(B_125)
      | ~ v1_relat_1(B_125)
      | ~ v5_relat_1(B_125,A_126)
      | ~ v1_relat_1(B_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_431])).

tff(c_501,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_342,c_495])).

tff(c_507,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_501])).

tff(c_451,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( k8_relset_1(A_116,B_117,C_118,D_119) = k10_relat_1(C_118,D_119)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_454,plain,(
    ! [D_119] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_119) = k10_relat_1('#skF_3',D_119) ),
    inference(resolution,[status(thm)],[c_327,c_451])).

tff(c_326,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_302,c_38])).

tff(c_455,plain,(
    k10_relat_1('#skF_3','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_326])).

tff(c_508,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_455])).

tff(c_316,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_44])).

tff(c_384,plain,(
    ! [A_106,B_107,C_108] :
      ( k1_relset_1(A_106,B_107,C_108) = k1_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_388,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_327,c_384])).

tff(c_34,plain,(
    ! [B_24,C_25] :
      ( k1_relset_1(k1_xboole_0,B_24,C_25) = k1_xboole_0
      | ~ v1_funct_2(C_25,k1_xboole_0,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_549,plain,(
    ! [B_129,C_130] :
      ( k1_relset_1('#skF_1',B_129,C_130) = '#skF_1'
      | ~ v1_funct_2(C_130,'#skF_1',B_129)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_129))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_296,c_296,c_296,c_34])).

tff(c_552,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_327,c_549])).

tff(c_555,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_388,c_552])).

tff(c_557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_508,c_555])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:33:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.37  
% 2.58/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.37  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.58/1.37  
% 2.58/1.37  %Foreground sorts:
% 2.58/1.37  
% 2.58/1.37  
% 2.58/1.37  %Background operators:
% 2.58/1.37  
% 2.58/1.37  
% 2.58/1.37  %Foreground operators:
% 2.58/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.58/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.37  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.58/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.58/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.58/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.58/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.58/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.58/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.58/1.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.58/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.58/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.37  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.58/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.58/1.37  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.58/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.58/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.58/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.58/1.37  
% 2.58/1.39  tff(f_99, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 2.58/1.39  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.58/1.39  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.58/1.39  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.58/1.39  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.58/1.39  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.58/1.39  tff(f_44, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.58/1.39  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.58/1.39  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.58/1.39  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.58/1.39  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.58/1.39  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.58/1.39  tff(c_67, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.58/1.39  tff(c_71, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_67])).
% 2.58/1.39  tff(c_99, plain, (![C_43, B_44, A_45]: (v5_relat_1(C_43, B_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_45, B_44))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.58/1.39  tff(c_103, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_99])).
% 2.58/1.39  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.39  tff(c_104, plain, (![B_46, A_47]: (k5_relat_1(B_46, k6_relat_1(A_47))=B_46 | ~r1_tarski(k2_relat_1(B_46), A_47) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.58/1.39  tff(c_111, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_relat_1(A_1))=B_2 | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_104])).
% 2.58/1.39  tff(c_6, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.58/1.39  tff(c_10, plain, (![A_7]: (k1_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.58/1.39  tff(c_155, plain, (![A_56, B_57]: (k10_relat_1(A_56, k1_relat_1(B_57))=k1_relat_1(k5_relat_1(A_56, B_57)) | ~v1_relat_1(B_57) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.58/1.39  tff(c_164, plain, (![A_56, A_7]: (k1_relat_1(k5_relat_1(A_56, k6_relat_1(A_7)))=k10_relat_1(A_56, A_7) | ~v1_relat_1(k6_relat_1(A_7)) | ~v1_relat_1(A_56))), inference(superposition, [status(thm), theory('equality')], [c_10, c_155])).
% 2.58/1.39  tff(c_169, plain, (![A_58, A_59]: (k1_relat_1(k5_relat_1(A_58, k6_relat_1(A_59)))=k10_relat_1(A_58, A_59) | ~v1_relat_1(A_58))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_164])).
% 2.58/1.39  tff(c_210, plain, (![B_62, A_63]: (k10_relat_1(B_62, A_63)=k1_relat_1(B_62) | ~v1_relat_1(B_62) | ~v5_relat_1(B_62, A_63) | ~v1_relat_1(B_62))), inference(superposition, [status(thm), theory('equality')], [c_111, c_169])).
% 2.58/1.39  tff(c_213, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_103, c_210])).
% 2.58/1.39  tff(c_219, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_71, c_213])).
% 2.58/1.39  tff(c_262, plain, (![A_66, B_67, C_68, D_69]: (k8_relset_1(A_66, B_67, C_68, D_69)=k10_relat_1(C_68, D_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.58/1.39  tff(c_265, plain, (![D_69]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_69)=k10_relat_1('#skF_3', D_69))), inference(resolution, [status(thm)], [c_42, c_262])).
% 2.58/1.39  tff(c_38, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.58/1.39  tff(c_266, plain, (k10_relat_1('#skF_3', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_265, c_38])).
% 2.58/1.39  tff(c_267, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_219, c_266])).
% 2.58/1.39  tff(c_40, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.58/1.39  tff(c_48, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_40])).
% 2.58/1.39  tff(c_44, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.58/1.39  tff(c_146, plain, (![A_53, B_54, C_55]: (k1_relset_1(A_53, B_54, C_55)=k1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.58/1.39  tff(c_150, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_146])).
% 2.58/1.39  tff(c_287, plain, (![B_80, A_81, C_82]: (k1_xboole_0=B_80 | k1_relset_1(A_81, B_80, C_82)=A_81 | ~v1_funct_2(C_82, A_81, B_80) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.58/1.39  tff(c_290, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_287])).
% 2.58/1.39  tff(c_293, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_150, c_290])).
% 2.58/1.39  tff(c_295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_267, c_48, c_293])).
% 2.58/1.39  tff(c_296, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_40])).
% 2.58/1.39  tff(c_297, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_40])).
% 2.58/1.39  tff(c_302, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_296, c_297])).
% 2.58/1.39  tff(c_327, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_302, c_42])).
% 2.58/1.39  tff(c_328, plain, (![C_85, A_86, B_87]: (v1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.58/1.39  tff(c_332, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_327, c_328])).
% 2.58/1.39  tff(c_338, plain, (![C_91, B_92, A_93]: (v5_relat_1(C_91, B_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.58/1.39  tff(c_342, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_327, c_338])).
% 2.58/1.39  tff(c_365, plain, (![B_102, A_103]: (k5_relat_1(B_102, k6_relat_1(A_103))=B_102 | ~r1_tarski(k2_relat_1(B_102), A_103) | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.58/1.39  tff(c_372, plain, (![B_2, A_1]: (k5_relat_1(B_2, k6_relat_1(A_1))=B_2 | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_365])).
% 2.58/1.39  tff(c_417, plain, (![A_112, B_113]: (k10_relat_1(A_112, k1_relat_1(B_113))=k1_relat_1(k5_relat_1(A_112, B_113)) | ~v1_relat_1(B_113) | ~v1_relat_1(A_112))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.58/1.39  tff(c_426, plain, (![A_112, A_7]: (k1_relat_1(k5_relat_1(A_112, k6_relat_1(A_7)))=k10_relat_1(A_112, A_7) | ~v1_relat_1(k6_relat_1(A_7)) | ~v1_relat_1(A_112))), inference(superposition, [status(thm), theory('equality')], [c_10, c_417])).
% 2.58/1.39  tff(c_431, plain, (![A_114, A_115]: (k1_relat_1(k5_relat_1(A_114, k6_relat_1(A_115)))=k10_relat_1(A_114, A_115) | ~v1_relat_1(A_114))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_426])).
% 2.58/1.39  tff(c_495, plain, (![B_125, A_126]: (k10_relat_1(B_125, A_126)=k1_relat_1(B_125) | ~v1_relat_1(B_125) | ~v5_relat_1(B_125, A_126) | ~v1_relat_1(B_125))), inference(superposition, [status(thm), theory('equality')], [c_372, c_431])).
% 2.58/1.39  tff(c_501, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_342, c_495])).
% 2.58/1.39  tff(c_507, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_332, c_501])).
% 2.58/1.39  tff(c_451, plain, (![A_116, B_117, C_118, D_119]: (k8_relset_1(A_116, B_117, C_118, D_119)=k10_relat_1(C_118, D_119) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.58/1.39  tff(c_454, plain, (![D_119]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_119)=k10_relat_1('#skF_3', D_119))), inference(resolution, [status(thm)], [c_327, c_451])).
% 2.58/1.39  tff(c_326, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_302, c_302, c_38])).
% 2.58/1.39  tff(c_455, plain, (k10_relat_1('#skF_3', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_454, c_326])).
% 2.58/1.39  tff(c_508, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_507, c_455])).
% 2.58/1.39  tff(c_316, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_302, c_44])).
% 2.58/1.39  tff(c_384, plain, (![A_106, B_107, C_108]: (k1_relset_1(A_106, B_107, C_108)=k1_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.58/1.39  tff(c_388, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_327, c_384])).
% 2.58/1.39  tff(c_34, plain, (![B_24, C_25]: (k1_relset_1(k1_xboole_0, B_24, C_25)=k1_xboole_0 | ~v1_funct_2(C_25, k1_xboole_0, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_24))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.58/1.39  tff(c_549, plain, (![B_129, C_130]: (k1_relset_1('#skF_1', B_129, C_130)='#skF_1' | ~v1_funct_2(C_130, '#skF_1', B_129) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_129))))), inference(demodulation, [status(thm), theory('equality')], [c_296, c_296, c_296, c_296, c_34])).
% 2.58/1.39  tff(c_552, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_327, c_549])).
% 2.58/1.39  tff(c_555, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_316, c_388, c_552])).
% 2.58/1.39  tff(c_557, plain, $false, inference(negUnitSimplification, [status(thm)], [c_508, c_555])).
% 2.58/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.39  
% 2.58/1.39  Inference rules
% 2.58/1.39  ----------------------
% 2.58/1.39  #Ref     : 0
% 2.58/1.39  #Sup     : 104
% 2.58/1.39  #Fact    : 0
% 2.58/1.39  #Define  : 0
% 2.58/1.39  #Split   : 1
% 2.58/1.39  #Chain   : 0
% 2.58/1.39  #Close   : 0
% 2.58/1.39  
% 2.58/1.39  Ordering : KBO
% 2.58/1.39  
% 2.58/1.39  Simplification rules
% 2.58/1.39  ----------------------
% 2.58/1.39  #Subsume      : 9
% 2.58/1.39  #Demod        : 81
% 2.58/1.39  #Tautology    : 61
% 2.58/1.39  #SimpNegUnit  : 3
% 2.58/1.39  #BackRed      : 3
% 2.58/1.39  
% 2.58/1.39  #Partial instantiations: 0
% 2.58/1.39  #Strategies tried      : 1
% 2.58/1.39  
% 2.58/1.39  Timing (in seconds)
% 2.58/1.39  ----------------------
% 2.58/1.40  Preprocessing        : 0.34
% 2.58/1.40  Parsing              : 0.18
% 2.58/1.40  CNF conversion       : 0.02
% 2.58/1.40  Main loop            : 0.28
% 2.89/1.40  Inferencing          : 0.11
% 2.89/1.40  Reduction            : 0.09
% 2.89/1.40  Demodulation         : 0.06
% 2.89/1.40  BG Simplification    : 0.02
% 2.89/1.40  Subsumption          : 0.04
% 2.89/1.40  Abstraction          : 0.01
% 2.89/1.40  MUC search           : 0.00
% 2.89/1.40  Cooper               : 0.00
% 2.89/1.40  Total                : 0.66
% 2.89/1.40  Index Insertion      : 0.00
% 2.89/1.40  Index Deletion       : 0.00
% 2.89/1.40  Index Matching       : 0.00
% 2.89/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
