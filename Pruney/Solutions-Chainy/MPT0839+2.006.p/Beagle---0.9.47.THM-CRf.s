%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:22 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 214 expanded)
%              Number of leaves         :   39 (  89 expanded)
%              Depth                    :   14
%              Number of atoms          :  135 ( 392 expanded)
%              Number of equality atoms :   31 (  80 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_38,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_516,plain,(
    ! [A_122,B_123,C_124] :
      ( k2_relset_1(A_122,B_123,C_124) = k2_relat_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_525,plain,(
    k2_relset_1('#skF_5','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_516])).

tff(c_10,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_51,plain,(
    ! [A_44] :
      ( k1_xboole_0 = A_44
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_59,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_10,c_51])).

tff(c_44,plain,(
    k2_relset_1('#skF_5','#skF_4','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_66,plain,(
    k2_relset_1('#skF_5','#skF_4','#skF_6') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_44])).

tff(c_526,plain,(
    k2_relat_1('#skF_6') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_66])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_108,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_99])).

tff(c_214,plain,(
    ! [A_85,B_86,C_87] :
      ( k2_relset_1(A_85,B_86,C_87) = k2_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_223,plain,(
    k2_relset_1('#skF_5','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_214])).

tff(c_224,plain,(
    k2_relat_1('#skF_6') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_66])).

tff(c_130,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_relat_1(C_61,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_139,plain,(
    v4_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_130])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v4_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_184,plain,(
    ! [A_77,C_78,B_79] :
      ( m1_subset_1(A_77,C_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(C_78))
      | ~ r2_hidden(A_77,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_229,plain,(
    ! [A_88,B_89,A_90] :
      ( m1_subset_1(A_88,B_89)
      | ~ r2_hidden(A_88,A_90)
      | ~ r1_tarski(A_90,B_89) ) ),
    inference(resolution,[status(thm)],[c_14,c_184])).

tff(c_233,plain,(
    ! [A_91,B_92] :
      ( m1_subset_1('#skF_1'(A_91),B_92)
      | ~ r1_tarski(A_91,B_92)
      | v1_xboole_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_4,c_229])).

tff(c_192,plain,(
    ! [A_81,B_82,C_83] :
      ( k1_relset_1(A_81,B_82,C_83) = k1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_201,plain,(
    k1_relset_1('#skF_5','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_192])).

tff(c_109,plain,(
    ! [D_56] :
      ( ~ r2_hidden(D_56,k1_relset_1('#skF_5','#skF_4','#skF_6'))
      | ~ m1_subset_1(D_56,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_114,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_5','#skF_4','#skF_6')),'#skF_5')
    | v1_xboole_0(k1_relset_1('#skF_5','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_4,c_109])).

tff(c_162,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_5','#skF_4','#skF_6')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_202,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_162])).

tff(c_265,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_5')
    | v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_233,c_202])).

tff(c_272,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_265])).

tff(c_288,plain,
    ( ~ v4_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_272])).

tff(c_292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_139,c_288])).

tff(c_293,plain,(
    v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_265])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_67,plain,(
    ! [A_5] :
      ( A_5 = '#skF_2'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_8])).

tff(c_298,plain,(
    k1_relat_1('#skF_6') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_293,c_67])).

tff(c_30,plain,(
    ! [A_19] :
      ( k9_relat_1(A_19,k1_relat_1(A_19)) = k2_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_313,plain,
    ( k9_relat_1('#skF_6','#skF_2') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_30])).

tff(c_321,plain,(
    k9_relat_1('#skF_6','#skF_2') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_313])).

tff(c_346,plain,(
    ! [A_98,B_99,C_100] :
      ( r2_hidden('#skF_3'(A_98,B_99,C_100),B_99)
      | ~ r2_hidden(A_98,k9_relat_1(C_100,B_99))
      | ~ v1_relat_1(C_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_369,plain,(
    ! [B_102,A_103,C_104] :
      ( ~ v1_xboole_0(B_102)
      | ~ r2_hidden(A_103,k9_relat_1(C_104,B_102))
      | ~ v1_relat_1(C_104) ) ),
    inference(resolution,[status(thm)],[c_346,c_2])).

tff(c_376,plain,(
    ! [A_103] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_103,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_369])).

tff(c_388,plain,(
    ! [A_105] : ~ r2_hidden(A_105,k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_10,c_376])).

tff(c_398,plain,(
    v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_4,c_388])).

tff(c_417,plain,(
    k2_relat_1('#skF_6') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_398,c_67])).

tff(c_421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_417])).

tff(c_422,plain,(
    v1_xboole_0(k1_relset_1('#skF_5','#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_427,plain,(
    k1_relset_1('#skF_5','#skF_4','#skF_6') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_422,c_67])).

tff(c_472,plain,(
    ! [A_117,B_118,C_119] :
      ( k1_relset_1(A_117,B_118,C_119) = k1_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_479,plain,(
    k1_relset_1('#skF_5','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_472])).

tff(c_482,plain,(
    k1_relat_1('#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_479])).

tff(c_492,plain,
    ( k9_relat_1('#skF_6','#skF_2') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_30])).

tff(c_500,plain,(
    k9_relat_1('#skF_6','#skF_2') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_492])).

tff(c_535,plain,(
    ! [A_128,B_129,C_130] :
      ( r2_hidden('#skF_3'(A_128,B_129,C_130),B_129)
      | ~ r2_hidden(A_128,k9_relat_1(C_130,B_129))
      | ~ v1_relat_1(C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_548,plain,(
    ! [B_131,A_132,C_133] :
      ( ~ v1_xboole_0(B_131)
      | ~ r2_hidden(A_132,k9_relat_1(C_133,B_131))
      | ~ v1_relat_1(C_133) ) ),
    inference(resolution,[status(thm)],[c_535,c_2])).

tff(c_555,plain,(
    ! [A_132] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_132,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_548])).

tff(c_567,plain,(
    ! [A_134] : ~ r2_hidden(A_134,k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_10,c_555])).

tff(c_577,plain,(
    v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_4,c_567])).

tff(c_580,plain,(
    k2_relat_1('#skF_6') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_577,c_67])).

tff(c_584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_526,c_580])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:45:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.32  
% 2.47/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.32  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.47/1.32  
% 2.47/1.32  %Foreground sorts:
% 2.47/1.32  
% 2.47/1.32  
% 2.47/1.32  %Background operators:
% 2.47/1.32  
% 2.47/1.32  
% 2.47/1.32  %Foreground operators:
% 2.47/1.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.47/1.32  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.47/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.47/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.47/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.47/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.47/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.47/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.47/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.47/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.47/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.47/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.47/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.47/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.47/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.32  
% 2.47/1.34  tff(f_108, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relset_1)).
% 2.47/1.34  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.47/1.34  tff(f_38, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.47/1.34  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.47/1.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.47/1.34  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.47/1.34  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.47/1.34  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.47/1.34  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.47/1.34  tff(f_48, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.47/1.34  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.47/1.34  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.47/1.34  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 2.47/1.34  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.47/1.34  tff(c_516, plain, (![A_122, B_123, C_124]: (k2_relset_1(A_122, B_123, C_124)=k2_relat_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.47/1.34  tff(c_525, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_516])).
% 2.47/1.34  tff(c_10, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.47/1.34  tff(c_51, plain, (![A_44]: (k1_xboole_0=A_44 | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.47/1.34  tff(c_59, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_10, c_51])).
% 2.47/1.34  tff(c_44, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.47/1.34  tff(c_66, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_6')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_44])).
% 2.47/1.34  tff(c_526, plain, (k2_relat_1('#skF_6')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_525, c_66])).
% 2.47/1.34  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.34  tff(c_99, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.47/1.34  tff(c_108, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_99])).
% 2.47/1.34  tff(c_214, plain, (![A_85, B_86, C_87]: (k2_relset_1(A_85, B_86, C_87)=k2_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.47/1.34  tff(c_223, plain, (k2_relset_1('#skF_5', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_214])).
% 2.47/1.34  tff(c_224, plain, (k2_relat_1('#skF_6')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_223, c_66])).
% 2.47/1.34  tff(c_130, plain, (![C_61, A_62, B_63]: (v4_relat_1(C_61, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.47/1.34  tff(c_139, plain, (v4_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_130])).
% 2.47/1.34  tff(c_20, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(B_12), A_11) | ~v4_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.47/1.34  tff(c_14, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.47/1.34  tff(c_184, plain, (![A_77, C_78, B_79]: (m1_subset_1(A_77, C_78) | ~m1_subset_1(B_79, k1_zfmisc_1(C_78)) | ~r2_hidden(A_77, B_79))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.47/1.34  tff(c_229, plain, (![A_88, B_89, A_90]: (m1_subset_1(A_88, B_89) | ~r2_hidden(A_88, A_90) | ~r1_tarski(A_90, B_89))), inference(resolution, [status(thm)], [c_14, c_184])).
% 2.47/1.34  tff(c_233, plain, (![A_91, B_92]: (m1_subset_1('#skF_1'(A_91), B_92) | ~r1_tarski(A_91, B_92) | v1_xboole_0(A_91))), inference(resolution, [status(thm)], [c_4, c_229])).
% 2.47/1.34  tff(c_192, plain, (![A_81, B_82, C_83]: (k1_relset_1(A_81, B_82, C_83)=k1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.47/1.34  tff(c_201, plain, (k1_relset_1('#skF_5', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_192])).
% 2.47/1.34  tff(c_109, plain, (![D_56]: (~r2_hidden(D_56, k1_relset_1('#skF_5', '#skF_4', '#skF_6')) | ~m1_subset_1(D_56, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.47/1.34  tff(c_114, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_5', '#skF_4', '#skF_6')), '#skF_5') | v1_xboole_0(k1_relset_1('#skF_5', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_4, c_109])).
% 2.47/1.34  tff(c_162, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_5', '#skF_4', '#skF_6')), '#skF_5')), inference(splitLeft, [status(thm)], [c_114])).
% 2.47/1.34  tff(c_202, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_201, c_162])).
% 2.47/1.34  tff(c_265, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_5') | v1_xboole_0(k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_233, c_202])).
% 2.47/1.34  tff(c_272, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_265])).
% 2.47/1.34  tff(c_288, plain, (~v4_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_272])).
% 2.47/1.34  tff(c_292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_139, c_288])).
% 2.47/1.34  tff(c_293, plain, (v1_xboole_0(k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_265])).
% 2.47/1.34  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.47/1.34  tff(c_67, plain, (![A_5]: (A_5='#skF_2' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_8])).
% 2.47/1.34  tff(c_298, plain, (k1_relat_1('#skF_6')='#skF_2'), inference(resolution, [status(thm)], [c_293, c_67])).
% 2.47/1.34  tff(c_30, plain, (![A_19]: (k9_relat_1(A_19, k1_relat_1(A_19))=k2_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.47/1.34  tff(c_313, plain, (k9_relat_1('#skF_6', '#skF_2')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_298, c_30])).
% 2.47/1.34  tff(c_321, plain, (k9_relat_1('#skF_6', '#skF_2')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_313])).
% 2.47/1.34  tff(c_346, plain, (![A_98, B_99, C_100]: (r2_hidden('#skF_3'(A_98, B_99, C_100), B_99) | ~r2_hidden(A_98, k9_relat_1(C_100, B_99)) | ~v1_relat_1(C_100))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.47/1.34  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.34  tff(c_369, plain, (![B_102, A_103, C_104]: (~v1_xboole_0(B_102) | ~r2_hidden(A_103, k9_relat_1(C_104, B_102)) | ~v1_relat_1(C_104))), inference(resolution, [status(thm)], [c_346, c_2])).
% 2.47/1.34  tff(c_376, plain, (![A_103]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_103, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_321, c_369])).
% 2.47/1.34  tff(c_388, plain, (![A_105]: (~r2_hidden(A_105, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_10, c_376])).
% 2.47/1.34  tff(c_398, plain, (v1_xboole_0(k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_4, c_388])).
% 2.47/1.34  tff(c_417, plain, (k2_relat_1('#skF_6')='#skF_2'), inference(resolution, [status(thm)], [c_398, c_67])).
% 2.47/1.34  tff(c_421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_417])).
% 2.47/1.34  tff(c_422, plain, (v1_xboole_0(k1_relset_1('#skF_5', '#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_114])).
% 2.47/1.34  tff(c_427, plain, (k1_relset_1('#skF_5', '#skF_4', '#skF_6')='#skF_2'), inference(resolution, [status(thm)], [c_422, c_67])).
% 2.47/1.34  tff(c_472, plain, (![A_117, B_118, C_119]: (k1_relset_1(A_117, B_118, C_119)=k1_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.47/1.34  tff(c_479, plain, (k1_relset_1('#skF_5', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_472])).
% 2.47/1.34  tff(c_482, plain, (k1_relat_1('#skF_6')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_427, c_479])).
% 2.47/1.34  tff(c_492, plain, (k9_relat_1('#skF_6', '#skF_2')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_482, c_30])).
% 2.47/1.34  tff(c_500, plain, (k9_relat_1('#skF_6', '#skF_2')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_492])).
% 2.47/1.34  tff(c_535, plain, (![A_128, B_129, C_130]: (r2_hidden('#skF_3'(A_128, B_129, C_130), B_129) | ~r2_hidden(A_128, k9_relat_1(C_130, B_129)) | ~v1_relat_1(C_130))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.47/1.34  tff(c_548, plain, (![B_131, A_132, C_133]: (~v1_xboole_0(B_131) | ~r2_hidden(A_132, k9_relat_1(C_133, B_131)) | ~v1_relat_1(C_133))), inference(resolution, [status(thm)], [c_535, c_2])).
% 2.47/1.34  tff(c_555, plain, (![A_132]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_132, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_500, c_548])).
% 2.47/1.34  tff(c_567, plain, (![A_134]: (~r2_hidden(A_134, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_10, c_555])).
% 2.47/1.34  tff(c_577, plain, (v1_xboole_0(k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_4, c_567])).
% 2.47/1.34  tff(c_580, plain, (k2_relat_1('#skF_6')='#skF_2'), inference(resolution, [status(thm)], [c_577, c_67])).
% 2.47/1.34  tff(c_584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_526, c_580])).
% 2.47/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.34  
% 2.47/1.34  Inference rules
% 2.47/1.34  ----------------------
% 2.47/1.34  #Ref     : 0
% 2.47/1.34  #Sup     : 115
% 2.47/1.34  #Fact    : 0
% 2.47/1.34  #Define  : 0
% 2.47/1.34  #Split   : 2
% 2.47/1.34  #Chain   : 0
% 2.47/1.34  #Close   : 0
% 2.47/1.34  
% 2.47/1.34  Ordering : KBO
% 2.47/1.34  
% 2.47/1.34  Simplification rules
% 2.47/1.34  ----------------------
% 2.47/1.34  #Subsume      : 3
% 2.47/1.34  #Demod        : 42
% 2.47/1.34  #Tautology    : 42
% 2.47/1.34  #SimpNegUnit  : 2
% 2.47/1.34  #BackRed      : 14
% 2.47/1.34  
% 2.47/1.34  #Partial instantiations: 0
% 2.47/1.34  #Strategies tried      : 1
% 2.47/1.34  
% 2.47/1.34  Timing (in seconds)
% 2.47/1.34  ----------------------
% 2.77/1.34  Preprocessing        : 0.31
% 2.77/1.34  Parsing              : 0.17
% 2.77/1.34  CNF conversion       : 0.02
% 2.77/1.34  Main loop            : 0.27
% 2.77/1.34  Inferencing          : 0.11
% 2.77/1.34  Reduction            : 0.08
% 2.77/1.34  Demodulation         : 0.05
% 2.77/1.34  BG Simplification    : 0.02
% 2.77/1.34  Subsumption          : 0.04
% 2.77/1.34  Abstraction          : 0.02
% 2.77/1.34  MUC search           : 0.00
% 2.77/1.34  Cooper               : 0.00
% 2.77/1.34  Total                : 0.62
% 2.77/1.34  Index Insertion      : 0.00
% 2.77/1.34  Index Deletion       : 0.00
% 2.77/1.34  Index Matching       : 0.00
% 2.77/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
