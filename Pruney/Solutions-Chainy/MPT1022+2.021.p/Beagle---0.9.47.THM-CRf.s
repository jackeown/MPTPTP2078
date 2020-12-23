%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:16 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 163 expanded)
%              Number of leaves         :   37 (  73 expanded)
%              Depth                    :    9
%              Number of atoms          :  143 ( 401 expanded)
%              Number of equality atoms :   40 (  98 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_34,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_44,plain,(
    ! [B_33,A_34] :
      ( v1_relat_1(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_44])).

tff(c_50,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_47])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_38,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_370,plain,(
    ! [C_126,A_127,B_128] :
      ( v2_funct_1(C_126)
      | ~ v3_funct_2(C_126,A_127,B_128)
      | ~ v1_funct_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_373,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_370])).

tff(c_376,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_373])).

tff(c_40,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_304,plain,(
    ! [A_111,B_112,C_113] :
      ( k1_relset_1(A_111,B_112,C_113) = k1_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_308,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_304])).

tff(c_406,plain,(
    ! [A_135,B_136] :
      ( k1_relset_1(A_135,A_135,B_136) = A_135
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_zfmisc_1(A_135,A_135)))
      | ~ v1_funct_2(B_136,A_135,A_135)
      | ~ v1_funct_1(B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_409,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_406])).

tff(c_412,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_308,c_409])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( k10_relat_1(B_9,k9_relat_1(B_9,A_8)) = A_8
      | ~ v2_funct_1(B_9)
      | ~ r1_tarski(A_8,k1_relat_1(B_9))
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_416,plain,(
    ! [A_8] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_8)) = A_8
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_8,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_8])).

tff(c_426,plain,(
    ! [A_137] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_137)) = A_137
      | ~ r1_tarski(A_137,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_376,c_416])).

tff(c_317,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( k8_relset_1(A_118,B_119,C_120,D_121) = k10_relat_1(C_120,D_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_320,plain,(
    ! [D_121] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_121) = k10_relat_1('#skF_3',D_121) ),
    inference(resolution,[status(thm)],[c_36,c_317])).

tff(c_313,plain,(
    ! [A_114,B_115,C_116,D_117] :
      ( k7_relset_1(A_114,B_115,C_116,D_117) = k9_relat_1(C_116,D_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_316,plain,(
    ! [D_117] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_117) = k9_relat_1('#skF_3',D_117) ),
    inference(resolution,[status(thm)],[c_36,c_313])).

tff(c_57,plain,(
    ! [C_38,B_39,A_40] :
      ( v5_relat_1(C_38,B_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_40,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_61,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_57])).

tff(c_63,plain,(
    ! [B_42,A_43] :
      ( k2_relat_1(B_42) = A_43
      | ~ v2_funct_2(B_42,A_43)
      | ~ v5_relat_1(B_42,A_43)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_66,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_63])).

tff(c_69,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_66])).

tff(c_70,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_116,plain,(
    ! [C_62,B_63,A_64] :
      ( v2_funct_2(C_62,B_63)
      | ~ v3_funct_2(C_62,A_64,B_63)
      | ~ v1_funct_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_119,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_116])).

tff(c_122,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_119])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_122])).

tff(c_125,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_153,plain,(
    ! [B_71,A_72] :
      ( k9_relat_1(B_71,k10_relat_1(B_71,A_72)) = A_72
      | ~ r1_tarski(A_72,k2_relat_1(B_71))
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_155,plain,(
    ! [A_72] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_72)) = A_72
      | ~ r1_tarski(A_72,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_153])).

tff(c_157,plain,(
    ! [A_72] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_72)) = A_72
      | ~ r1_tarski(A_72,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_155])).

tff(c_181,plain,(
    ! [A_79,B_80,C_81,D_82] :
      ( k7_relset_1(A_79,B_80,C_81,D_82) = k9_relat_1(C_81,D_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_184,plain,(
    ! [D_82] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_82) = k9_relat_1('#skF_3',D_82) ),
    inference(resolution,[status(thm)],[c_36,c_181])).

tff(c_167,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( k8_relset_1(A_74,B_75,C_76,D_77) = k10_relat_1(C_76,D_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_170,plain,(
    ! [D_77] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_77) = k10_relat_1('#skF_3',D_77) ),
    inference(resolution,[status(thm)],[c_36,c_167])).

tff(c_32,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2'
    | k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_56,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_171,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_56])).

tff(c_185,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_171])).

tff(c_197,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_185])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_197])).

tff(c_202,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_321,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_202])).

tff(c_347,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_321])).

tff(c_435,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_347])).

tff(c_450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_435])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.30  
% 2.23/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.30  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.23/1.30  
% 2.23/1.30  %Foreground sorts:
% 2.23/1.30  
% 2.23/1.30  
% 2.23/1.30  %Background operators:
% 2.23/1.30  
% 2.23/1.30  
% 2.23/1.30  %Foreground operators:
% 2.23/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.23/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.30  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.23/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.23/1.30  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.23/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.23/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.23/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.30  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 2.23/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.23/1.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.23/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.23/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.23/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.23/1.30  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 2.23/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.30  
% 2.23/1.32  tff(f_113, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_funct_2)).
% 2.23/1.32  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.23/1.32  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.23/1.32  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 2.23/1.32  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.23/1.32  tff(f_98, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 2.23/1.32  tff(f_52, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 2.23/1.32  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.23/1.32  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.23/1.32  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.23/1.32  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 2.23/1.32  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 2.23/1.32  tff(c_34, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.23/1.32  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.23/1.32  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.23/1.32  tff(c_44, plain, (![B_33, A_34]: (v1_relat_1(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.23/1.32  tff(c_47, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_36, c_44])).
% 2.23/1.32  tff(c_50, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_47])).
% 2.23/1.32  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.23/1.32  tff(c_38, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.23/1.32  tff(c_370, plain, (![C_126, A_127, B_128]: (v2_funct_1(C_126) | ~v3_funct_2(C_126, A_127, B_128) | ~v1_funct_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.23/1.32  tff(c_373, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_370])).
% 2.23/1.32  tff(c_376, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_373])).
% 2.23/1.32  tff(c_40, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.23/1.32  tff(c_304, plain, (![A_111, B_112, C_113]: (k1_relset_1(A_111, B_112, C_113)=k1_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.23/1.32  tff(c_308, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_304])).
% 2.23/1.32  tff(c_406, plain, (![A_135, B_136]: (k1_relset_1(A_135, A_135, B_136)=A_135 | ~m1_subset_1(B_136, k1_zfmisc_1(k2_zfmisc_1(A_135, A_135))) | ~v1_funct_2(B_136, A_135, A_135) | ~v1_funct_1(B_136))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.23/1.32  tff(c_409, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_406])).
% 2.23/1.32  tff(c_412, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_308, c_409])).
% 2.23/1.32  tff(c_8, plain, (![B_9, A_8]: (k10_relat_1(B_9, k9_relat_1(B_9, A_8))=A_8 | ~v2_funct_1(B_9) | ~r1_tarski(A_8, k1_relat_1(B_9)) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.23/1.32  tff(c_416, plain, (![A_8]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_8))=A_8 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_8, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_412, c_8])).
% 2.23/1.32  tff(c_426, plain, (![A_137]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_137))=A_137 | ~r1_tarski(A_137, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_376, c_416])).
% 2.23/1.32  tff(c_317, plain, (![A_118, B_119, C_120, D_121]: (k8_relset_1(A_118, B_119, C_120, D_121)=k10_relat_1(C_120, D_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.23/1.32  tff(c_320, plain, (![D_121]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_121)=k10_relat_1('#skF_3', D_121))), inference(resolution, [status(thm)], [c_36, c_317])).
% 2.23/1.32  tff(c_313, plain, (![A_114, B_115, C_116, D_117]: (k7_relset_1(A_114, B_115, C_116, D_117)=k9_relat_1(C_116, D_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.23/1.32  tff(c_316, plain, (![D_117]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_117)=k9_relat_1('#skF_3', D_117))), inference(resolution, [status(thm)], [c_36, c_313])).
% 2.23/1.32  tff(c_57, plain, (![C_38, B_39, A_40]: (v5_relat_1(C_38, B_39) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_40, B_39))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.23/1.32  tff(c_61, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_57])).
% 2.23/1.32  tff(c_63, plain, (![B_42, A_43]: (k2_relat_1(B_42)=A_43 | ~v2_funct_2(B_42, A_43) | ~v5_relat_1(B_42, A_43) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.23/1.32  tff(c_66, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_61, c_63])).
% 2.23/1.32  tff(c_69, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_66])).
% 2.23/1.32  tff(c_70, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_69])).
% 2.23/1.32  tff(c_116, plain, (![C_62, B_63, A_64]: (v2_funct_2(C_62, B_63) | ~v3_funct_2(C_62, A_64, B_63) | ~v1_funct_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.23/1.32  tff(c_119, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_116])).
% 2.23/1.32  tff(c_122, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_119])).
% 2.23/1.32  tff(c_124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_122])).
% 2.23/1.32  tff(c_125, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_69])).
% 2.23/1.32  tff(c_153, plain, (![B_71, A_72]: (k9_relat_1(B_71, k10_relat_1(B_71, A_72))=A_72 | ~r1_tarski(A_72, k2_relat_1(B_71)) | ~v1_funct_1(B_71) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.32  tff(c_155, plain, (![A_72]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_72))=A_72 | ~r1_tarski(A_72, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_125, c_153])).
% 2.23/1.32  tff(c_157, plain, (![A_72]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_72))=A_72 | ~r1_tarski(A_72, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_155])).
% 2.23/1.32  tff(c_181, plain, (![A_79, B_80, C_81, D_82]: (k7_relset_1(A_79, B_80, C_81, D_82)=k9_relat_1(C_81, D_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.23/1.32  tff(c_184, plain, (![D_82]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_82)=k9_relat_1('#skF_3', D_82))), inference(resolution, [status(thm)], [c_36, c_181])).
% 2.23/1.32  tff(c_167, plain, (![A_74, B_75, C_76, D_77]: (k8_relset_1(A_74, B_75, C_76, D_77)=k10_relat_1(C_76, D_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.23/1.32  tff(c_170, plain, (![D_77]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_77)=k10_relat_1('#skF_3', D_77))), inference(resolution, [status(thm)], [c_36, c_167])).
% 2.23/1.32  tff(c_32, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2' | k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.23/1.32  tff(c_56, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_32])).
% 2.23/1.32  tff(c_171, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_170, c_56])).
% 2.23/1.32  tff(c_185, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_184, c_171])).
% 2.23/1.32  tff(c_197, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_157, c_185])).
% 2.23/1.32  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_197])).
% 2.23/1.32  tff(c_202, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_32])).
% 2.23/1.32  tff(c_321, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_316, c_202])).
% 2.23/1.32  tff(c_347, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_320, c_321])).
% 2.23/1.32  tff(c_435, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_426, c_347])).
% 2.23/1.32  tff(c_450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_435])).
% 2.23/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.32  
% 2.23/1.32  Inference rules
% 2.23/1.32  ----------------------
% 2.23/1.32  #Ref     : 0
% 2.23/1.32  #Sup     : 92
% 2.23/1.32  #Fact    : 0
% 2.23/1.32  #Define  : 0
% 2.23/1.32  #Split   : 3
% 2.23/1.32  #Chain   : 0
% 2.23/1.32  #Close   : 0
% 2.23/1.32  
% 2.23/1.32  Ordering : KBO
% 2.23/1.32  
% 2.23/1.32  Simplification rules
% 2.23/1.32  ----------------------
% 2.23/1.32  #Subsume      : 0
% 2.23/1.32  #Demod        : 57
% 2.23/1.32  #Tautology    : 58
% 2.23/1.32  #SimpNegUnit  : 2
% 2.23/1.32  #BackRed      : 10
% 2.23/1.32  
% 2.23/1.32  #Partial instantiations: 0
% 2.23/1.32  #Strategies tried      : 1
% 2.23/1.32  
% 2.23/1.32  Timing (in seconds)
% 2.23/1.32  ----------------------
% 2.63/1.32  Preprocessing        : 0.32
% 2.63/1.32  Parsing              : 0.17
% 2.63/1.32  CNF conversion       : 0.02
% 2.63/1.32  Main loop            : 0.24
% 2.63/1.32  Inferencing          : 0.10
% 2.63/1.32  Reduction            : 0.07
% 2.63/1.32  Demodulation         : 0.05
% 2.63/1.32  BG Simplification    : 0.02
% 2.63/1.32  Subsumption          : 0.02
% 2.63/1.32  Abstraction          : 0.01
% 2.63/1.32  MUC search           : 0.00
% 2.63/1.32  Cooper               : 0.00
% 2.63/1.32  Total                : 0.60
% 2.63/1.32  Index Insertion      : 0.00
% 2.63/1.32  Index Deletion       : 0.00
% 2.63/1.32  Index Matching       : 0.00
% 2.63/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
