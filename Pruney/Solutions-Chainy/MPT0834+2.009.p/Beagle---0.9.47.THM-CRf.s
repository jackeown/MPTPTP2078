%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:50 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 145 expanded)
%              Number of leaves         :   39 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  135 ( 239 expanded)
%              Number of equality atoms :   49 (  85 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_535,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( k8_relset_1(A_123,B_124,C_125,D_126) = k10_relat_1(C_125,D_126)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_538,plain,(
    ! [D_126] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_126) = k10_relat_1('#skF_3',D_126) ),
    inference(resolution,[status(thm)],[c_42,c_535])).

tff(c_442,plain,(
    ! [A_111,B_112,C_113] :
      ( k1_relset_1(A_111,B_112,C_113) = k1_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_446,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_442])).

tff(c_59,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_63,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_59])).

tff(c_123,plain,(
    ! [C_64,A_65,B_66] :
      ( v4_relat_1(C_64,A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_127,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_123])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_130,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_127,c_20])).

tff(c_133,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_130])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( k2_relat_1(k7_relat_1(B_8,A_7)) = k9_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_137,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_14])).

tff(c_141,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_137])).

tff(c_295,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( k7_relset_1(A_86,B_87,C_88,D_89) = k9_relat_1(C_88,D_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_298,plain,(
    ! [D_89] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_89) = k9_relat_1('#skF_3',D_89) ),
    inference(resolution,[status(thm)],[c_42,c_295])).

tff(c_204,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_208,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_204])).

tff(c_40,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_84,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_214,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_84])).

tff(c_299,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_214])).

tff(c_302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_299])).

tff(c_303,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_447,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_303])).

tff(c_540,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_447])).

tff(c_79,plain,(
    ! [C_52,B_53,A_54] :
      ( v5_relat_1(C_52,B_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_54,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_83,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_79])).

tff(c_305,plain,(
    ! [B_90,A_91] :
      ( r1_tarski(k2_relat_1(B_90),A_91)
      | ~ v5_relat_1(B_90,A_91)
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_403,plain,(
    ! [B_106,A_107] :
      ( k3_xboole_0(k2_relat_1(B_106),A_107) = k2_relat_1(B_106)
      | ~ v5_relat_1(B_106,A_107)
      | ~ v1_relat_1(B_106) ) ),
    inference(resolution,[status(thm)],[c_305,c_8])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( k10_relat_1(B_12,k3_xboole_0(k2_relat_1(B_12),A_11)) = k10_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_604,plain,(
    ! [B_135,A_136] :
      ( k10_relat_1(B_135,k2_relat_1(B_135)) = k10_relat_1(B_135,A_136)
      | ~ v1_relat_1(B_135)
      | ~ v5_relat_1(B_135,A_136)
      | ~ v1_relat_1(B_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_18])).

tff(c_612,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_83,c_604])).

tff(c_622,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_612])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_643,plain,(
    ! [D_137,B_138,C_139,A_140] :
      ( m1_subset_1(D_137,k1_zfmisc_1(k2_zfmisc_1(B_138,C_139)))
      | ~ r1_tarski(k1_relat_1(D_137),B_138)
      | ~ m1_subset_1(D_137,k1_zfmisc_1(k2_zfmisc_1(A_140,C_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_671,plain,(
    ! [B_141] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_141,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_141) ) ),
    inference(resolution,[status(thm)],[c_42,c_643])).

tff(c_28,plain,(
    ! [C_22,A_20,B_21] :
      ( v4_relat_1(C_22,A_20)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_703,plain,(
    ! [B_142] :
      ( v4_relat_1('#skF_3',B_142)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_142) ) ),
    inference(resolution,[status(thm)],[c_671,c_28])).

tff(c_713,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_703])).

tff(c_716,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_713,c_20])).

tff(c_719,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_716])).

tff(c_726,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_14])).

tff(c_732,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_726])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,k10_relat_1(B_16,k9_relat_1(B_16,A_15)))
      | ~ r1_tarski(A_15,k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_71,plain,(
    ! [B_50,A_51] :
      ( r1_tarski(k10_relat_1(B_50,A_51),k1_relat_1(B_50))
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_486,plain,(
    ! [B_118,A_119] :
      ( k10_relat_1(B_118,A_119) = k1_relat_1(B_118)
      | ~ r1_tarski(k1_relat_1(B_118),k10_relat_1(B_118,A_119))
      | ~ v1_relat_1(B_118) ) ),
    inference(resolution,[status(thm)],[c_71,c_2])).

tff(c_490,plain,(
    ! [B_16] :
      ( k10_relat_1(B_16,k9_relat_1(B_16,k1_relat_1(B_16))) = k1_relat_1(B_16)
      | ~ r1_tarski(k1_relat_1(B_16),k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_22,c_486])).

tff(c_496,plain,(
    ! [B_16] :
      ( k10_relat_1(B_16,k9_relat_1(B_16,k1_relat_1(B_16))) = k1_relat_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_490])).

tff(c_750,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_732,c_496])).

tff(c_761,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_622,c_750])).

tff(c_763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_540,c_761])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.49  
% 2.74/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.50  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.74/1.50  
% 2.74/1.50  %Foreground sorts:
% 2.74/1.50  
% 2.74/1.50  
% 2.74/1.50  %Background operators:
% 2.74/1.50  
% 2.74/1.50  
% 2.74/1.50  %Foreground operators:
% 2.74/1.50  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.74/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.74/1.50  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.74/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.74/1.50  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.74/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.50  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.74/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.50  tff('#skF_1', type, '#skF_1': $i).
% 2.74/1.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.74/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.74/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.50  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.74/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.74/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.74/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.74/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.74/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.74/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.50  
% 2.92/1.51  tff(f_104, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.92/1.51  tff(f_91, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.92/1.51  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.92/1.51  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.92/1.51  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.92/1.51  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.92/1.51  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.92/1.51  tff(f_87, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.92/1.51  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.92/1.51  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.92/1.51  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.92/1.51  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 2.92/1.51  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.92/1.51  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 2.92/1.51  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 2.92/1.51  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 2.92/1.51  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.92/1.51  tff(c_535, plain, (![A_123, B_124, C_125, D_126]: (k8_relset_1(A_123, B_124, C_125, D_126)=k10_relat_1(C_125, D_126) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.92/1.51  tff(c_538, plain, (![D_126]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_126)=k10_relat_1('#skF_3', D_126))), inference(resolution, [status(thm)], [c_42, c_535])).
% 2.92/1.51  tff(c_442, plain, (![A_111, B_112, C_113]: (k1_relset_1(A_111, B_112, C_113)=k1_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.92/1.51  tff(c_446, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_442])).
% 2.92/1.51  tff(c_59, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.92/1.51  tff(c_63, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_59])).
% 2.92/1.51  tff(c_123, plain, (![C_64, A_65, B_66]: (v4_relat_1(C_64, A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.92/1.51  tff(c_127, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_123])).
% 2.92/1.51  tff(c_20, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.92/1.51  tff(c_130, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_127, c_20])).
% 2.92/1.51  tff(c_133, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_130])).
% 2.92/1.51  tff(c_14, plain, (![B_8, A_7]: (k2_relat_1(k7_relat_1(B_8, A_7))=k9_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.92/1.51  tff(c_137, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_133, c_14])).
% 2.92/1.51  tff(c_141, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_137])).
% 2.92/1.51  tff(c_295, plain, (![A_86, B_87, C_88, D_89]: (k7_relset_1(A_86, B_87, C_88, D_89)=k9_relat_1(C_88, D_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.92/1.51  tff(c_298, plain, (![D_89]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_89)=k9_relat_1('#skF_3', D_89))), inference(resolution, [status(thm)], [c_42, c_295])).
% 2.92/1.51  tff(c_204, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.92/1.51  tff(c_208, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_204])).
% 2.92/1.51  tff(c_40, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.92/1.51  tff(c_84, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 2.92/1.51  tff(c_214, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_84])).
% 2.92/1.51  tff(c_299, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_298, c_214])).
% 2.92/1.51  tff(c_302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_299])).
% 2.92/1.51  tff(c_303, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 2.92/1.51  tff(c_447, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_446, c_303])).
% 2.92/1.51  tff(c_540, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_538, c_447])).
% 2.92/1.51  tff(c_79, plain, (![C_52, B_53, A_54]: (v5_relat_1(C_52, B_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_54, B_53))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.92/1.51  tff(c_83, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_79])).
% 2.92/1.51  tff(c_305, plain, (![B_90, A_91]: (r1_tarski(k2_relat_1(B_90), A_91) | ~v5_relat_1(B_90, A_91) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.92/1.51  tff(c_8, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.92/1.51  tff(c_403, plain, (![B_106, A_107]: (k3_xboole_0(k2_relat_1(B_106), A_107)=k2_relat_1(B_106) | ~v5_relat_1(B_106, A_107) | ~v1_relat_1(B_106))), inference(resolution, [status(thm)], [c_305, c_8])).
% 2.92/1.51  tff(c_18, plain, (![B_12, A_11]: (k10_relat_1(B_12, k3_xboole_0(k2_relat_1(B_12), A_11))=k10_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.92/1.51  tff(c_604, plain, (![B_135, A_136]: (k10_relat_1(B_135, k2_relat_1(B_135))=k10_relat_1(B_135, A_136) | ~v1_relat_1(B_135) | ~v5_relat_1(B_135, A_136) | ~v1_relat_1(B_135))), inference(superposition, [status(thm), theory('equality')], [c_403, c_18])).
% 2.92/1.51  tff(c_612, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_83, c_604])).
% 2.92/1.51  tff(c_622, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_612])).
% 2.92/1.51  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.51  tff(c_643, plain, (![D_137, B_138, C_139, A_140]: (m1_subset_1(D_137, k1_zfmisc_1(k2_zfmisc_1(B_138, C_139))) | ~r1_tarski(k1_relat_1(D_137), B_138) | ~m1_subset_1(D_137, k1_zfmisc_1(k2_zfmisc_1(A_140, C_139))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.92/1.51  tff(c_671, plain, (![B_141]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_141, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_141))), inference(resolution, [status(thm)], [c_42, c_643])).
% 2.92/1.51  tff(c_28, plain, (![C_22, A_20, B_21]: (v4_relat_1(C_22, A_20) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.92/1.51  tff(c_703, plain, (![B_142]: (v4_relat_1('#skF_3', B_142) | ~r1_tarski(k1_relat_1('#skF_3'), B_142))), inference(resolution, [status(thm)], [c_671, c_28])).
% 2.92/1.51  tff(c_713, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_703])).
% 2.92/1.51  tff(c_716, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_713, c_20])).
% 2.92/1.51  tff(c_719, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_716])).
% 2.92/1.51  tff(c_726, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_719, c_14])).
% 2.92/1.51  tff(c_732, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_726])).
% 2.92/1.51  tff(c_22, plain, (![A_15, B_16]: (r1_tarski(A_15, k10_relat_1(B_16, k9_relat_1(B_16, A_15))) | ~r1_tarski(A_15, k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.92/1.51  tff(c_71, plain, (![B_50, A_51]: (r1_tarski(k10_relat_1(B_50, A_51), k1_relat_1(B_50)) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.92/1.51  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.51  tff(c_486, plain, (![B_118, A_119]: (k10_relat_1(B_118, A_119)=k1_relat_1(B_118) | ~r1_tarski(k1_relat_1(B_118), k10_relat_1(B_118, A_119)) | ~v1_relat_1(B_118))), inference(resolution, [status(thm)], [c_71, c_2])).
% 2.92/1.51  tff(c_490, plain, (![B_16]: (k10_relat_1(B_16, k9_relat_1(B_16, k1_relat_1(B_16)))=k1_relat_1(B_16) | ~r1_tarski(k1_relat_1(B_16), k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_22, c_486])).
% 2.92/1.51  tff(c_496, plain, (![B_16]: (k10_relat_1(B_16, k9_relat_1(B_16, k1_relat_1(B_16)))=k1_relat_1(B_16) | ~v1_relat_1(B_16))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_490])).
% 2.92/1.51  tff(c_750, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_732, c_496])).
% 2.92/1.51  tff(c_761, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_622, c_750])).
% 2.92/1.51  tff(c_763, plain, $false, inference(negUnitSimplification, [status(thm)], [c_540, c_761])).
% 2.92/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.51  
% 2.92/1.51  Inference rules
% 2.92/1.51  ----------------------
% 2.92/1.51  #Ref     : 0
% 2.92/1.51  #Sup     : 170
% 2.92/1.51  #Fact    : 0
% 2.92/1.51  #Define  : 0
% 2.92/1.51  #Split   : 3
% 2.92/1.51  #Chain   : 0
% 2.92/1.51  #Close   : 0
% 2.92/1.51  
% 2.92/1.51  Ordering : KBO
% 2.92/1.51  
% 2.92/1.51  Simplification rules
% 2.92/1.51  ----------------------
% 2.92/1.51  #Subsume      : 9
% 2.92/1.51  #Demod        : 70
% 2.92/1.51  #Tautology    : 85
% 2.92/1.51  #SimpNegUnit  : 3
% 2.92/1.51  #BackRed      : 6
% 2.92/1.51  
% 2.92/1.52  #Partial instantiations: 0
% 2.92/1.52  #Strategies tried      : 1
% 2.92/1.52  
% 2.92/1.52  Timing (in seconds)
% 2.92/1.52  ----------------------
% 2.92/1.52  Preprocessing        : 0.32
% 2.92/1.52  Parsing              : 0.17
% 2.92/1.52  CNF conversion       : 0.02
% 2.92/1.52  Main loop            : 0.31
% 2.92/1.52  Inferencing          : 0.12
% 2.92/1.52  Reduction            : 0.09
% 2.92/1.52  Demodulation         : 0.07
% 2.92/1.52  BG Simplification    : 0.02
% 2.92/1.52  Subsumption          : 0.05
% 2.92/1.52  Abstraction          : 0.02
% 2.92/1.52  MUC search           : 0.00
% 2.92/1.52  Cooper               : 0.00
% 2.92/1.52  Total                : 0.67
% 2.92/1.52  Index Insertion      : 0.00
% 2.92/1.52  Index Deletion       : 0.00
% 2.92/1.52  Index Matching       : 0.00
% 2.92/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
