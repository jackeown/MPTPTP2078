%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:52 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 130 expanded)
%              Number of leaves         :   41 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  107 ( 190 expanded)
%              Number of equality atoms :   47 (  78 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k8_relat_1(A,B)) = k3_xboole_0(k2_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_60,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_69,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_60])).

tff(c_508,plain,(
    ! [A_133,B_134,C_135] :
      ( k2_relset_1(A_133,B_134,C_135) = k2_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_517,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_508])).

tff(c_523,plain,(
    ! [A_136,B_137,C_138] :
      ( m1_subset_1(k2_relset_1(A_136,B_137,C_138),k1_zfmisc_1(B_137))
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_549,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_517,c_523])).

tff(c_557,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_549])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_561,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_557,c_6])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k8_relat_1(A_9,B_10) = B_10
      | ~ r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_564,plain,
    ( k8_relat_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_561,c_12])).

tff(c_567,plain,(
    k8_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_564])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( k3_xboole_0(k2_relat_1(B_8),A_7) = k2_relat_1(k8_relat_1(A_7,B_8))
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_472,plain,(
    ! [B_125,A_126] :
      ( k10_relat_1(B_125,k3_xboole_0(k2_relat_1(B_125),A_126)) = k10_relat_1(B_125,A_126)
      | ~ v1_relat_1(B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_663,plain,(
    ! [B_150,A_151] :
      ( k10_relat_1(B_150,k2_relat_1(k8_relat_1(A_151,B_150))) = k10_relat_1(B_150,A_151)
      | ~ v1_relat_1(B_150)
      | ~ v1_relat_1(B_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_472])).

tff(c_672,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_663])).

tff(c_676,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_69,c_672])).

tff(c_18,plain,(
    ! [A_15] :
      ( k10_relat_1(A_15,k2_relat_1(A_15)) = k1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_692,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_676,c_18])).

tff(c_699,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_692])).

tff(c_677,plain,(
    ! [A_152,B_153,C_154,D_155] :
      ( k8_relset_1(A_152,B_153,C_154,D_155) = k10_relat_1(C_154,D_155)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_688,plain,(
    ! [D_155] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_155) = k10_relat_1('#skF_3',D_155) ),
    inference(resolution,[status(thm)],[c_40,c_677])).

tff(c_487,plain,(
    ! [A_127,B_128,C_129] :
      ( k1_relset_1(A_127,B_128,C_129) = k1_relat_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_496,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_487])).

tff(c_129,plain,(
    ! [C_64,A_65,B_66] :
      ( v4_relat_1(C_64,A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_138,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_129])).

tff(c_145,plain,(
    ! [B_70,A_71] :
      ( k7_relat_1(B_70,A_71) = B_70
      | ~ v4_relat_1(B_70,A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_148,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_138,c_145])).

tff(c_151,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_148])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_155,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_14])).

tff(c_159,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_155])).

tff(c_339,plain,(
    ! [A_97,B_98,C_99,D_100] :
      ( k7_relset_1(A_97,B_98,C_99,D_100) = k9_relat_1(C_99,D_100)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_350,plain,(
    ! [D_100] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_100) = k9_relat_1('#skF_3',D_100) ),
    inference(resolution,[status(thm)],[c_40,c_339])).

tff(c_226,plain,(
    ! [A_83,B_84,C_85] :
      ( k2_relset_1(A_83,B_84,C_85) = k2_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_235,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_226])).

tff(c_38,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_85,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_236,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_85])).

tff(c_351,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_236])).

tff(c_354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_351])).

tff(c_355,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_497,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_355])).

tff(c_709,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_497])).

tff(c_712,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_709])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:28:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.28  
% 2.45/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.29  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.45/1.29  
% 2.45/1.29  %Foreground sorts:
% 2.45/1.29  
% 2.45/1.29  
% 2.45/1.29  %Background operators:
% 2.45/1.29  
% 2.45/1.29  
% 2.45/1.29  %Foreground operators:
% 2.45/1.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.45/1.29  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.45/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.45/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.45/1.29  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.45/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.45/1.29  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.45/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.45/1.29  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.45/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.45/1.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.45/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.29  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.45/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.45/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.45/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.45/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.45/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.45/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.29  
% 2.45/1.30  tff(f_98, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.45/1.30  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.45/1.30  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.45/1.30  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.45/1.30  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.45/1.30  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.45/1.30  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k8_relat_1(A, B)) = k3_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t119_relat_1)).
% 2.45/1.30  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 2.45/1.30  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.45/1.30  tff(f_91, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.45/1.30  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.45/1.30  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.45/1.30  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.45/1.30  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.45/1.30  tff(f_87, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.45/1.30  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.45/1.30  tff(c_60, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.45/1.30  tff(c_69, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_60])).
% 2.45/1.30  tff(c_508, plain, (![A_133, B_134, C_135]: (k2_relset_1(A_133, B_134, C_135)=k2_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.45/1.30  tff(c_517, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_508])).
% 2.45/1.30  tff(c_523, plain, (![A_136, B_137, C_138]: (m1_subset_1(k2_relset_1(A_136, B_137, C_138), k1_zfmisc_1(B_137)) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.45/1.30  tff(c_549, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_517, c_523])).
% 2.45/1.30  tff(c_557, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_549])).
% 2.45/1.30  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.45/1.30  tff(c_561, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_557, c_6])).
% 2.45/1.30  tff(c_12, plain, (![A_9, B_10]: (k8_relat_1(A_9, B_10)=B_10 | ~r1_tarski(k2_relat_1(B_10), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.45/1.30  tff(c_564, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_561, c_12])).
% 2.45/1.30  tff(c_567, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_69, c_564])).
% 2.45/1.30  tff(c_10, plain, (![B_8, A_7]: (k3_xboole_0(k2_relat_1(B_8), A_7)=k2_relat_1(k8_relat_1(A_7, B_8)) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.45/1.30  tff(c_472, plain, (![B_125, A_126]: (k10_relat_1(B_125, k3_xboole_0(k2_relat_1(B_125), A_126))=k10_relat_1(B_125, A_126) | ~v1_relat_1(B_125))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.45/1.30  tff(c_663, plain, (![B_150, A_151]: (k10_relat_1(B_150, k2_relat_1(k8_relat_1(A_151, B_150)))=k10_relat_1(B_150, A_151) | ~v1_relat_1(B_150) | ~v1_relat_1(B_150))), inference(superposition, [status(thm), theory('equality')], [c_10, c_472])).
% 2.45/1.30  tff(c_672, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_567, c_663])).
% 2.45/1.30  tff(c_676, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_69, c_672])).
% 2.45/1.30  tff(c_18, plain, (![A_15]: (k10_relat_1(A_15, k2_relat_1(A_15))=k1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.45/1.30  tff(c_692, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_676, c_18])).
% 2.45/1.30  tff(c_699, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_692])).
% 2.45/1.30  tff(c_677, plain, (![A_152, B_153, C_154, D_155]: (k8_relset_1(A_152, B_153, C_154, D_155)=k10_relat_1(C_154, D_155) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.45/1.30  tff(c_688, plain, (![D_155]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_155)=k10_relat_1('#skF_3', D_155))), inference(resolution, [status(thm)], [c_40, c_677])).
% 2.45/1.30  tff(c_487, plain, (![A_127, B_128, C_129]: (k1_relset_1(A_127, B_128, C_129)=k1_relat_1(C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.45/1.30  tff(c_496, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_487])).
% 2.45/1.30  tff(c_129, plain, (![C_64, A_65, B_66]: (v4_relat_1(C_64, A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.45/1.30  tff(c_138, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_129])).
% 2.45/1.30  tff(c_145, plain, (![B_70, A_71]: (k7_relat_1(B_70, A_71)=B_70 | ~v4_relat_1(B_70, A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.45/1.30  tff(c_148, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_138, c_145])).
% 2.45/1.30  tff(c_151, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_69, c_148])).
% 2.45/1.30  tff(c_14, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.45/1.30  tff(c_155, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_151, c_14])).
% 2.45/1.30  tff(c_159, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_155])).
% 2.45/1.30  tff(c_339, plain, (![A_97, B_98, C_99, D_100]: (k7_relset_1(A_97, B_98, C_99, D_100)=k9_relat_1(C_99, D_100) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.45/1.30  tff(c_350, plain, (![D_100]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_100)=k9_relat_1('#skF_3', D_100))), inference(resolution, [status(thm)], [c_40, c_339])).
% 2.45/1.30  tff(c_226, plain, (![A_83, B_84, C_85]: (k2_relset_1(A_83, B_84, C_85)=k2_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.45/1.30  tff(c_235, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_226])).
% 2.45/1.30  tff(c_38, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.45/1.30  tff(c_85, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 2.45/1.30  tff(c_236, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_235, c_85])).
% 2.45/1.30  tff(c_351, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_350, c_236])).
% 2.45/1.30  tff(c_354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_351])).
% 2.45/1.30  tff(c_355, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 2.45/1.30  tff(c_497, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_496, c_355])).
% 2.45/1.30  tff(c_709, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_688, c_497])).
% 2.45/1.30  tff(c_712, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_699, c_709])).
% 2.45/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.30  
% 2.45/1.30  Inference rules
% 2.45/1.30  ----------------------
% 2.45/1.30  #Ref     : 0
% 2.45/1.30  #Sup     : 161
% 2.45/1.30  #Fact    : 0
% 2.45/1.30  #Define  : 0
% 2.45/1.30  #Split   : 1
% 2.45/1.30  #Chain   : 0
% 2.45/1.30  #Close   : 0
% 2.45/1.30  
% 2.45/1.30  Ordering : KBO
% 2.45/1.30  
% 2.45/1.30  Simplification rules
% 2.45/1.30  ----------------------
% 2.45/1.30  #Subsume      : 0
% 2.45/1.30  #Demod        : 40
% 2.45/1.30  #Tautology    : 77
% 2.45/1.30  #SimpNegUnit  : 0
% 2.45/1.30  #BackRed      : 6
% 2.45/1.30  
% 2.45/1.30  #Partial instantiations: 0
% 2.45/1.30  #Strategies tried      : 1
% 2.45/1.30  
% 2.45/1.30  Timing (in seconds)
% 2.45/1.30  ----------------------
% 2.45/1.31  Preprocessing        : 0.30
% 2.45/1.31  Parsing              : 0.16
% 2.45/1.31  CNF conversion       : 0.02
% 2.45/1.31  Main loop            : 0.31
% 2.45/1.31  Inferencing          : 0.13
% 2.45/1.31  Reduction            : 0.08
% 2.45/1.31  Demodulation         : 0.06
% 2.45/1.31  BG Simplification    : 0.02
% 2.45/1.31  Subsumption          : 0.04
% 2.45/1.31  Abstraction          : 0.02
% 2.78/1.31  MUC search           : 0.00
% 2.78/1.31  Cooper               : 0.00
% 2.78/1.31  Total                : 0.64
% 2.78/1.31  Index Insertion      : 0.00
% 2.78/1.31  Index Deletion       : 0.00
% 2.78/1.31  Index Matching       : 0.00
% 2.78/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
