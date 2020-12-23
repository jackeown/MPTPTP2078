%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:51 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 113 expanded)
%              Number of leaves         :   37 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  111 ( 172 expanded)
%              Number of equality atoms :   42 (  71 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_555,plain,(
    ! [A_156,B_157,C_158,D_159] :
      ( k8_relset_1(A_156,B_157,C_158,D_159) = k10_relat_1(C_158,D_159)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_566,plain,(
    ! [D_159] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_159) = k10_relat_1('#skF_3',D_159) ),
    inference(resolution,[status(thm)],[c_40,c_555])).

tff(c_479,plain,(
    ! [A_142,B_143,C_144] :
      ( k1_relset_1(A_142,B_143,C_144) = k1_relat_1(C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_488,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_479])).

tff(c_53,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_62,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_53])).

tff(c_103,plain,(
    ! [C_57,A_58,B_59] :
      ( v4_relat_1(C_57,A_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_112,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_103])).

tff(c_113,plain,(
    ! [B_60,A_61] :
      ( k7_relat_1(B_60,A_61) = B_60
      | ~ v4_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_116,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_113])).

tff(c_119,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_116])).

tff(c_173,plain,(
    ! [B_77,A_78] :
      ( k2_relat_1(k7_relat_1(B_77,A_78)) = k9_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_188,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_173])).

tff(c_194,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_188])).

tff(c_279,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( k7_relset_1(A_98,B_99,C_100,D_101) = k9_relat_1(C_100,D_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_286,plain,(
    ! [D_101] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_101) = k9_relat_1('#skF_3',D_101) ),
    inference(resolution,[status(thm)],[c_40,c_279])).

tff(c_253,plain,(
    ! [A_92,B_93,C_94] :
      ( k2_relset_1(A_92,B_93,C_94) = k2_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_262,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_253])).

tff(c_38,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_75,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_263,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_75])).

tff(c_287,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_263])).

tff(c_290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_287])).

tff(c_291,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_489,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_291])).

tff(c_575,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_489])).

tff(c_430,plain,(
    ! [A_131,B_132,C_133] :
      ( k2_relset_1(A_131,B_132,C_133) = k2_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_439,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_430])).

tff(c_292,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_440,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_292])).

tff(c_520,plain,(
    ! [A_152,B_153,C_154,D_155] :
      ( m1_subset_1(k7_relset_1(A_152,B_153,C_154,D_155),k1_zfmisc_1(B_153))
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_546,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_520])).

tff(c_554,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_546])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_570,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_554,c_8])).

tff(c_16,plain,(
    ! [A_9] :
      ( k10_relat_1(A_9,k2_relat_1(A_9)) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_449,plain,(
    ! [C_134,A_135,B_136] :
      ( r1_tarski(k10_relat_1(C_134,A_135),k10_relat_1(C_134,B_136))
      | ~ r1_tarski(A_135,B_136)
      | ~ v1_relat_1(C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_864,plain,(
    ! [A_220,B_221] :
      ( r1_tarski(k1_relat_1(A_220),k10_relat_1(A_220,B_221))
      | ~ r1_tarski(k2_relat_1(A_220),B_221)
      | ~ v1_relat_1(A_220)
      | ~ v1_relat_1(A_220) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_449])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k10_relat_1(B_8,A_7),k1_relat_1(B_8))
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_307,plain,(
    ! [B_105,A_106] :
      ( B_105 = A_106
      | ~ r1_tarski(B_105,A_106)
      | ~ r1_tarski(A_106,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_314,plain,(
    ! [B_8,A_7] :
      ( k10_relat_1(B_8,A_7) = k1_relat_1(B_8)
      | ~ r1_tarski(k1_relat_1(B_8),k10_relat_1(B_8,A_7))
      | ~ v1_relat_1(B_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_307])).

tff(c_877,plain,(
    ! [A_222,B_223] :
      ( k10_relat_1(A_222,B_223) = k1_relat_1(A_222)
      | ~ r1_tarski(k2_relat_1(A_222),B_223)
      | ~ v1_relat_1(A_222) ) ),
    inference(resolution,[status(thm)],[c_864,c_314])).

tff(c_883,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_570,c_877])).

tff(c_896,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_883])).

tff(c_898,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_575,c_896])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:53:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.44  
% 2.76/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.44  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.76/1.44  
% 2.76/1.44  %Foreground sorts:
% 2.76/1.44  
% 2.76/1.44  
% 2.76/1.44  %Background operators:
% 2.76/1.44  
% 2.76/1.44  
% 2.76/1.44  %Foreground operators:
% 2.76/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.76/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.76/1.44  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.76/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.76/1.44  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.76/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.76/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.76/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.76/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.76/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.76/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.76/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.76/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.76/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.76/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.44  
% 3.14/1.46  tff(f_96, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.14/1.46  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.14/1.46  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.14/1.46  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.14/1.46  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.14/1.46  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.14/1.46  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.14/1.46  tff(f_85, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.14/1.46  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.14/1.46  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 3.14/1.46  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.14/1.46  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 3.14/1.46  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 3.14/1.46  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 3.14/1.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.14/1.46  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.14/1.46  tff(c_555, plain, (![A_156, B_157, C_158, D_159]: (k8_relset_1(A_156, B_157, C_158, D_159)=k10_relat_1(C_158, D_159) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.14/1.46  tff(c_566, plain, (![D_159]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_159)=k10_relat_1('#skF_3', D_159))), inference(resolution, [status(thm)], [c_40, c_555])).
% 3.14/1.46  tff(c_479, plain, (![A_142, B_143, C_144]: (k1_relset_1(A_142, B_143, C_144)=k1_relat_1(C_144) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.14/1.46  tff(c_488, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_479])).
% 3.14/1.46  tff(c_53, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.14/1.46  tff(c_62, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_53])).
% 3.14/1.46  tff(c_103, plain, (![C_57, A_58, B_59]: (v4_relat_1(C_57, A_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.14/1.46  tff(c_112, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_103])).
% 3.14/1.46  tff(c_113, plain, (![B_60, A_61]: (k7_relat_1(B_60, A_61)=B_60 | ~v4_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.14/1.46  tff(c_116, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_112, c_113])).
% 3.14/1.46  tff(c_119, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_116])).
% 3.14/1.46  tff(c_173, plain, (![B_77, A_78]: (k2_relat_1(k7_relat_1(B_77, A_78))=k9_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.14/1.46  tff(c_188, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_119, c_173])).
% 3.14/1.46  tff(c_194, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_188])).
% 3.14/1.46  tff(c_279, plain, (![A_98, B_99, C_100, D_101]: (k7_relset_1(A_98, B_99, C_100, D_101)=k9_relat_1(C_100, D_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.14/1.46  tff(c_286, plain, (![D_101]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_101)=k9_relat_1('#skF_3', D_101))), inference(resolution, [status(thm)], [c_40, c_279])).
% 3.14/1.46  tff(c_253, plain, (![A_92, B_93, C_94]: (k2_relset_1(A_92, B_93, C_94)=k2_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.14/1.46  tff(c_262, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_253])).
% 3.14/1.46  tff(c_38, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.14/1.46  tff(c_75, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_38])).
% 3.14/1.46  tff(c_263, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_262, c_75])).
% 3.14/1.46  tff(c_287, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_286, c_263])).
% 3.14/1.46  tff(c_290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_194, c_287])).
% 3.14/1.46  tff(c_291, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 3.14/1.46  tff(c_489, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_488, c_291])).
% 3.14/1.46  tff(c_575, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_566, c_489])).
% 3.14/1.46  tff(c_430, plain, (![A_131, B_132, C_133]: (k2_relset_1(A_131, B_132, C_133)=k2_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.14/1.46  tff(c_439, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_430])).
% 3.14/1.46  tff(c_292, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 3.14/1.46  tff(c_440, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_439, c_292])).
% 3.14/1.46  tff(c_520, plain, (![A_152, B_153, C_154, D_155]: (m1_subset_1(k7_relset_1(A_152, B_153, C_154, D_155), k1_zfmisc_1(B_153)) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.14/1.46  tff(c_546, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_440, c_520])).
% 3.14/1.46  tff(c_554, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_546])).
% 3.14/1.46  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.14/1.46  tff(c_570, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_554, c_8])).
% 3.14/1.46  tff(c_16, plain, (![A_9]: (k10_relat_1(A_9, k2_relat_1(A_9))=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.14/1.46  tff(c_449, plain, (![C_134, A_135, B_136]: (r1_tarski(k10_relat_1(C_134, A_135), k10_relat_1(C_134, B_136)) | ~r1_tarski(A_135, B_136) | ~v1_relat_1(C_134))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.14/1.46  tff(c_864, plain, (![A_220, B_221]: (r1_tarski(k1_relat_1(A_220), k10_relat_1(A_220, B_221)) | ~r1_tarski(k2_relat_1(A_220), B_221) | ~v1_relat_1(A_220) | ~v1_relat_1(A_220))), inference(superposition, [status(thm), theory('equality')], [c_16, c_449])).
% 3.14/1.46  tff(c_14, plain, (![B_8, A_7]: (r1_tarski(k10_relat_1(B_8, A_7), k1_relat_1(B_8)) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.14/1.46  tff(c_307, plain, (![B_105, A_106]: (B_105=A_106 | ~r1_tarski(B_105, A_106) | ~r1_tarski(A_106, B_105))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.14/1.46  tff(c_314, plain, (![B_8, A_7]: (k10_relat_1(B_8, A_7)=k1_relat_1(B_8) | ~r1_tarski(k1_relat_1(B_8), k10_relat_1(B_8, A_7)) | ~v1_relat_1(B_8))), inference(resolution, [status(thm)], [c_14, c_307])).
% 3.14/1.46  tff(c_877, plain, (![A_222, B_223]: (k10_relat_1(A_222, B_223)=k1_relat_1(A_222) | ~r1_tarski(k2_relat_1(A_222), B_223) | ~v1_relat_1(A_222))), inference(resolution, [status(thm)], [c_864, c_314])).
% 3.14/1.46  tff(c_883, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_570, c_877])).
% 3.14/1.46  tff(c_896, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_883])).
% 3.14/1.46  tff(c_898, plain, $false, inference(negUnitSimplification, [status(thm)], [c_575, c_896])).
% 3.14/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.46  
% 3.14/1.46  Inference rules
% 3.14/1.46  ----------------------
% 3.14/1.46  #Ref     : 0
% 3.14/1.46  #Sup     : 188
% 3.14/1.46  #Fact    : 0
% 3.14/1.46  #Define  : 0
% 3.14/1.46  #Split   : 4
% 3.14/1.46  #Chain   : 0
% 3.14/1.46  #Close   : 0
% 3.14/1.46  
% 3.14/1.46  Ordering : KBO
% 3.14/1.46  
% 3.14/1.46  Simplification rules
% 3.14/1.46  ----------------------
% 3.14/1.46  #Subsume      : 5
% 3.14/1.46  #Demod        : 57
% 3.14/1.46  #Tautology    : 79
% 3.14/1.46  #SimpNegUnit  : 1
% 3.14/1.46  #BackRed      : 6
% 3.14/1.46  
% 3.14/1.46  #Partial instantiations: 0
% 3.14/1.46  #Strategies tried      : 1
% 3.14/1.46  
% 3.14/1.46  Timing (in seconds)
% 3.14/1.46  ----------------------
% 3.14/1.46  Preprocessing        : 0.32
% 3.14/1.46  Parsing              : 0.18
% 3.14/1.46  CNF conversion       : 0.02
% 3.14/1.46  Main loop            : 0.37
% 3.14/1.46  Inferencing          : 0.15
% 3.14/1.46  Reduction            : 0.11
% 3.14/1.46  Demodulation         : 0.08
% 3.14/1.46  BG Simplification    : 0.02
% 3.14/1.46  Subsumption          : 0.06
% 3.14/1.46  Abstraction          : 0.02
% 3.14/1.46  MUC search           : 0.00
% 3.14/1.46  Cooper               : 0.00
% 3.14/1.46  Total                : 0.73
% 3.14/1.46  Index Insertion      : 0.00
% 3.14/1.46  Index Deletion       : 0.00
% 3.14/1.46  Index Matching       : 0.00
% 3.14/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
