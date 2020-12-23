%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:51 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 120 expanded)
%              Number of leaves         :   40 (  57 expanded)
%              Depth                    :    7
%              Number of atoms          :  109 ( 180 expanded)
%              Number of equality atoms :   47 (  73 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_58,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_62,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_58])).

tff(c_316,plain,(
    ! [C_94,B_95,A_96] :
      ( v5_relat_1(C_94,B_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_320,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_316])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_345,plain,(
    ! [A_100,B_101] :
      ( k8_relat_1(A_100,B_101) = B_101
      | ~ r1_tarski(k2_relat_1(B_101),A_100)
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_358,plain,(
    ! [A_102,B_103] :
      ( k8_relat_1(A_102,B_103) = B_103
      | ~ v5_relat_1(B_103,A_102)
      | ~ v1_relat_1(B_103) ) ),
    inference(resolution,[status(thm)],[c_4,c_345])).

tff(c_361,plain,
    ( k8_relat_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_320,c_358])).

tff(c_367,plain,(
    k8_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_361])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_relat_1(A_4)) = k8_relat_1(A_4,B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_384,plain,(
    ! [A_106,B_107] :
      ( k10_relat_1(A_106,k1_relat_1(B_107)) = k1_relat_1(k5_relat_1(A_106,B_107))
      | ~ v1_relat_1(B_107)
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_393,plain,(
    ! [A_106,A_15] :
      ( k1_relat_1(k5_relat_1(A_106,k6_relat_1(A_15))) = k10_relat_1(A_106,A_15)
      | ~ v1_relat_1(k6_relat_1(A_15))
      | ~ v1_relat_1(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_384])).

tff(c_398,plain,(
    ! [A_108,A_109] :
      ( k1_relat_1(k5_relat_1(A_108,k6_relat_1(A_109))) = k10_relat_1(A_108,A_109)
      | ~ v1_relat_1(A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_393])).

tff(c_413,plain,(
    ! [A_110,B_111] :
      ( k1_relat_1(k8_relat_1(A_110,B_111)) = k10_relat_1(B_111,A_110)
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_398])).

tff(c_428,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_413])).

tff(c_434,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_62,c_428])).

tff(c_480,plain,(
    ! [A_120,B_121,C_122,D_123] :
      ( k8_relset_1(A_120,B_121,C_122,D_123) = k10_relat_1(C_122,D_123)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_483,plain,(
    ! [D_123] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_123) = k10_relat_1('#skF_3',D_123) ),
    inference(resolution,[status(thm)],[c_38,c_480])).

tff(c_439,plain,(
    ! [A_112,B_113,C_114] :
      ( k1_relset_1(A_112,B_113,C_114) = k1_relat_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_443,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_439])).

tff(c_111,plain,(
    ! [C_56,A_57,B_58] :
      ( v4_relat_1(C_56,A_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_115,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_111])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_123,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_115,c_16])).

tff(c_126,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_123])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_130,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_12])).

tff(c_134,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_130])).

tff(c_270,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( k7_relset_1(A_82,B_83,C_84,D_85) = k9_relat_1(C_84,D_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_273,plain,(
    ! [D_85] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_85) = k9_relat_1('#skF_3',D_85) ),
    inference(resolution,[status(thm)],[c_38,c_270])).

tff(c_179,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_183,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_179])).

tff(c_36,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_82,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_184,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_82])).

tff(c_278,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_184])).

tff(c_281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_278])).

tff(c_282,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_444,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_282])).

tff(c_488,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_444])).

tff(c_491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_488])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:54:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.42  
% 2.42/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.42  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.42/1.42  
% 2.42/1.42  %Foreground sorts:
% 2.42/1.42  
% 2.42/1.42  
% 2.42/1.42  %Background operators:
% 2.42/1.42  
% 2.42/1.42  
% 2.42/1.42  %Foreground operators:
% 2.42/1.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.42/1.42  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.42/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.42/1.42  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.42/1.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.42/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.42/1.42  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.42/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.42/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.42/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.42/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.42/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.42  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.42/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.42/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.42/1.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.42/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.42/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.42/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.42/1.42  
% 2.42/1.44  tff(f_97, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.42/1.44  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.42/1.44  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.42/1.44  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.42/1.44  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.42/1.44  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.42/1.44  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.42/1.44  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.42/1.44  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.42/1.44  tff(f_90, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.42/1.44  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.42/1.44  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.42/1.44  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.42/1.44  tff(f_86, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.42/1.44  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.42/1.44  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.42/1.44  tff(c_58, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.42/1.44  tff(c_62, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_58])).
% 2.42/1.44  tff(c_316, plain, (![C_94, B_95, A_96]: (v5_relat_1(C_94, B_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.42/1.44  tff(c_320, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_316])).
% 2.42/1.44  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.42/1.44  tff(c_345, plain, (![A_100, B_101]: (k8_relat_1(A_100, B_101)=B_101 | ~r1_tarski(k2_relat_1(B_101), A_100) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.42/1.44  tff(c_358, plain, (![A_102, B_103]: (k8_relat_1(A_102, B_103)=B_103 | ~v5_relat_1(B_103, A_102) | ~v1_relat_1(B_103))), inference(resolution, [status(thm)], [c_4, c_345])).
% 2.42/1.44  tff(c_361, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_320, c_358])).
% 2.42/1.44  tff(c_367, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_361])).
% 2.42/1.44  tff(c_8, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_relat_1(A_4))=k8_relat_1(A_4, B_5) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.42/1.44  tff(c_6, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.42/1.44  tff(c_18, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.42/1.44  tff(c_384, plain, (![A_106, B_107]: (k10_relat_1(A_106, k1_relat_1(B_107))=k1_relat_1(k5_relat_1(A_106, B_107)) | ~v1_relat_1(B_107) | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.42/1.44  tff(c_393, plain, (![A_106, A_15]: (k1_relat_1(k5_relat_1(A_106, k6_relat_1(A_15)))=k10_relat_1(A_106, A_15) | ~v1_relat_1(k6_relat_1(A_15)) | ~v1_relat_1(A_106))), inference(superposition, [status(thm), theory('equality')], [c_18, c_384])).
% 2.42/1.44  tff(c_398, plain, (![A_108, A_109]: (k1_relat_1(k5_relat_1(A_108, k6_relat_1(A_109)))=k10_relat_1(A_108, A_109) | ~v1_relat_1(A_108))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_393])).
% 2.42/1.44  tff(c_413, plain, (![A_110, B_111]: (k1_relat_1(k8_relat_1(A_110, B_111))=k10_relat_1(B_111, A_110) | ~v1_relat_1(B_111) | ~v1_relat_1(B_111))), inference(superposition, [status(thm), theory('equality')], [c_8, c_398])).
% 2.42/1.44  tff(c_428, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_367, c_413])).
% 2.42/1.44  tff(c_434, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_62, c_428])).
% 2.42/1.44  tff(c_480, plain, (![A_120, B_121, C_122, D_123]: (k8_relset_1(A_120, B_121, C_122, D_123)=k10_relat_1(C_122, D_123) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.42/1.44  tff(c_483, plain, (![D_123]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_123)=k10_relat_1('#skF_3', D_123))), inference(resolution, [status(thm)], [c_38, c_480])).
% 2.42/1.44  tff(c_439, plain, (![A_112, B_113, C_114]: (k1_relset_1(A_112, B_113, C_114)=k1_relat_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.42/1.44  tff(c_443, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_439])).
% 2.42/1.44  tff(c_111, plain, (![C_56, A_57, B_58]: (v4_relat_1(C_56, A_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.42/1.44  tff(c_115, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_111])).
% 2.42/1.44  tff(c_16, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.42/1.44  tff(c_123, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_115, c_16])).
% 2.42/1.44  tff(c_126, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_123])).
% 2.42/1.44  tff(c_12, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.42/1.44  tff(c_130, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_126, c_12])).
% 2.42/1.44  tff(c_134, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_130])).
% 2.42/1.44  tff(c_270, plain, (![A_82, B_83, C_84, D_85]: (k7_relset_1(A_82, B_83, C_84, D_85)=k9_relat_1(C_84, D_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.42/1.44  tff(c_273, plain, (![D_85]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_85)=k9_relat_1('#skF_3', D_85))), inference(resolution, [status(thm)], [c_38, c_270])).
% 2.42/1.44  tff(c_179, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.42/1.44  tff(c_183, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_179])).
% 2.42/1.44  tff(c_36, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.42/1.44  tff(c_82, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_36])).
% 2.42/1.44  tff(c_184, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_82])).
% 2.42/1.44  tff(c_278, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_273, c_184])).
% 2.42/1.44  tff(c_281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_278])).
% 2.42/1.44  tff(c_282, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 2.42/1.44  tff(c_444, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_443, c_282])).
% 2.42/1.44  tff(c_488, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_483, c_444])).
% 2.42/1.44  tff(c_491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_434, c_488])).
% 2.42/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.44  
% 2.42/1.44  Inference rules
% 2.42/1.44  ----------------------
% 2.42/1.44  #Ref     : 0
% 2.42/1.44  #Sup     : 109
% 2.42/1.44  #Fact    : 0
% 2.42/1.44  #Define  : 0
% 2.42/1.44  #Split   : 1
% 2.42/1.44  #Chain   : 0
% 2.42/1.44  #Close   : 0
% 2.42/1.44  
% 2.42/1.44  Ordering : KBO
% 2.42/1.44  
% 2.42/1.44  Simplification rules
% 2.42/1.44  ----------------------
% 2.42/1.44  #Subsume      : 2
% 2.42/1.44  #Demod        : 36
% 2.42/1.44  #Tautology    : 62
% 2.42/1.44  #SimpNegUnit  : 0
% 2.42/1.44  #BackRed      : 5
% 2.42/1.44  
% 2.42/1.44  #Partial instantiations: 0
% 2.42/1.44  #Strategies tried      : 1
% 2.42/1.44  
% 2.42/1.44  Timing (in seconds)
% 2.42/1.44  ----------------------
% 2.42/1.44  Preprocessing        : 0.34
% 2.42/1.44  Parsing              : 0.19
% 2.42/1.44  CNF conversion       : 0.02
% 2.42/1.44  Main loop            : 0.26
% 2.42/1.44  Inferencing          : 0.11
% 2.42/1.44  Reduction            : 0.08
% 2.42/1.44  Demodulation         : 0.06
% 2.42/1.44  BG Simplification    : 0.02
% 2.42/1.44  Subsumption          : 0.03
% 2.42/1.44  Abstraction          : 0.01
% 2.42/1.44  MUC search           : 0.00
% 2.42/1.44  Cooper               : 0.00
% 2.42/1.44  Total                : 0.64
% 2.42/1.44  Index Insertion      : 0.00
% 2.42/1.44  Index Deletion       : 0.00
% 2.42/1.44  Index Matching       : 0.00
% 2.42/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
