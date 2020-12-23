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
% DateTime   : Thu Dec  3 10:07:50 EST 2020

% Result     : Theorem 5.72s
% Output     : CNFRefutation 5.91s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 277 expanded)
%              Number of leaves         :   47 ( 111 expanded)
%              Depth                    :   16
%              Number of atoms          :  227 ( 506 expanded)
%              Number of equality atoms :   63 ( 148 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_128,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_124,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_134,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_102,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2749,plain,(
    ! [A_328,B_329,C_330,D_331] :
      ( k8_relset_1(A_328,B_329,C_330,D_331) = k10_relat_1(C_330,D_331)
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(A_328,B_329))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2756,plain,(
    ! [D_331] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_331) = k10_relat_1('#skF_3',D_331) ),
    inference(resolution,[status(thm)],[c_68,c_2749])).

tff(c_2271,plain,(
    ! [A_301,B_302,C_303] :
      ( k1_relset_1(A_301,B_302,C_303) = k1_relat_1(C_303)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_301,B_302))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2280,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2271])).

tff(c_150,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_159,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_150])).

tff(c_399,plain,(
    ! [C_116,A_117,B_118] :
      ( v4_relat_1(C_116,A_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_408,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_399])).

tff(c_30,plain,(
    ! [B_18,A_17] :
      ( k7_relat_1(B_18,A_17) = B_18
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_411,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_408,c_30])).

tff(c_414,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_411])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_418,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_24])).

tff(c_422,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_418])).

tff(c_1466,plain,(
    ! [A_197,B_198,C_199,D_200] :
      ( k7_relset_1(A_197,B_198,C_199,D_200) = k9_relat_1(C_199,D_200)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1473,plain,(
    ! [D_200] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_200) = k9_relat_1('#skF_3',D_200) ),
    inference(resolution,[status(thm)],[c_68,c_1466])).

tff(c_874,plain,(
    ! [A_158,B_159,C_160] :
      ( k2_relset_1(A_158,B_159,C_160) = k2_relat_1(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_883,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_874])).

tff(c_66,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_103,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_884,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_103])).

tff(c_1474,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1473,c_884])).

tff(c_1477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_1474])).

tff(c_1478,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_2281,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2280,c_1478])).

tff(c_2757,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2756,c_2281])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_94,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,B_64)
      | ~ m1_subset_1(A_63,k1_zfmisc_1(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_102,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_94])).

tff(c_40,plain,(
    ! [A_26] : v1_relat_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,(
    ! [A_23] : k1_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1759,plain,(
    ! [B_254,A_255] :
      ( v4_relat_1(B_254,A_255)
      | ~ r1_tarski(k1_relat_1(B_254),A_255)
      | ~ v1_relat_1(B_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1765,plain,(
    ! [A_23,A_255] :
      ( v4_relat_1(k6_relat_1(A_23),A_255)
      | ~ r1_tarski(A_23,A_255)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1759])).

tff(c_1772,plain,(
    ! [A_23,A_255] :
      ( v4_relat_1(k6_relat_1(A_23),A_255)
      | ~ r1_tarski(A_23,A_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1765])).

tff(c_2053,plain,(
    ! [C_280,B_281,A_282] :
      ( v4_relat_1(C_280,B_281)
      | ~ v4_relat_1(C_280,A_282)
      | ~ v1_relat_1(C_280)
      | ~ r1_tarski(A_282,B_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2061,plain,(
    ! [A_23,B_281,A_255] :
      ( v4_relat_1(k6_relat_1(A_23),B_281)
      | ~ v1_relat_1(k6_relat_1(A_23))
      | ~ r1_tarski(A_255,B_281)
      | ~ r1_tarski(A_23,A_255) ) ),
    inference(resolution,[status(thm)],[c_1772,c_2053])).

tff(c_2837,plain,(
    ! [A_342,B_343,A_344] :
      ( v4_relat_1(k6_relat_1(A_342),B_343)
      | ~ r1_tarski(A_344,B_343)
      | ~ r1_tarski(A_342,A_344) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2061])).

tff(c_2893,plain,(
    ! [A_350] :
      ( v4_relat_1(k6_relat_1(A_350),k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_350,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_102,c_2837])).

tff(c_1536,plain,(
    ! [B_212,A_213] :
      ( r1_tarski(k1_relat_1(B_212),A_213)
      | ~ v4_relat_1(B_212,A_213)
      | ~ v1_relat_1(B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1541,plain,(
    ! [A_23,A_213] :
      ( r1_tarski(A_23,A_213)
      | ~ v4_relat_1(k6_relat_1(A_23),A_213)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1536])).

tff(c_1544,plain,(
    ! [A_23,A_213] :
      ( r1_tarski(A_23,A_213)
      | ~ v4_relat_1(k6_relat_1(A_23),A_213) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1541])).

tff(c_2940,plain,(
    ! [A_352] :
      ( r1_tarski(A_352,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_352,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2893,c_1544])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1578,plain,(
    ! [C_224,B_225,A_226] :
      ( v5_relat_1(C_224,B_225)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_226,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1586,plain,(
    ! [A_3,B_225,A_226] :
      ( v5_relat_1(A_3,B_225)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_226,B_225)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1578])).

tff(c_2983,plain,(
    ! [A_352] :
      ( v5_relat_1(A_352,'#skF_2')
      | ~ r1_tarski(A_352,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2940,c_1586])).

tff(c_1526,plain,(
    ! [C_209,A_210,B_211] :
      ( v1_relat_1(C_209)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1535,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1526])).

tff(c_3033,plain,(
    ! [D_358,B_359,C_360,A_361] :
      ( m1_subset_1(D_358,k1_zfmisc_1(k2_zfmisc_1(B_359,C_360)))
      | ~ r1_tarski(k1_relat_1(D_358),B_359)
      | ~ m1_subset_1(D_358,k1_zfmisc_1(k2_zfmisc_1(A_361,C_360))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3071,plain,(
    ! [B_365] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_365,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_365) ) ),
    inference(resolution,[status(thm)],[c_68,c_3033])).

tff(c_54,plain,(
    ! [C_36,A_34,B_35] :
      ( v4_relat_1(C_36,A_34)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3122,plain,(
    ! [B_367] :
      ( v4_relat_1('#skF_3',B_367)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_367) ) ),
    inference(resolution,[status(thm)],[c_3071,c_54])).

tff(c_3161,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_3122])).

tff(c_3166,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3161,c_30])).

tff(c_3172,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1535,c_3166])).

tff(c_3179,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3172,c_24])).

tff(c_3189,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1535,c_3179])).

tff(c_46,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,k10_relat_1(B_28,k9_relat_1(B_28,A_27)))
      | ~ r1_tarski(A_27,k1_relat_1(B_28))
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3238,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',k2_relat_1('#skF_3')))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3189,c_46])).

tff(c_3248,plain,(
    r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',k2_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1535,c_6,c_3238])).

tff(c_1513,plain,(
    ! [B_205,A_206] :
      ( r1_tarski(k10_relat_1(B_205,A_206),k1_relat_1(B_205))
      | ~ v1_relat_1(B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4355,plain,(
    ! [B_408,A_409] :
      ( k10_relat_1(B_408,A_409) = k1_relat_1(B_408)
      | ~ r1_tarski(k1_relat_1(B_408),k10_relat_1(B_408,A_409))
      | ~ v1_relat_1(B_408) ) ),
    inference(resolution,[status(thm)],[c_1513,c_2])).

tff(c_4361,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3248,c_4355])).

tff(c_4396,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1535,c_4361])).

tff(c_1851,plain,(
    ! [C_263,A_264,B_265] :
      ( v4_relat_1(C_263,A_264)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_264,B_265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1860,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_1851])).

tff(c_1863,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1860,c_30])).

tff(c_1866,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1535,c_1863])).

tff(c_1870,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1866,c_24])).

tff(c_1874,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1535,c_1870])).

tff(c_1674,plain,(
    ! [B_246,A_247] :
      ( r1_tarski(k2_relat_1(B_246),A_247)
      | ~ v5_relat_1(B_246,A_247)
      | ~ v1_relat_1(B_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5440,plain,(
    ! [B_454,A_455,A_456] :
      ( r1_tarski(k9_relat_1(B_454,A_455),A_456)
      | ~ v5_relat_1(k7_relat_1(B_454,A_455),A_456)
      | ~ v1_relat_1(k7_relat_1(B_454,A_455))
      | ~ v1_relat_1(B_454) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1674])).

tff(c_5462,plain,(
    ! [A_456] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),A_456)
      | ~ v5_relat_1('#skF_3',A_456)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1866,c_5440])).

tff(c_5487,plain,(
    ! [A_457] :
      ( r1_tarski(k2_relat_1('#skF_3'),A_457)
      | ~ v5_relat_1('#skF_3',A_457) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1535,c_1535,c_1866,c_1874,c_5462])).

tff(c_48,plain,(
    ! [B_30,A_29] : k5_relat_1(k6_relat_1(B_30),k6_relat_1(A_29)) = k6_relat_1(k3_xboole_0(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1654,plain,(
    ! [A_244,B_245] :
      ( k5_relat_1(k6_relat_1(A_244),B_245) = k7_relat_1(B_245,A_244)
      | ~ v1_relat_1(B_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1667,plain,(
    ! [A_29,B_30] :
      ( k7_relat_1(k6_relat_1(A_29),B_30) = k6_relat_1(k3_xboole_0(A_29,B_30))
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1654])).

tff(c_1673,plain,(
    ! [A_29,B_30] : k7_relat_1(k6_relat_1(A_29),B_30) = k6_relat_1(k3_xboole_0(A_29,B_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1667])).

tff(c_1810,plain,(
    ! [A_260,A_261] :
      ( v4_relat_1(k6_relat_1(A_260),A_261)
      | ~ r1_tarski(A_260,A_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1765])).

tff(c_1813,plain,(
    ! [A_260,A_261] :
      ( k7_relat_1(k6_relat_1(A_260),A_261) = k6_relat_1(A_260)
      | ~ v1_relat_1(k6_relat_1(A_260))
      | ~ r1_tarski(A_260,A_261) ) ),
    inference(resolution,[status(thm)],[c_1810,c_30])).

tff(c_1983,plain,(
    ! [A_278,A_279] :
      ( k6_relat_1(k3_xboole_0(A_278,A_279)) = k6_relat_1(A_278)
      | ~ r1_tarski(A_278,A_279) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1673,c_1813])).

tff(c_2028,plain,(
    ! [A_278,A_279] :
      ( k3_xboole_0(A_278,A_279) = k1_relat_1(k6_relat_1(A_278))
      | ~ r1_tarski(A_278,A_279) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1983,c_34])).

tff(c_2046,plain,(
    ! [A_278,A_279] :
      ( k3_xboole_0(A_278,A_279) = A_278
      | ~ r1_tarski(A_278,A_279) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2028])).

tff(c_5842,plain,(
    ! [A_467] :
      ( k3_xboole_0(k2_relat_1('#skF_3'),A_467) = k2_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_467) ) ),
    inference(resolution,[status(thm)],[c_5487,c_2046])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( k10_relat_1(B_16,k3_xboole_0(k2_relat_1(B_16),A_15)) = k10_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5881,plain,(
    ! [A_467] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_467)
      | ~ v1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_467) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5842,c_28])).

tff(c_5926,plain,(
    ! [A_468] :
      ( k10_relat_1('#skF_3',A_468) = k1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_468) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1535,c_4396,c_5881])).

tff(c_5933,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_2983,c_5926])).

tff(c_5945,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5933])).

tff(c_5947,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2757,c_5945])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:17:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.72/2.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.72/2.14  
% 5.72/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.72/2.14  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.72/2.14  
% 5.72/2.14  %Foreground sorts:
% 5.72/2.14  
% 5.72/2.14  
% 5.72/2.14  %Background operators:
% 5.72/2.14  
% 5.72/2.14  
% 5.72/2.14  %Foreground operators:
% 5.72/2.14  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.72/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.72/2.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.72/2.14  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 5.72/2.14  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.72/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.72/2.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.72/2.14  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.72/2.14  tff('#skF_2', type, '#skF_2': $i).
% 5.72/2.14  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.72/2.14  tff('#skF_3', type, '#skF_3': $i).
% 5.72/2.14  tff('#skF_1', type, '#skF_1': $i).
% 5.72/2.14  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.72/2.14  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.72/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.72/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.72/2.14  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.72/2.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.72/2.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.72/2.14  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.72/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.72/2.14  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.72/2.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.72/2.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.72/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.72/2.14  
% 5.91/2.16  tff(f_141, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 5.91/2.16  tff(f_128, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 5.91/2.16  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.91/2.16  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.91/2.16  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.91/2.16  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 5.91/2.16  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 5.91/2.16  tff(f_124, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.91/2.16  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.91/2.16  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.91/2.16  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.91/2.16  tff(f_94, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 5.91/2.16  tff(f_84, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 5.91/2.16  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 5.91/2.16  tff(f_80, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t217_relat_1)).
% 5.91/2.16  tff(f_134, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 5.91/2.16  tff(f_100, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 5.91/2.16  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 5.91/2.16  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 5.91/2.16  tff(f_102, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 5.91/2.16  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 5.91/2.16  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 5.91/2.16  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.91/2.16  tff(c_2749, plain, (![A_328, B_329, C_330, D_331]: (k8_relset_1(A_328, B_329, C_330, D_331)=k10_relat_1(C_330, D_331) | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(A_328, B_329))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.91/2.16  tff(c_2756, plain, (![D_331]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_331)=k10_relat_1('#skF_3', D_331))), inference(resolution, [status(thm)], [c_68, c_2749])).
% 5.91/2.16  tff(c_2271, plain, (![A_301, B_302, C_303]: (k1_relset_1(A_301, B_302, C_303)=k1_relat_1(C_303) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_301, B_302))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.91/2.16  tff(c_2280, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2271])).
% 5.91/2.16  tff(c_150, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.91/2.16  tff(c_159, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_150])).
% 5.91/2.16  tff(c_399, plain, (![C_116, A_117, B_118]: (v4_relat_1(C_116, A_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.91/2.16  tff(c_408, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_399])).
% 5.91/2.16  tff(c_30, plain, (![B_18, A_17]: (k7_relat_1(B_18, A_17)=B_18 | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.91/2.16  tff(c_411, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_408, c_30])).
% 5.91/2.16  tff(c_414, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_159, c_411])).
% 5.91/2.16  tff(c_24, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.91/2.16  tff(c_418, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_414, c_24])).
% 5.91/2.16  tff(c_422, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_418])).
% 5.91/2.16  tff(c_1466, plain, (![A_197, B_198, C_199, D_200]: (k7_relset_1(A_197, B_198, C_199, D_200)=k9_relat_1(C_199, D_200) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.91/2.16  tff(c_1473, plain, (![D_200]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_200)=k9_relat_1('#skF_3', D_200))), inference(resolution, [status(thm)], [c_68, c_1466])).
% 5.91/2.16  tff(c_874, plain, (![A_158, B_159, C_160]: (k2_relset_1(A_158, B_159, C_160)=k2_relat_1(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.91/2.16  tff(c_883, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_874])).
% 5.91/2.16  tff(c_66, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.91/2.16  tff(c_103, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 5.91/2.16  tff(c_884, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_883, c_103])).
% 5.91/2.16  tff(c_1474, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1473, c_884])).
% 5.91/2.16  tff(c_1477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_422, c_1474])).
% 5.91/2.16  tff(c_1478, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_66])).
% 5.91/2.16  tff(c_2281, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2280, c_1478])).
% 5.91/2.16  tff(c_2757, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2756, c_2281])).
% 5.91/2.16  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.91/2.16  tff(c_94, plain, (![A_63, B_64]: (r1_tarski(A_63, B_64) | ~m1_subset_1(A_63, k1_zfmisc_1(B_64)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.91/2.16  tff(c_102, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_94])).
% 5.91/2.16  tff(c_40, plain, (![A_26]: (v1_relat_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.91/2.16  tff(c_34, plain, (![A_23]: (k1_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.91/2.16  tff(c_1759, plain, (![B_254, A_255]: (v4_relat_1(B_254, A_255) | ~r1_tarski(k1_relat_1(B_254), A_255) | ~v1_relat_1(B_254))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.91/2.16  tff(c_1765, plain, (![A_23, A_255]: (v4_relat_1(k6_relat_1(A_23), A_255) | ~r1_tarski(A_23, A_255) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1759])).
% 5.91/2.16  tff(c_1772, plain, (![A_23, A_255]: (v4_relat_1(k6_relat_1(A_23), A_255) | ~r1_tarski(A_23, A_255))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1765])).
% 5.91/2.16  tff(c_2053, plain, (![C_280, B_281, A_282]: (v4_relat_1(C_280, B_281) | ~v4_relat_1(C_280, A_282) | ~v1_relat_1(C_280) | ~r1_tarski(A_282, B_281))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.91/2.16  tff(c_2061, plain, (![A_23, B_281, A_255]: (v4_relat_1(k6_relat_1(A_23), B_281) | ~v1_relat_1(k6_relat_1(A_23)) | ~r1_tarski(A_255, B_281) | ~r1_tarski(A_23, A_255))), inference(resolution, [status(thm)], [c_1772, c_2053])).
% 5.91/2.16  tff(c_2837, plain, (![A_342, B_343, A_344]: (v4_relat_1(k6_relat_1(A_342), B_343) | ~r1_tarski(A_344, B_343) | ~r1_tarski(A_342, A_344))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2061])).
% 5.91/2.16  tff(c_2893, plain, (![A_350]: (v4_relat_1(k6_relat_1(A_350), k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_350, '#skF_3'))), inference(resolution, [status(thm)], [c_102, c_2837])).
% 5.91/2.16  tff(c_1536, plain, (![B_212, A_213]: (r1_tarski(k1_relat_1(B_212), A_213) | ~v4_relat_1(B_212, A_213) | ~v1_relat_1(B_212))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.91/2.16  tff(c_1541, plain, (![A_23, A_213]: (r1_tarski(A_23, A_213) | ~v4_relat_1(k6_relat_1(A_23), A_213) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1536])).
% 5.91/2.16  tff(c_1544, plain, (![A_23, A_213]: (r1_tarski(A_23, A_213) | ~v4_relat_1(k6_relat_1(A_23), A_213))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1541])).
% 5.91/2.16  tff(c_2940, plain, (![A_352]: (r1_tarski(A_352, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_352, '#skF_3'))), inference(resolution, [status(thm)], [c_2893, c_1544])).
% 5.91/2.16  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.91/2.16  tff(c_1578, plain, (![C_224, B_225, A_226]: (v5_relat_1(C_224, B_225) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_226, B_225))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.91/2.16  tff(c_1586, plain, (![A_3, B_225, A_226]: (v5_relat_1(A_3, B_225) | ~r1_tarski(A_3, k2_zfmisc_1(A_226, B_225)))), inference(resolution, [status(thm)], [c_10, c_1578])).
% 5.91/2.16  tff(c_2983, plain, (![A_352]: (v5_relat_1(A_352, '#skF_2') | ~r1_tarski(A_352, '#skF_3'))), inference(resolution, [status(thm)], [c_2940, c_1586])).
% 5.91/2.16  tff(c_1526, plain, (![C_209, A_210, B_211]: (v1_relat_1(C_209) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.91/2.16  tff(c_1535, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1526])).
% 5.91/2.16  tff(c_3033, plain, (![D_358, B_359, C_360, A_361]: (m1_subset_1(D_358, k1_zfmisc_1(k2_zfmisc_1(B_359, C_360))) | ~r1_tarski(k1_relat_1(D_358), B_359) | ~m1_subset_1(D_358, k1_zfmisc_1(k2_zfmisc_1(A_361, C_360))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 5.91/2.16  tff(c_3071, plain, (![B_365]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_365, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_365))), inference(resolution, [status(thm)], [c_68, c_3033])).
% 5.91/2.16  tff(c_54, plain, (![C_36, A_34, B_35]: (v4_relat_1(C_36, A_34) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.91/2.16  tff(c_3122, plain, (![B_367]: (v4_relat_1('#skF_3', B_367) | ~r1_tarski(k1_relat_1('#skF_3'), B_367))), inference(resolution, [status(thm)], [c_3071, c_54])).
% 5.91/2.16  tff(c_3161, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_3122])).
% 5.91/2.16  tff(c_3166, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3161, c_30])).
% 5.91/2.16  tff(c_3172, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1535, c_3166])).
% 5.91/2.16  tff(c_3179, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3172, c_24])).
% 5.91/2.16  tff(c_3189, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1535, c_3179])).
% 5.91/2.16  tff(c_46, plain, (![A_27, B_28]: (r1_tarski(A_27, k10_relat_1(B_28, k9_relat_1(B_28, A_27))) | ~r1_tarski(A_27, k1_relat_1(B_28)) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.91/2.16  tff(c_3238, plain, (r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', k2_relat_1('#skF_3'))) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3189, c_46])).
% 5.91/2.16  tff(c_3248, plain, (r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1535, c_6, c_3238])).
% 5.91/2.16  tff(c_1513, plain, (![B_205, A_206]: (r1_tarski(k10_relat_1(B_205, A_206), k1_relat_1(B_205)) | ~v1_relat_1(B_205))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.91/2.16  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.91/2.16  tff(c_4355, plain, (![B_408, A_409]: (k10_relat_1(B_408, A_409)=k1_relat_1(B_408) | ~r1_tarski(k1_relat_1(B_408), k10_relat_1(B_408, A_409)) | ~v1_relat_1(B_408))), inference(resolution, [status(thm)], [c_1513, c_2])).
% 5.91/2.16  tff(c_4361, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3248, c_4355])).
% 5.91/2.16  tff(c_4396, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1535, c_4361])).
% 5.91/2.16  tff(c_1851, plain, (![C_263, A_264, B_265]: (v4_relat_1(C_263, A_264) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_264, B_265))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.91/2.16  tff(c_1860, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_1851])).
% 5.91/2.16  tff(c_1863, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1860, c_30])).
% 5.91/2.16  tff(c_1866, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1535, c_1863])).
% 5.91/2.16  tff(c_1870, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1866, c_24])).
% 5.91/2.16  tff(c_1874, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1535, c_1870])).
% 5.91/2.16  tff(c_1674, plain, (![B_246, A_247]: (r1_tarski(k2_relat_1(B_246), A_247) | ~v5_relat_1(B_246, A_247) | ~v1_relat_1(B_246))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.91/2.16  tff(c_5440, plain, (![B_454, A_455, A_456]: (r1_tarski(k9_relat_1(B_454, A_455), A_456) | ~v5_relat_1(k7_relat_1(B_454, A_455), A_456) | ~v1_relat_1(k7_relat_1(B_454, A_455)) | ~v1_relat_1(B_454))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1674])).
% 5.91/2.16  tff(c_5462, plain, (![A_456]: (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), A_456) | ~v5_relat_1('#skF_3', A_456) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1866, c_5440])).
% 5.91/2.16  tff(c_5487, plain, (![A_457]: (r1_tarski(k2_relat_1('#skF_3'), A_457) | ~v5_relat_1('#skF_3', A_457))), inference(demodulation, [status(thm), theory('equality')], [c_1535, c_1535, c_1866, c_1874, c_5462])).
% 5.91/2.16  tff(c_48, plain, (![B_30, A_29]: (k5_relat_1(k6_relat_1(B_30), k6_relat_1(A_29))=k6_relat_1(k3_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.91/2.16  tff(c_1654, plain, (![A_244, B_245]: (k5_relat_1(k6_relat_1(A_244), B_245)=k7_relat_1(B_245, A_244) | ~v1_relat_1(B_245))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.91/2.16  tff(c_1667, plain, (![A_29, B_30]: (k7_relat_1(k6_relat_1(A_29), B_30)=k6_relat_1(k3_xboole_0(A_29, B_30)) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1654])).
% 5.91/2.16  tff(c_1673, plain, (![A_29, B_30]: (k7_relat_1(k6_relat_1(A_29), B_30)=k6_relat_1(k3_xboole_0(A_29, B_30)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1667])).
% 5.91/2.16  tff(c_1810, plain, (![A_260, A_261]: (v4_relat_1(k6_relat_1(A_260), A_261) | ~r1_tarski(A_260, A_261))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1765])).
% 5.91/2.16  tff(c_1813, plain, (![A_260, A_261]: (k7_relat_1(k6_relat_1(A_260), A_261)=k6_relat_1(A_260) | ~v1_relat_1(k6_relat_1(A_260)) | ~r1_tarski(A_260, A_261))), inference(resolution, [status(thm)], [c_1810, c_30])).
% 5.91/2.16  tff(c_1983, plain, (![A_278, A_279]: (k6_relat_1(k3_xboole_0(A_278, A_279))=k6_relat_1(A_278) | ~r1_tarski(A_278, A_279))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1673, c_1813])).
% 5.91/2.16  tff(c_2028, plain, (![A_278, A_279]: (k3_xboole_0(A_278, A_279)=k1_relat_1(k6_relat_1(A_278)) | ~r1_tarski(A_278, A_279))), inference(superposition, [status(thm), theory('equality')], [c_1983, c_34])).
% 5.91/2.16  tff(c_2046, plain, (![A_278, A_279]: (k3_xboole_0(A_278, A_279)=A_278 | ~r1_tarski(A_278, A_279))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2028])).
% 5.91/2.16  tff(c_5842, plain, (![A_467]: (k3_xboole_0(k2_relat_1('#skF_3'), A_467)=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_467))), inference(resolution, [status(thm)], [c_5487, c_2046])).
% 5.91/2.16  tff(c_28, plain, (![B_16, A_15]: (k10_relat_1(B_16, k3_xboole_0(k2_relat_1(B_16), A_15))=k10_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.91/2.16  tff(c_5881, plain, (![A_467]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_467) | ~v1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_467))), inference(superposition, [status(thm), theory('equality')], [c_5842, c_28])).
% 5.91/2.16  tff(c_5926, plain, (![A_468]: (k10_relat_1('#skF_3', A_468)=k1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_468))), inference(demodulation, [status(thm), theory('equality')], [c_1535, c_4396, c_5881])).
% 5.91/2.16  tff(c_5933, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_2983, c_5926])).
% 5.91/2.16  tff(c_5945, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5933])).
% 5.91/2.16  tff(c_5947, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2757, c_5945])).
% 5.91/2.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.91/2.17  
% 5.91/2.17  Inference rules
% 5.91/2.17  ----------------------
% 5.91/2.17  #Ref     : 0
% 5.91/2.17  #Sup     : 1255
% 5.91/2.17  #Fact    : 0
% 5.91/2.17  #Define  : 0
% 5.91/2.17  #Split   : 10
% 5.91/2.17  #Chain   : 0
% 5.91/2.17  #Close   : 0
% 5.91/2.17  
% 5.91/2.17  Ordering : KBO
% 5.91/2.17  
% 5.91/2.17  Simplification rules
% 5.91/2.17  ----------------------
% 5.91/2.17  #Subsume      : 122
% 5.91/2.17  #Demod        : 987
% 5.91/2.17  #Tautology    : 546
% 5.91/2.17  #SimpNegUnit  : 5
% 5.91/2.17  #BackRed      : 16
% 5.91/2.17  
% 5.91/2.17  #Partial instantiations: 0
% 5.91/2.17  #Strategies tried      : 1
% 5.91/2.17  
% 5.91/2.17  Timing (in seconds)
% 5.91/2.17  ----------------------
% 5.91/2.17  Preprocessing        : 0.35
% 5.91/2.17  Parsing              : 0.19
% 5.91/2.17  CNF conversion       : 0.02
% 5.91/2.17  Main loop            : 1.06
% 5.91/2.17  Inferencing          : 0.36
% 5.91/2.17  Reduction            : 0.38
% 5.91/2.17  Demodulation         : 0.27
% 5.91/2.17  BG Simplification    : 0.05
% 5.91/2.17  Subsumption          : 0.19
% 5.91/2.17  Abstraction          : 0.05
% 5.91/2.17  MUC search           : 0.00
% 5.91/2.17  Cooper               : 0.00
% 5.91/2.17  Total                : 1.45
% 5.91/2.17  Index Insertion      : 0.00
% 5.91/2.17  Index Deletion       : 0.00
% 5.91/2.17  Index Matching       : 0.00
% 5.91/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
