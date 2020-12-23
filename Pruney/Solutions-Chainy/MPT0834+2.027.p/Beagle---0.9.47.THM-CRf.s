%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:53 EST 2020

% Result     : Theorem 7.14s
% Output     : CNFRefutation 7.30s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 657 expanded)
%              Number of leaves         :   49 ( 241 expanded)
%              Depth                    :   19
%              Number of atoms          :  258 (1269 expanded)
%              Number of equality atoms :   74 ( 310 expanded)
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

tff(f_147,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_134,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_130,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_126,axiom,(
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

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_104,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_112,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_140,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_3542,plain,(
    ! [A_415,B_416,C_417,D_418] :
      ( k8_relset_1(A_415,B_416,C_417,D_418) = k10_relat_1(C_417,D_418)
      | ~ m1_subset_1(C_417,k1_zfmisc_1(k2_zfmisc_1(A_415,B_416))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_3549,plain,(
    ! [D_418] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_418) = k10_relat_1('#skF_3',D_418) ),
    inference(resolution,[status(thm)],[c_66,c_3542])).

tff(c_3163,plain,(
    ! [A_387,B_388,C_389] :
      ( k1_relset_1(A_387,B_388,C_389) = k1_relat_1(C_389)
      | ~ m1_subset_1(C_389,k1_zfmisc_1(k2_zfmisc_1(A_387,B_388))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_3172,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_3163])).

tff(c_20,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_116,plain,(
    ! [B_75,A_76] :
      ( v1_relat_1(B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76))
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_122,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_116])).

tff(c_126,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_122])).

tff(c_260,plain,(
    ! [C_106,A_107,B_108] :
      ( v4_relat_1(C_106,A_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_269,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_260])).

tff(c_441,plain,(
    ! [B_134,A_135] :
      ( k7_relat_1(B_134,A_135) = B_134
      | ~ v4_relat_1(B_134,A_135)
      | ~ v1_relat_1(B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_453,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_269,c_441])).

tff(c_464,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_453])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( k2_relat_1(k7_relat_1(B_16,A_15)) = k9_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_471,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_22])).

tff(c_478,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_471])).

tff(c_1569,plain,(
    ! [A_216,B_217,C_218,D_219] :
      ( k7_relset_1(A_216,B_217,C_218,D_219) = k9_relat_1(C_218,D_219)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1576,plain,(
    ! [D_219] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_219) = k9_relat_1('#skF_3',D_219) ),
    inference(resolution,[status(thm)],[c_66,c_1569])).

tff(c_786,plain,(
    ! [A_158,B_159,C_160] :
      ( k2_relset_1(A_158,B_159,C_160) = k2_relat_1(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_795,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_786])).

tff(c_64,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_96,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_796,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_795,c_96])).

tff(c_1577,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1576,c_796])).

tff(c_1580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_1577])).

tff(c_1581,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_3173,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3172,c_1581])).

tff(c_3550,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3549,c_3173])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(A_67,B_68)
      | ~ m1_subset_1(A_67,k1_zfmisc_1(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_95,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_91])).

tff(c_1750,plain,(
    ! [A_262,C_263,B_264] :
      ( r1_tarski(A_262,C_263)
      | ~ r1_tarski(B_264,C_263)
      | ~ r1_tarski(A_262,B_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1769,plain,(
    ! [A_265] :
      ( r1_tarski(A_265,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_265,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_95,c_1750])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1655,plain,(
    ! [C_236,B_237,A_238] :
      ( v5_relat_1(C_236,B_237)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_238,B_237))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1663,plain,(
    ! [A_6,B_237,A_238] :
      ( v5_relat_1(A_6,B_237)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_238,B_237)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1655])).

tff(c_1785,plain,(
    ! [A_265] :
      ( v5_relat_1(A_265,'#skF_2')
      | ~ r1_tarski(A_265,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1769,c_1663])).

tff(c_1619,plain,(
    ! [B_230,A_231] :
      ( v1_relat_1(B_230)
      | ~ m1_subset_1(B_230,k1_zfmisc_1(A_231))
      | ~ v1_relat_1(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1625,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_1619])).

tff(c_1629,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1625])).

tff(c_26,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k10_relat_1(B_21,A_20),k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1687,plain,(
    ! [C_244,A_245,B_246] :
      ( v4_relat_1(C_244,A_245)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1696,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_1687])).

tff(c_1866,plain,(
    ! [B_278,A_279] :
      ( k7_relat_1(B_278,A_279) = B_278
      | ~ v4_relat_1(B_278,A_279)
      | ~ v1_relat_1(B_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1878,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1696,c_1866])).

tff(c_1889,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1629,c_1878])).

tff(c_38,plain,(
    ! [B_32,A_31] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_32,A_31)),A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1896,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1889,c_38])).

tff(c_1900,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1629,c_1896])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1998,plain,(
    ! [A_286] :
      ( r1_tarski(A_286,'#skF_1')
      | ~ r1_tarski(A_286,k1_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1900,c_8])).

tff(c_2010,plain,(
    ! [A_20] :
      ( r1_tarski(k10_relat_1('#skF_3',A_20),'#skF_1')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_1998])).

tff(c_2023,plain,(
    ! [A_20] : r1_tarski(k10_relat_1('#skF_3',A_20),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1629,c_2010])).

tff(c_40,plain,(
    ! [A_33] : v1_relat_1(k6_relat_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_36,plain,(
    ! [A_30] : k2_relat_1(k6_relat_1(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_48,plain,(
    ! [B_37,A_36] : k5_relat_1(k6_relat_1(B_37),k6_relat_1(A_36)) = k6_relat_1(k3_xboole_0(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2855,plain,(
    ! [B_365,A_366] :
      ( k9_relat_1(B_365,k2_relat_1(A_366)) = k2_relat_1(k5_relat_1(A_366,B_365))
      | ~ v1_relat_1(B_365)
      | ~ v1_relat_1(A_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2891,plain,(
    ! [A_30,B_365] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_30),B_365)) = k9_relat_1(B_365,A_30)
      | ~ v1_relat_1(B_365)
      | ~ v1_relat_1(k6_relat_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_2855])).

tff(c_3560,plain,(
    ! [A_420,B_421] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_420),B_421)) = k9_relat_1(B_421,A_420)
      | ~ v1_relat_1(B_421) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2891])).

tff(c_3587,plain,(
    ! [A_36,B_37] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_36,B_37))) = k9_relat_1(k6_relat_1(A_36),B_37)
      | ~ v1_relat_1(k6_relat_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_3560])).

tff(c_3591,plain,(
    ! [A_36,B_37] : k9_relat_1(k6_relat_1(A_36),B_37) = k3_xboole_0(A_36,B_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_3587])).

tff(c_42,plain,(
    ! [A_33] : v4_relat_1(k6_relat_1(A_33),A_33) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2239,plain,(
    ! [C_316,B_317,A_318] :
      ( v4_relat_1(C_316,B_317)
      | ~ v4_relat_1(C_316,A_318)
      | ~ v1_relat_1(C_316)
      | ~ r1_tarski(A_318,B_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2251,plain,(
    ! [A_33,B_317] :
      ( v4_relat_1(k6_relat_1(A_33),B_317)
      | ~ v1_relat_1(k6_relat_1(A_33))
      | ~ r1_tarski(A_33,B_317) ) ),
    inference(resolution,[status(thm)],[c_42,c_2239])).

tff(c_2276,plain,(
    ! [A_320,B_321] :
      ( v4_relat_1(k6_relat_1(A_320),B_321)
      | ~ r1_tarski(A_320,B_321) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2251])).

tff(c_30,plain,(
    ! [B_25,A_24] :
      ( k7_relat_1(B_25,A_24) = B_25
      | ~ v4_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2281,plain,(
    ! [A_320,B_321] :
      ( k7_relat_1(k6_relat_1(A_320),B_321) = k6_relat_1(A_320)
      | ~ v1_relat_1(k6_relat_1(A_320))
      | ~ r1_tarski(A_320,B_321) ) ),
    inference(resolution,[status(thm)],[c_2276,c_30])).

tff(c_2356,plain,(
    ! [A_331,B_332] :
      ( k7_relat_1(k6_relat_1(A_331),B_332) = k6_relat_1(A_331)
      | ~ r1_tarski(A_331,B_332) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2281])).

tff(c_2365,plain,(
    ! [A_331,B_332] :
      ( k9_relat_1(k6_relat_1(A_331),B_332) = k2_relat_1(k6_relat_1(A_331))
      | ~ v1_relat_1(k6_relat_1(A_331))
      | ~ r1_tarski(A_331,B_332) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2356,c_22])).

tff(c_2387,plain,(
    ! [A_331,B_332] :
      ( k9_relat_1(k6_relat_1(A_331),B_332) = A_331
      | ~ r1_tarski(A_331,B_332) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_2365])).

tff(c_3668,plain,(
    ! [A_427,B_428] :
      ( k3_xboole_0(A_427,B_428) = A_427
      | ~ r1_tarski(A_427,B_428) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3591,c_2387])).

tff(c_3760,plain,(
    ! [A_20] : k3_xboole_0(k10_relat_1('#skF_3',A_20),'#skF_1') = k10_relat_1('#skF_3',A_20) ),
    inference(resolution,[status(thm)],[c_2023,c_3668])).

tff(c_28,plain,(
    ! [B_23,A_22] :
      ( k10_relat_1(B_23,k3_xboole_0(k2_relat_1(B_23),A_22)) = k10_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3803,plain,(
    ! [A_434] : k3_xboole_0(k10_relat_1('#skF_3',A_434),'#skF_1') = k10_relat_1('#skF_3',A_434) ),
    inference(resolution,[status(thm)],[c_2023,c_3668])).

tff(c_3813,plain,(
    ! [A_22] :
      ( k10_relat_1('#skF_3',k3_xboole_0(k2_relat_1('#skF_3'),A_22)) = k3_xboole_0(k10_relat_1('#skF_3',A_22),'#skF_1')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_3803])).

tff(c_3861,plain,(
    ! [A_442] : k10_relat_1('#skF_3',k3_xboole_0(k2_relat_1('#skF_3'),A_442)) = k10_relat_1('#skF_3',A_442) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1629,c_3760,c_3813])).

tff(c_3889,plain,(
    ! [A_442] :
      ( r1_tarski(k10_relat_1('#skF_3',A_442),k1_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3861,c_26])).

tff(c_3918,plain,(
    ! [A_442] : r1_tarski(k10_relat_1('#skF_3',A_442),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1629,c_3889])).

tff(c_3959,plain,(
    ! [D_444,B_445,C_446,A_447] :
      ( m1_subset_1(D_444,k1_zfmisc_1(k2_zfmisc_1(B_445,C_446)))
      | ~ r1_tarski(k1_relat_1(D_444),B_445)
      | ~ m1_subset_1(D_444,k1_zfmisc_1(k2_zfmisc_1(A_447,C_446))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_3968,plain,(
    ! [B_448] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_448,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_448) ) ),
    inference(resolution,[status(thm)],[c_66,c_3959])).

tff(c_52,plain,(
    ! [C_40,A_38,B_39] :
      ( v4_relat_1(C_40,A_38)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4005,plain,(
    ! [B_449] :
      ( v4_relat_1('#skF_3',B_449)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_449) ) ),
    inference(resolution,[status(thm)],[c_3968,c_52])).

tff(c_4025,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_4005])).

tff(c_4030,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4025,c_30])).

tff(c_4036,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1629,c_4030])).

tff(c_4046,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4036,c_22])).

tff(c_4058,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1629,c_4046])).

tff(c_46,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,k10_relat_1(B_35,k9_relat_1(B_35,A_34)))
      | ~ r1_tarski(A_34,k1_relat_1(B_35))
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4065,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',k2_relat_1('#skF_3')))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4058,c_46])).

tff(c_4069,plain,(
    r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',k2_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1629,c_6,c_4065])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4090,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k10_relat_1('#skF_3',k2_relat_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4069,c_2])).

tff(c_4103,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3918,c_4090])).

tff(c_1954,plain,(
    ! [B_283,A_284] :
      ( k2_relat_1(k7_relat_1(B_283,A_284)) = k9_relat_1(B_283,A_284)
      | ~ v1_relat_1(B_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1978,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1889,c_1954])).

tff(c_1984,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1629,c_1978])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8494,plain,(
    ! [B_598,A_599,A_600] :
      ( r1_tarski(k9_relat_1(B_598,A_599),A_600)
      | ~ v5_relat_1(k7_relat_1(B_598,A_599),A_600)
      | ~ v1_relat_1(k7_relat_1(B_598,A_599))
      | ~ v1_relat_1(B_598) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1954,c_18])).

tff(c_8519,plain,(
    ! [A_600] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),A_600)
      | ~ v5_relat_1('#skF_3',A_600)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1889,c_8494])).

tff(c_8545,plain,(
    ! [A_601] :
      ( r1_tarski(k2_relat_1('#skF_3'),A_601)
      | ~ v5_relat_1('#skF_3',A_601) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1629,c_1629,c_1889,c_1984,c_8519])).

tff(c_3619,plain,(
    ! [A_331,B_332] :
      ( k3_xboole_0(A_331,B_332) = A_331
      | ~ r1_tarski(A_331,B_332) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3591,c_2387])).

tff(c_8988,plain,(
    ! [A_612] :
      ( k3_xboole_0(k2_relat_1('#skF_3'),A_612) = k2_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_612) ) ),
    inference(resolution,[status(thm)],[c_8545,c_3619])).

tff(c_3817,plain,(
    ! [A_22] : k10_relat_1('#skF_3',k3_xboole_0(k2_relat_1('#skF_3'),A_22)) = k10_relat_1('#skF_3',A_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1629,c_3760,c_3813])).

tff(c_9001,plain,(
    ! [A_612] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_612)
      | ~ v5_relat_1('#skF_3',A_612) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8988,c_3817])).

tff(c_9036,plain,(
    ! [A_613] :
      ( k10_relat_1('#skF_3',A_613) = k1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_613) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4103,c_9001])).

tff(c_9044,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1785,c_9036])).

tff(c_9057,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9044])).

tff(c_9059,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3550,c_9057])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:03:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.14/2.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.14/2.71  
% 7.14/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.14/2.71  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 7.14/2.71  
% 7.14/2.71  %Foreground sorts:
% 7.14/2.71  
% 7.14/2.71  
% 7.14/2.71  %Background operators:
% 7.14/2.71  
% 7.14/2.71  
% 7.14/2.71  %Foreground operators:
% 7.14/2.71  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.14/2.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.14/2.71  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.14/2.71  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 7.14/2.71  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.14/2.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.14/2.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.14/2.71  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 7.14/2.71  tff('#skF_2', type, '#skF_2': $i).
% 7.14/2.71  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.14/2.71  tff('#skF_3', type, '#skF_3': $i).
% 7.14/2.71  tff('#skF_1', type, '#skF_1': $i).
% 7.14/2.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.14/2.71  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.14/2.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.14/2.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.14/2.71  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.14/2.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.14/2.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.14/2.71  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.14/2.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.14/2.71  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.14/2.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.14/2.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.14/2.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.14/2.71  
% 7.30/2.74  tff(f_147, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 7.30/2.74  tff(f_134, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 7.30/2.74  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.30/2.74  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.30/2.74  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.30/2.74  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.30/2.74  tff(f_81, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 7.30/2.74  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 7.30/2.74  tff(f_130, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 7.30/2.74  tff(f_126, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.30/2.74  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.30/2.74  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.30/2.74  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.30/2.74  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 7.30/2.74  tff(f_98, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 7.30/2.74  tff(f_104, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 7.30/2.74  tff(f_94, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.30/2.74  tff(f_112, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 7.30/2.74  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 7.30/2.74  tff(f_90, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t217_relat_1)).
% 7.30/2.74  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 7.30/2.74  tff(f_140, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 7.30/2.74  tff(f_110, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 7.30/2.74  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 7.30/2.74  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.30/2.74  tff(c_3542, plain, (![A_415, B_416, C_417, D_418]: (k8_relset_1(A_415, B_416, C_417, D_418)=k10_relat_1(C_417, D_418) | ~m1_subset_1(C_417, k1_zfmisc_1(k2_zfmisc_1(A_415, B_416))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.30/2.74  tff(c_3549, plain, (![D_418]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_418)=k10_relat_1('#skF_3', D_418))), inference(resolution, [status(thm)], [c_66, c_3542])).
% 7.30/2.74  tff(c_3163, plain, (![A_387, B_388, C_389]: (k1_relset_1(A_387, B_388, C_389)=k1_relat_1(C_389) | ~m1_subset_1(C_389, k1_zfmisc_1(k2_zfmisc_1(A_387, B_388))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.30/2.74  tff(c_3172, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_3163])).
% 7.30/2.74  tff(c_20, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.30/2.74  tff(c_116, plain, (![B_75, A_76]: (v1_relat_1(B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.30/2.74  tff(c_122, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_116])).
% 7.30/2.74  tff(c_126, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_122])).
% 7.30/2.74  tff(c_260, plain, (![C_106, A_107, B_108]: (v4_relat_1(C_106, A_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.30/2.74  tff(c_269, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_260])).
% 7.30/2.74  tff(c_441, plain, (![B_134, A_135]: (k7_relat_1(B_134, A_135)=B_134 | ~v4_relat_1(B_134, A_135) | ~v1_relat_1(B_134))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.30/2.74  tff(c_453, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_269, c_441])).
% 7.30/2.74  tff(c_464, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_126, c_453])).
% 7.30/2.74  tff(c_22, plain, (![B_16, A_15]: (k2_relat_1(k7_relat_1(B_16, A_15))=k9_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.30/2.74  tff(c_471, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_464, c_22])).
% 7.30/2.74  tff(c_478, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_471])).
% 7.30/2.74  tff(c_1569, plain, (![A_216, B_217, C_218, D_219]: (k7_relset_1(A_216, B_217, C_218, D_219)=k9_relat_1(C_218, D_219) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.30/2.74  tff(c_1576, plain, (![D_219]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_219)=k9_relat_1('#skF_3', D_219))), inference(resolution, [status(thm)], [c_66, c_1569])).
% 7.30/2.74  tff(c_786, plain, (![A_158, B_159, C_160]: (k2_relset_1(A_158, B_159, C_160)=k2_relat_1(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.30/2.74  tff(c_795, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_786])).
% 7.30/2.74  tff(c_64, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.30/2.74  tff(c_96, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_64])).
% 7.30/2.74  tff(c_796, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_795, c_96])).
% 7.30/2.74  tff(c_1577, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1576, c_796])).
% 7.30/2.74  tff(c_1580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_478, c_1577])).
% 7.30/2.74  tff(c_1581, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_64])).
% 7.30/2.74  tff(c_3173, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3172, c_1581])).
% 7.30/2.74  tff(c_3550, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3549, c_3173])).
% 7.30/2.74  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.30/2.74  tff(c_91, plain, (![A_67, B_68]: (r1_tarski(A_67, B_68) | ~m1_subset_1(A_67, k1_zfmisc_1(B_68)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.30/2.74  tff(c_95, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_91])).
% 7.30/2.74  tff(c_1750, plain, (![A_262, C_263, B_264]: (r1_tarski(A_262, C_263) | ~r1_tarski(B_264, C_263) | ~r1_tarski(A_262, B_264))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.30/2.74  tff(c_1769, plain, (![A_265]: (r1_tarski(A_265, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_265, '#skF_3'))), inference(resolution, [status(thm)], [c_95, c_1750])).
% 7.30/2.74  tff(c_12, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.30/2.74  tff(c_1655, plain, (![C_236, B_237, A_238]: (v5_relat_1(C_236, B_237) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_238, B_237))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.30/2.74  tff(c_1663, plain, (![A_6, B_237, A_238]: (v5_relat_1(A_6, B_237) | ~r1_tarski(A_6, k2_zfmisc_1(A_238, B_237)))), inference(resolution, [status(thm)], [c_12, c_1655])).
% 7.30/2.74  tff(c_1785, plain, (![A_265]: (v5_relat_1(A_265, '#skF_2') | ~r1_tarski(A_265, '#skF_3'))), inference(resolution, [status(thm)], [c_1769, c_1663])).
% 7.30/2.74  tff(c_1619, plain, (![B_230, A_231]: (v1_relat_1(B_230) | ~m1_subset_1(B_230, k1_zfmisc_1(A_231)) | ~v1_relat_1(A_231))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.30/2.74  tff(c_1625, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_1619])).
% 7.30/2.74  tff(c_1629, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1625])).
% 7.30/2.74  tff(c_26, plain, (![B_21, A_20]: (r1_tarski(k10_relat_1(B_21, A_20), k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.30/2.74  tff(c_1687, plain, (![C_244, A_245, B_246]: (v4_relat_1(C_244, A_245) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.30/2.74  tff(c_1696, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_1687])).
% 7.30/2.74  tff(c_1866, plain, (![B_278, A_279]: (k7_relat_1(B_278, A_279)=B_278 | ~v4_relat_1(B_278, A_279) | ~v1_relat_1(B_278))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.30/2.74  tff(c_1878, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1696, c_1866])).
% 7.30/2.74  tff(c_1889, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1629, c_1878])).
% 7.30/2.74  tff(c_38, plain, (![B_32, A_31]: (r1_tarski(k1_relat_1(k7_relat_1(B_32, A_31)), A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.30/2.74  tff(c_1896, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1889, c_38])).
% 7.30/2.74  tff(c_1900, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1629, c_1896])).
% 7.30/2.74  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.30/2.74  tff(c_1998, plain, (![A_286]: (r1_tarski(A_286, '#skF_1') | ~r1_tarski(A_286, k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_1900, c_8])).
% 7.30/2.74  tff(c_2010, plain, (![A_20]: (r1_tarski(k10_relat_1('#skF_3', A_20), '#skF_1') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_1998])).
% 7.30/2.74  tff(c_2023, plain, (![A_20]: (r1_tarski(k10_relat_1('#skF_3', A_20), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1629, c_2010])).
% 7.30/2.74  tff(c_40, plain, (![A_33]: (v1_relat_1(k6_relat_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.30/2.74  tff(c_36, plain, (![A_30]: (k2_relat_1(k6_relat_1(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.30/2.74  tff(c_48, plain, (![B_37, A_36]: (k5_relat_1(k6_relat_1(B_37), k6_relat_1(A_36))=k6_relat_1(k3_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.30/2.74  tff(c_2855, plain, (![B_365, A_366]: (k9_relat_1(B_365, k2_relat_1(A_366))=k2_relat_1(k5_relat_1(A_366, B_365)) | ~v1_relat_1(B_365) | ~v1_relat_1(A_366))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.30/2.74  tff(c_2891, plain, (![A_30, B_365]: (k2_relat_1(k5_relat_1(k6_relat_1(A_30), B_365))=k9_relat_1(B_365, A_30) | ~v1_relat_1(B_365) | ~v1_relat_1(k6_relat_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_2855])).
% 7.30/2.74  tff(c_3560, plain, (![A_420, B_421]: (k2_relat_1(k5_relat_1(k6_relat_1(A_420), B_421))=k9_relat_1(B_421, A_420) | ~v1_relat_1(B_421))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2891])).
% 7.30/2.74  tff(c_3587, plain, (![A_36, B_37]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_36, B_37)))=k9_relat_1(k6_relat_1(A_36), B_37) | ~v1_relat_1(k6_relat_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_3560])).
% 7.30/2.74  tff(c_3591, plain, (![A_36, B_37]: (k9_relat_1(k6_relat_1(A_36), B_37)=k3_xboole_0(A_36, B_37))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_3587])).
% 7.30/2.74  tff(c_42, plain, (![A_33]: (v4_relat_1(k6_relat_1(A_33), A_33))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.30/2.74  tff(c_2239, plain, (![C_316, B_317, A_318]: (v4_relat_1(C_316, B_317) | ~v4_relat_1(C_316, A_318) | ~v1_relat_1(C_316) | ~r1_tarski(A_318, B_317))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.30/2.74  tff(c_2251, plain, (![A_33, B_317]: (v4_relat_1(k6_relat_1(A_33), B_317) | ~v1_relat_1(k6_relat_1(A_33)) | ~r1_tarski(A_33, B_317))), inference(resolution, [status(thm)], [c_42, c_2239])).
% 7.30/2.74  tff(c_2276, plain, (![A_320, B_321]: (v4_relat_1(k6_relat_1(A_320), B_321) | ~r1_tarski(A_320, B_321))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2251])).
% 7.30/2.74  tff(c_30, plain, (![B_25, A_24]: (k7_relat_1(B_25, A_24)=B_25 | ~v4_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.30/2.74  tff(c_2281, plain, (![A_320, B_321]: (k7_relat_1(k6_relat_1(A_320), B_321)=k6_relat_1(A_320) | ~v1_relat_1(k6_relat_1(A_320)) | ~r1_tarski(A_320, B_321))), inference(resolution, [status(thm)], [c_2276, c_30])).
% 7.30/2.74  tff(c_2356, plain, (![A_331, B_332]: (k7_relat_1(k6_relat_1(A_331), B_332)=k6_relat_1(A_331) | ~r1_tarski(A_331, B_332))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2281])).
% 7.30/2.74  tff(c_2365, plain, (![A_331, B_332]: (k9_relat_1(k6_relat_1(A_331), B_332)=k2_relat_1(k6_relat_1(A_331)) | ~v1_relat_1(k6_relat_1(A_331)) | ~r1_tarski(A_331, B_332))), inference(superposition, [status(thm), theory('equality')], [c_2356, c_22])).
% 7.30/2.74  tff(c_2387, plain, (![A_331, B_332]: (k9_relat_1(k6_relat_1(A_331), B_332)=A_331 | ~r1_tarski(A_331, B_332))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_2365])).
% 7.30/2.74  tff(c_3668, plain, (![A_427, B_428]: (k3_xboole_0(A_427, B_428)=A_427 | ~r1_tarski(A_427, B_428))), inference(demodulation, [status(thm), theory('equality')], [c_3591, c_2387])).
% 7.30/2.74  tff(c_3760, plain, (![A_20]: (k3_xboole_0(k10_relat_1('#skF_3', A_20), '#skF_1')=k10_relat_1('#skF_3', A_20))), inference(resolution, [status(thm)], [c_2023, c_3668])).
% 7.30/2.74  tff(c_28, plain, (![B_23, A_22]: (k10_relat_1(B_23, k3_xboole_0(k2_relat_1(B_23), A_22))=k10_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.30/2.74  tff(c_3803, plain, (![A_434]: (k3_xboole_0(k10_relat_1('#skF_3', A_434), '#skF_1')=k10_relat_1('#skF_3', A_434))), inference(resolution, [status(thm)], [c_2023, c_3668])).
% 7.30/2.74  tff(c_3813, plain, (![A_22]: (k10_relat_1('#skF_3', k3_xboole_0(k2_relat_1('#skF_3'), A_22))=k3_xboole_0(k10_relat_1('#skF_3', A_22), '#skF_1') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_3803])).
% 7.30/2.74  tff(c_3861, plain, (![A_442]: (k10_relat_1('#skF_3', k3_xboole_0(k2_relat_1('#skF_3'), A_442))=k10_relat_1('#skF_3', A_442))), inference(demodulation, [status(thm), theory('equality')], [c_1629, c_3760, c_3813])).
% 7.30/2.74  tff(c_3889, plain, (![A_442]: (r1_tarski(k10_relat_1('#skF_3', A_442), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3861, c_26])).
% 7.30/2.74  tff(c_3918, plain, (![A_442]: (r1_tarski(k10_relat_1('#skF_3', A_442), k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1629, c_3889])).
% 7.30/2.74  tff(c_3959, plain, (![D_444, B_445, C_446, A_447]: (m1_subset_1(D_444, k1_zfmisc_1(k2_zfmisc_1(B_445, C_446))) | ~r1_tarski(k1_relat_1(D_444), B_445) | ~m1_subset_1(D_444, k1_zfmisc_1(k2_zfmisc_1(A_447, C_446))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.30/2.74  tff(c_3968, plain, (![B_448]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_448, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_448))), inference(resolution, [status(thm)], [c_66, c_3959])).
% 7.30/2.74  tff(c_52, plain, (![C_40, A_38, B_39]: (v4_relat_1(C_40, A_38) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.30/2.74  tff(c_4005, plain, (![B_449]: (v4_relat_1('#skF_3', B_449) | ~r1_tarski(k1_relat_1('#skF_3'), B_449))), inference(resolution, [status(thm)], [c_3968, c_52])).
% 7.30/2.74  tff(c_4025, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_4005])).
% 7.30/2.74  tff(c_4030, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4025, c_30])).
% 7.30/2.74  tff(c_4036, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1629, c_4030])).
% 7.30/2.74  tff(c_4046, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4036, c_22])).
% 7.30/2.74  tff(c_4058, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1629, c_4046])).
% 7.30/2.74  tff(c_46, plain, (![A_34, B_35]: (r1_tarski(A_34, k10_relat_1(B_35, k9_relat_1(B_35, A_34))) | ~r1_tarski(A_34, k1_relat_1(B_35)) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.30/2.74  tff(c_4065, plain, (r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', k2_relat_1('#skF_3'))) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4058, c_46])).
% 7.30/2.74  tff(c_4069, plain, (r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1629, c_6, c_4065])).
% 7.30/2.74  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.30/2.74  tff(c_4090, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~r1_tarski(k10_relat_1('#skF_3', k2_relat_1('#skF_3')), k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_4069, c_2])).
% 7.30/2.74  tff(c_4103, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3918, c_4090])).
% 7.30/2.74  tff(c_1954, plain, (![B_283, A_284]: (k2_relat_1(k7_relat_1(B_283, A_284))=k9_relat_1(B_283, A_284) | ~v1_relat_1(B_283))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.30/2.74  tff(c_1978, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1889, c_1954])).
% 7.30/2.74  tff(c_1984, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1629, c_1978])).
% 7.30/2.74  tff(c_18, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.30/2.74  tff(c_8494, plain, (![B_598, A_599, A_600]: (r1_tarski(k9_relat_1(B_598, A_599), A_600) | ~v5_relat_1(k7_relat_1(B_598, A_599), A_600) | ~v1_relat_1(k7_relat_1(B_598, A_599)) | ~v1_relat_1(B_598))), inference(superposition, [status(thm), theory('equality')], [c_1954, c_18])).
% 7.30/2.74  tff(c_8519, plain, (![A_600]: (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), A_600) | ~v5_relat_1('#skF_3', A_600) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1889, c_8494])).
% 7.30/2.74  tff(c_8545, plain, (![A_601]: (r1_tarski(k2_relat_1('#skF_3'), A_601) | ~v5_relat_1('#skF_3', A_601))), inference(demodulation, [status(thm), theory('equality')], [c_1629, c_1629, c_1889, c_1984, c_8519])).
% 7.30/2.74  tff(c_3619, plain, (![A_331, B_332]: (k3_xboole_0(A_331, B_332)=A_331 | ~r1_tarski(A_331, B_332))), inference(demodulation, [status(thm), theory('equality')], [c_3591, c_2387])).
% 7.30/2.74  tff(c_8988, plain, (![A_612]: (k3_xboole_0(k2_relat_1('#skF_3'), A_612)=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_612))), inference(resolution, [status(thm)], [c_8545, c_3619])).
% 7.30/2.74  tff(c_3817, plain, (![A_22]: (k10_relat_1('#skF_3', k3_xboole_0(k2_relat_1('#skF_3'), A_22))=k10_relat_1('#skF_3', A_22))), inference(demodulation, [status(thm), theory('equality')], [c_1629, c_3760, c_3813])).
% 7.30/2.74  tff(c_9001, plain, (![A_612]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_612) | ~v5_relat_1('#skF_3', A_612))), inference(superposition, [status(thm), theory('equality')], [c_8988, c_3817])).
% 7.30/2.74  tff(c_9036, plain, (![A_613]: (k10_relat_1('#skF_3', A_613)=k1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_613))), inference(demodulation, [status(thm), theory('equality')], [c_4103, c_9001])).
% 7.30/2.74  tff(c_9044, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1785, c_9036])).
% 7.30/2.74  tff(c_9057, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_9044])).
% 7.30/2.74  tff(c_9059, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3550, c_9057])).
% 7.30/2.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.30/2.74  
% 7.30/2.74  Inference rules
% 7.30/2.74  ----------------------
% 7.30/2.74  #Ref     : 0
% 7.30/2.74  #Sup     : 1964
% 7.30/2.74  #Fact    : 0
% 7.30/2.74  #Define  : 0
% 7.30/2.74  #Split   : 19
% 7.30/2.74  #Chain   : 0
% 7.30/2.74  #Close   : 0
% 7.30/2.74  
% 7.30/2.74  Ordering : KBO
% 7.30/2.74  
% 7.30/2.74  Simplification rules
% 7.30/2.74  ----------------------
% 7.30/2.74  #Subsume      : 320
% 7.30/2.74  #Demod        : 1175
% 7.30/2.74  #Tautology    : 625
% 7.30/2.74  #SimpNegUnit  : 11
% 7.30/2.74  #BackRed      : 11
% 7.30/2.74  
% 7.30/2.74  #Partial instantiations: 0
% 7.30/2.74  #Strategies tried      : 1
% 7.30/2.74  
% 7.30/2.74  Timing (in seconds)
% 7.30/2.74  ----------------------
% 7.30/2.74  Preprocessing        : 0.36
% 7.30/2.74  Parsing              : 0.20
% 7.30/2.74  CNF conversion       : 0.02
% 7.30/2.74  Main loop            : 1.55
% 7.30/2.74  Inferencing          : 0.49
% 7.30/2.74  Reduction            : 0.57
% 7.30/2.74  Demodulation         : 0.42
% 7.30/2.74  BG Simplification    : 0.05
% 7.30/2.74  Subsumption          : 0.32
% 7.30/2.74  Abstraction          : 0.07
% 7.30/2.74  MUC search           : 0.00
% 7.30/2.74  Cooper               : 0.00
% 7.30/2.74  Total                : 1.96
% 7.30/2.74  Index Insertion      : 0.00
% 7.30/2.74  Index Deletion       : 0.00
% 7.30/2.74  Index Matching       : 0.00
% 7.30/2.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
