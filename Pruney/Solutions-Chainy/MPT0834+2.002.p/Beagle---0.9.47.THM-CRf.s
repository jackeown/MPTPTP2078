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
% DateTime   : Thu Dec  3 10:07:49 EST 2020

% Result     : Theorem 4.48s
% Output     : CNFRefutation 4.76s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 255 expanded)
%              Number of leaves         :   45 ( 104 expanded)
%              Depth                    :   15
%              Number of atoms          :  204 ( 457 expanded)
%              Number of equality atoms :   67 ( 145 expanded)
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

tff(f_130,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_117,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_123,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_91,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3019,plain,(
    ! [A_291,B_292,C_293,D_294] :
      ( k8_relset_1(A_291,B_292,C_293,D_294) = k10_relat_1(C_293,D_294)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(A_291,B_292))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_3022,plain,(
    ! [D_294] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_294) = k10_relat_1('#skF_3',D_294) ),
    inference(resolution,[status(thm)],[c_58,c_3019])).

tff(c_2297,plain,(
    ! [A_258,B_259,C_260] :
      ( k1_relset_1(A_258,B_259,C_260) = k1_relat_1(C_260)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2301,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_2297])).

tff(c_123,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_127,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_123])).

tff(c_251,plain,(
    ! [C_89,A_90,B_91] :
      ( v4_relat_1(C_89,A_90)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_255,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_251])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( k7_relat_1(B_17,A_16) = B_17
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_258,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_255,c_22])).

tff(c_261,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_258])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( k2_relat_1(k7_relat_1(B_8,A_7)) = k9_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_265,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_14])).

tff(c_269,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_265])).

tff(c_1315,plain,(
    ! [A_161,B_162,C_163,D_164] :
      ( k7_relset_1(A_161,B_162,C_163,D_164) = k9_relat_1(C_163,D_164)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1318,plain,(
    ! [D_164] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_164) = k9_relat_1('#skF_3',D_164) ),
    inference(resolution,[status(thm)],[c_58,c_1315])).

tff(c_772,plain,(
    ! [A_136,B_137,C_138] :
      ( k2_relset_1(A_136,B_137,C_138) = k2_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_776,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_772])).

tff(c_56,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_122,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_818,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_122])).

tff(c_1319,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1318,c_818])).

tff(c_1322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_1319])).

tff(c_1323,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2302,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2301,c_1323])).

tff(c_3052,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3022,c_2302])).

tff(c_1343,plain,(
    ! [C_172,B_173,A_174] :
      ( v5_relat_1(C_172,B_173)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_174,B_173))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1347,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_1343])).

tff(c_1325,plain,(
    ! [C_165,A_166,B_167] :
      ( v1_relat_1(C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1329,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1325])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3233,plain,(
    ! [D_303,B_304,C_305,A_306] :
      ( m1_subset_1(D_303,k1_zfmisc_1(k2_zfmisc_1(B_304,C_305)))
      | ~ r1_tarski(k1_relat_1(D_303),B_304)
      | ~ m1_subset_1(D_303,k1_zfmisc_1(k2_zfmisc_1(A_306,C_305))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3256,plain,(
    ! [B_309] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_309,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_309) ) ),
    inference(resolution,[status(thm)],[c_58,c_3233])).

tff(c_44,plain,(
    ! [C_33,A_31,B_32] :
      ( v4_relat_1(C_33,A_31)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3288,plain,(
    ! [B_310] :
      ( v4_relat_1('#skF_3',B_310)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_310) ) ),
    inference(resolution,[status(thm)],[c_3256,c_44])).

tff(c_3303,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_3288])).

tff(c_3324,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3303,c_22])).

tff(c_3330,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1329,c_3324])).

tff(c_3337,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3330,c_14])).

tff(c_3343,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1329,c_3337])).

tff(c_36,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,k10_relat_1(B_25,k9_relat_1(B_25,A_24)))
      | ~ r1_tarski(A_24,k1_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3348,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',k2_relat_1('#skF_3')))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3343,c_36])).

tff(c_3352,plain,(
    r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3',k2_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1329,c_8,c_3348])).

tff(c_1330,plain,(
    ! [B_168,A_169] :
      ( r1_tarski(k10_relat_1(B_168,A_169),k1_relat_1(B_168))
      | ~ v1_relat_1(B_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3383,plain,(
    ! [B_312,A_313] :
      ( k10_relat_1(B_312,A_313) = k1_relat_1(B_312)
      | ~ r1_tarski(k1_relat_1(B_312),k10_relat_1(B_312,A_313))
      | ~ v1_relat_1(B_312) ) ),
    inference(resolution,[status(thm)],[c_1330,c_4])).

tff(c_3386,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3352,c_3383])).

tff(c_3418,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1329,c_3386])).

tff(c_1348,plain,(
    ! [C_175,A_176,B_177] :
      ( v4_relat_1(C_175,A_176)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1352,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_1348])).

tff(c_1368,plain,(
    ! [B_182,A_183] :
      ( k7_relat_1(B_182,A_183) = B_182
      | ~ v4_relat_1(B_182,A_183)
      | ~ v1_relat_1(B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1371,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1352,c_1368])).

tff(c_1377,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1329,c_1371])).

tff(c_1398,plain,(
    ! [B_185,A_186] :
      ( k2_relat_1(k7_relat_1(B_185,A_186)) = k9_relat_1(B_185,A_186)
      | ~ v1_relat_1(B_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1413,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1377,c_1398])).

tff(c_1419,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1329,c_1413])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k2_relat_1(B_6),A_5)
      | ~ v5_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3498,plain,(
    ! [B_315,A_316,A_317] :
      ( r1_tarski(k9_relat_1(B_315,A_316),A_317)
      | ~ v5_relat_1(k7_relat_1(B_315,A_316),A_317)
      | ~ v1_relat_1(k7_relat_1(B_315,A_316))
      | ~ v1_relat_1(B_315) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1398,c_12])).

tff(c_3520,plain,(
    ! [A_317] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),A_317)
      | ~ v5_relat_1('#skF_3',A_317)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1377,c_3498])).

tff(c_3534,plain,(
    ! [A_318] :
      ( r1_tarski(k2_relat_1('#skF_3'),A_318)
      | ~ v5_relat_1('#skF_3',A_318) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1329,c_1329,c_1377,c_1419,c_3520])).

tff(c_30,plain,(
    ! [A_23] : v1_relat_1(k6_relat_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    ! [A_22] : k2_relat_1(k6_relat_1(A_22)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38,plain,(
    ! [B_27,A_26] : k5_relat_1(k6_relat_1(B_27),k6_relat_1(A_26)) = k6_relat_1(k3_xboole_0(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2006,plain,(
    ! [B_243,A_244] :
      ( k9_relat_1(B_243,k2_relat_1(A_244)) = k2_relat_1(k5_relat_1(A_244,B_243))
      | ~ v1_relat_1(B_243)
      | ~ v1_relat_1(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2034,plain,(
    ! [A_22,B_243] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_22),B_243)) = k9_relat_1(B_243,A_22)
      | ~ v1_relat_1(B_243)
      | ~ v1_relat_1(k6_relat_1(A_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2006])).

tff(c_2047,plain,(
    ! [A_245,B_246] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_245),B_246)) = k9_relat_1(B_246,A_245)
      | ~ v1_relat_1(B_246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2034])).

tff(c_2076,plain,(
    ! [A_26,B_27] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_26,B_27))) = k9_relat_1(k6_relat_1(A_26),B_27)
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2047])).

tff(c_2080,plain,(
    ! [A_26,B_27] : k9_relat_1(k6_relat_1(A_26),B_27) = k3_xboole_0(A_26,B_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_2076])).

tff(c_32,plain,(
    ! [A_23] : v4_relat_1(k6_relat_1(A_23),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1481,plain,(
    ! [C_195,B_196,A_197] :
      ( v4_relat_1(C_195,B_196)
      | ~ v4_relat_1(C_195,A_197)
      | ~ v1_relat_1(C_195)
      | ~ r1_tarski(A_197,B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1485,plain,(
    ! [A_23,B_196] :
      ( v4_relat_1(k6_relat_1(A_23),B_196)
      | ~ v1_relat_1(k6_relat_1(A_23))
      | ~ r1_tarski(A_23,B_196) ) ),
    inference(resolution,[status(thm)],[c_32,c_1481])).

tff(c_1504,plain,(
    ! [A_199,B_200] :
      ( v4_relat_1(k6_relat_1(A_199),B_200)
      | ~ r1_tarski(A_199,B_200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1485])).

tff(c_1509,plain,(
    ! [A_199,B_200] :
      ( k7_relat_1(k6_relat_1(A_199),B_200) = k6_relat_1(A_199)
      | ~ v1_relat_1(k6_relat_1(A_199))
      | ~ r1_tarski(A_199,B_200) ) ),
    inference(resolution,[status(thm)],[c_1504,c_22])).

tff(c_1523,plain,(
    ! [A_202,B_203] :
      ( k7_relat_1(k6_relat_1(A_202),B_203) = k6_relat_1(A_202)
      | ~ r1_tarski(A_202,B_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1509])).

tff(c_1529,plain,(
    ! [A_202,B_203] :
      ( k9_relat_1(k6_relat_1(A_202),B_203) = k2_relat_1(k6_relat_1(A_202))
      | ~ v1_relat_1(k6_relat_1(A_202))
      | ~ r1_tarski(A_202,B_203) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1523,c_14])).

tff(c_1542,plain,(
    ! [A_202,B_203] :
      ( k9_relat_1(k6_relat_1(A_202),B_203) = A_202
      | ~ r1_tarski(A_202,B_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1529])).

tff(c_2081,plain,(
    ! [A_202,B_203] :
      ( k3_xboole_0(A_202,B_203) = A_202
      | ~ r1_tarski(A_202,B_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2080,c_1542])).

tff(c_3573,plain,(
    ! [A_319] :
      ( k3_xboole_0(k2_relat_1('#skF_3'),A_319) = k2_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_319) ) ),
    inference(resolution,[status(thm)],[c_3534,c_2081])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( k10_relat_1(B_15,k3_xboole_0(k2_relat_1(B_15),A_14)) = k10_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3608,plain,(
    ! [A_319] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_319)
      | ~ v1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_319) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3573,c_20])).

tff(c_3676,plain,(
    ! [A_322] :
      ( k10_relat_1('#skF_3',A_322) = k1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_322) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1329,c_3418,c_3608])).

tff(c_3683,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1347,c_3676])).

tff(c_3690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3052,c_3683])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.48/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.84  
% 4.68/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.84  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.68/1.84  
% 4.68/1.84  %Foreground sorts:
% 4.68/1.84  
% 4.68/1.84  
% 4.68/1.84  %Background operators:
% 4.68/1.84  
% 4.68/1.84  
% 4.68/1.84  %Foreground operators:
% 4.68/1.84  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.68/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.84  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.68/1.84  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.68/1.84  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.68/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.68/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.68/1.84  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.68/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.68/1.84  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.68/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.68/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.68/1.84  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.68/1.84  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.68/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.68/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.84  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.68/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.68/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.68/1.84  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.68/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.84  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.68/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.68/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.68/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.68/1.84  
% 4.76/1.86  tff(f_130, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 4.76/1.86  tff(f_117, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.76/1.86  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.76/1.86  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.76/1.86  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.76/1.86  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 4.76/1.86  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 4.76/1.86  tff(f_113, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.76/1.86  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.76/1.86  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.76/1.86  tff(f_123, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 4.76/1.86  tff(f_89, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 4.76/1.86  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 4.76/1.86  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.76/1.86  tff(f_83, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 4.76/1.86  tff(f_77, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.76/1.86  tff(f_91, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 4.76/1.86  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 4.76/1.86  tff(f_73, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t217_relat_1)).
% 4.76/1.86  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 4.76/1.86  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.76/1.86  tff(c_3019, plain, (![A_291, B_292, C_293, D_294]: (k8_relset_1(A_291, B_292, C_293, D_294)=k10_relat_1(C_293, D_294) | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(A_291, B_292))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.76/1.86  tff(c_3022, plain, (![D_294]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_294)=k10_relat_1('#skF_3', D_294))), inference(resolution, [status(thm)], [c_58, c_3019])).
% 4.76/1.86  tff(c_2297, plain, (![A_258, B_259, C_260]: (k1_relset_1(A_258, B_259, C_260)=k1_relat_1(C_260) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.76/1.86  tff(c_2301, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_2297])).
% 4.76/1.86  tff(c_123, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.76/1.86  tff(c_127, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_123])).
% 4.76/1.86  tff(c_251, plain, (![C_89, A_90, B_91]: (v4_relat_1(C_89, A_90) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.76/1.86  tff(c_255, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_251])).
% 4.76/1.86  tff(c_22, plain, (![B_17, A_16]: (k7_relat_1(B_17, A_16)=B_17 | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.76/1.86  tff(c_258, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_255, c_22])).
% 4.76/1.86  tff(c_261, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_258])).
% 4.76/1.86  tff(c_14, plain, (![B_8, A_7]: (k2_relat_1(k7_relat_1(B_8, A_7))=k9_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.76/1.86  tff(c_265, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_261, c_14])).
% 4.76/1.86  tff(c_269, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_265])).
% 4.76/1.86  tff(c_1315, plain, (![A_161, B_162, C_163, D_164]: (k7_relset_1(A_161, B_162, C_163, D_164)=k9_relat_1(C_163, D_164) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.76/1.86  tff(c_1318, plain, (![D_164]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_164)=k9_relat_1('#skF_3', D_164))), inference(resolution, [status(thm)], [c_58, c_1315])).
% 4.76/1.86  tff(c_772, plain, (![A_136, B_137, C_138]: (k2_relset_1(A_136, B_137, C_138)=k2_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.76/1.86  tff(c_776, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_772])).
% 4.76/1.86  tff(c_56, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.76/1.86  tff(c_122, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 4.76/1.86  tff(c_818, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_776, c_122])).
% 4.76/1.86  tff(c_1319, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1318, c_818])).
% 4.76/1.86  tff(c_1322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_269, c_1319])).
% 4.76/1.86  tff(c_1323, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 4.76/1.86  tff(c_2302, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2301, c_1323])).
% 4.76/1.86  tff(c_3052, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3022, c_2302])).
% 4.76/1.86  tff(c_1343, plain, (![C_172, B_173, A_174]: (v5_relat_1(C_172, B_173) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_174, B_173))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.76/1.86  tff(c_1347, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_58, c_1343])).
% 4.76/1.86  tff(c_1325, plain, (![C_165, A_166, B_167]: (v1_relat_1(C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.76/1.86  tff(c_1329, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_1325])).
% 4.76/1.86  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.76/1.86  tff(c_3233, plain, (![D_303, B_304, C_305, A_306]: (m1_subset_1(D_303, k1_zfmisc_1(k2_zfmisc_1(B_304, C_305))) | ~r1_tarski(k1_relat_1(D_303), B_304) | ~m1_subset_1(D_303, k1_zfmisc_1(k2_zfmisc_1(A_306, C_305))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.76/1.86  tff(c_3256, plain, (![B_309]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_309, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_309))), inference(resolution, [status(thm)], [c_58, c_3233])).
% 4.76/1.86  tff(c_44, plain, (![C_33, A_31, B_32]: (v4_relat_1(C_33, A_31) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.76/1.86  tff(c_3288, plain, (![B_310]: (v4_relat_1('#skF_3', B_310) | ~r1_tarski(k1_relat_1('#skF_3'), B_310))), inference(resolution, [status(thm)], [c_3256, c_44])).
% 4.76/1.86  tff(c_3303, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_3288])).
% 4.76/1.86  tff(c_3324, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3303, c_22])).
% 4.76/1.86  tff(c_3330, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1329, c_3324])).
% 4.76/1.86  tff(c_3337, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3330, c_14])).
% 4.76/1.86  tff(c_3343, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1329, c_3337])).
% 4.76/1.86  tff(c_36, plain, (![A_24, B_25]: (r1_tarski(A_24, k10_relat_1(B_25, k9_relat_1(B_25, A_24))) | ~r1_tarski(A_24, k1_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.76/1.86  tff(c_3348, plain, (r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', k2_relat_1('#skF_3'))) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3343, c_36])).
% 4.76/1.86  tff(c_3352, plain, (r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1329, c_8, c_3348])).
% 4.76/1.86  tff(c_1330, plain, (![B_168, A_169]: (r1_tarski(k10_relat_1(B_168, A_169), k1_relat_1(B_168)) | ~v1_relat_1(B_168))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.76/1.86  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.76/1.86  tff(c_3383, plain, (![B_312, A_313]: (k10_relat_1(B_312, A_313)=k1_relat_1(B_312) | ~r1_tarski(k1_relat_1(B_312), k10_relat_1(B_312, A_313)) | ~v1_relat_1(B_312))), inference(resolution, [status(thm)], [c_1330, c_4])).
% 4.76/1.86  tff(c_3386, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3352, c_3383])).
% 4.76/1.86  tff(c_3418, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1329, c_3386])).
% 4.76/1.86  tff(c_1348, plain, (![C_175, A_176, B_177]: (v4_relat_1(C_175, A_176) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.76/1.86  tff(c_1352, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_1348])).
% 4.76/1.86  tff(c_1368, plain, (![B_182, A_183]: (k7_relat_1(B_182, A_183)=B_182 | ~v4_relat_1(B_182, A_183) | ~v1_relat_1(B_182))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.76/1.86  tff(c_1371, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1352, c_1368])).
% 4.76/1.86  tff(c_1377, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1329, c_1371])).
% 4.76/1.86  tff(c_1398, plain, (![B_185, A_186]: (k2_relat_1(k7_relat_1(B_185, A_186))=k9_relat_1(B_185, A_186) | ~v1_relat_1(B_185))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.76/1.86  tff(c_1413, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1377, c_1398])).
% 4.76/1.86  tff(c_1419, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1329, c_1413])).
% 4.76/1.86  tff(c_12, plain, (![B_6, A_5]: (r1_tarski(k2_relat_1(B_6), A_5) | ~v5_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.76/1.86  tff(c_3498, plain, (![B_315, A_316, A_317]: (r1_tarski(k9_relat_1(B_315, A_316), A_317) | ~v5_relat_1(k7_relat_1(B_315, A_316), A_317) | ~v1_relat_1(k7_relat_1(B_315, A_316)) | ~v1_relat_1(B_315))), inference(superposition, [status(thm), theory('equality')], [c_1398, c_12])).
% 4.76/1.86  tff(c_3520, plain, (![A_317]: (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), A_317) | ~v5_relat_1('#skF_3', A_317) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1377, c_3498])).
% 4.76/1.86  tff(c_3534, plain, (![A_318]: (r1_tarski(k2_relat_1('#skF_3'), A_318) | ~v5_relat_1('#skF_3', A_318))), inference(demodulation, [status(thm), theory('equality')], [c_1329, c_1329, c_1377, c_1419, c_3520])).
% 4.76/1.86  tff(c_30, plain, (![A_23]: (v1_relat_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.76/1.86  tff(c_28, plain, (![A_22]: (k2_relat_1(k6_relat_1(A_22))=A_22)), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.76/1.86  tff(c_38, plain, (![B_27, A_26]: (k5_relat_1(k6_relat_1(B_27), k6_relat_1(A_26))=k6_relat_1(k3_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.76/1.86  tff(c_2006, plain, (![B_243, A_244]: (k9_relat_1(B_243, k2_relat_1(A_244))=k2_relat_1(k5_relat_1(A_244, B_243)) | ~v1_relat_1(B_243) | ~v1_relat_1(A_244))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.76/1.86  tff(c_2034, plain, (![A_22, B_243]: (k2_relat_1(k5_relat_1(k6_relat_1(A_22), B_243))=k9_relat_1(B_243, A_22) | ~v1_relat_1(B_243) | ~v1_relat_1(k6_relat_1(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2006])).
% 4.76/1.86  tff(c_2047, plain, (![A_245, B_246]: (k2_relat_1(k5_relat_1(k6_relat_1(A_245), B_246))=k9_relat_1(B_246, A_245) | ~v1_relat_1(B_246))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2034])).
% 4.76/1.86  tff(c_2076, plain, (![A_26, B_27]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_26, B_27)))=k9_relat_1(k6_relat_1(A_26), B_27) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_2047])).
% 4.76/1.86  tff(c_2080, plain, (![A_26, B_27]: (k9_relat_1(k6_relat_1(A_26), B_27)=k3_xboole_0(A_26, B_27))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_2076])).
% 4.76/1.86  tff(c_32, plain, (![A_23]: (v4_relat_1(k6_relat_1(A_23), A_23))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.76/1.86  tff(c_1481, plain, (![C_195, B_196, A_197]: (v4_relat_1(C_195, B_196) | ~v4_relat_1(C_195, A_197) | ~v1_relat_1(C_195) | ~r1_tarski(A_197, B_196))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.76/1.86  tff(c_1485, plain, (![A_23, B_196]: (v4_relat_1(k6_relat_1(A_23), B_196) | ~v1_relat_1(k6_relat_1(A_23)) | ~r1_tarski(A_23, B_196))), inference(resolution, [status(thm)], [c_32, c_1481])).
% 4.76/1.86  tff(c_1504, plain, (![A_199, B_200]: (v4_relat_1(k6_relat_1(A_199), B_200) | ~r1_tarski(A_199, B_200))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1485])).
% 4.76/1.86  tff(c_1509, plain, (![A_199, B_200]: (k7_relat_1(k6_relat_1(A_199), B_200)=k6_relat_1(A_199) | ~v1_relat_1(k6_relat_1(A_199)) | ~r1_tarski(A_199, B_200))), inference(resolution, [status(thm)], [c_1504, c_22])).
% 4.76/1.86  tff(c_1523, plain, (![A_202, B_203]: (k7_relat_1(k6_relat_1(A_202), B_203)=k6_relat_1(A_202) | ~r1_tarski(A_202, B_203))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1509])).
% 4.76/1.86  tff(c_1529, plain, (![A_202, B_203]: (k9_relat_1(k6_relat_1(A_202), B_203)=k2_relat_1(k6_relat_1(A_202)) | ~v1_relat_1(k6_relat_1(A_202)) | ~r1_tarski(A_202, B_203))), inference(superposition, [status(thm), theory('equality')], [c_1523, c_14])).
% 4.76/1.86  tff(c_1542, plain, (![A_202, B_203]: (k9_relat_1(k6_relat_1(A_202), B_203)=A_202 | ~r1_tarski(A_202, B_203))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1529])).
% 4.76/1.86  tff(c_2081, plain, (![A_202, B_203]: (k3_xboole_0(A_202, B_203)=A_202 | ~r1_tarski(A_202, B_203))), inference(demodulation, [status(thm), theory('equality')], [c_2080, c_1542])).
% 4.76/1.86  tff(c_3573, plain, (![A_319]: (k3_xboole_0(k2_relat_1('#skF_3'), A_319)=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_319))), inference(resolution, [status(thm)], [c_3534, c_2081])).
% 4.76/1.86  tff(c_20, plain, (![B_15, A_14]: (k10_relat_1(B_15, k3_xboole_0(k2_relat_1(B_15), A_14))=k10_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.76/1.86  tff(c_3608, plain, (![A_319]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_319) | ~v1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_319))), inference(superposition, [status(thm), theory('equality')], [c_3573, c_20])).
% 4.76/1.86  tff(c_3676, plain, (![A_322]: (k10_relat_1('#skF_3', A_322)=k1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_322))), inference(demodulation, [status(thm), theory('equality')], [c_1329, c_3418, c_3608])).
% 4.76/1.86  tff(c_3683, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1347, c_3676])).
% 4.76/1.86  tff(c_3690, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3052, c_3683])).
% 4.76/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.86  
% 4.76/1.86  Inference rules
% 4.76/1.86  ----------------------
% 4.76/1.86  #Ref     : 0
% 4.76/1.86  #Sup     : 806
% 4.76/1.86  #Fact    : 0
% 4.76/1.86  #Define  : 0
% 4.76/1.86  #Split   : 4
% 4.76/1.86  #Chain   : 0
% 4.76/1.86  #Close   : 0
% 4.76/1.86  
% 4.76/1.86  Ordering : KBO
% 4.76/1.86  
% 4.76/1.86  Simplification rules
% 4.76/1.86  ----------------------
% 4.76/1.86  #Subsume      : 118
% 4.76/1.86  #Demod        : 651
% 4.76/1.86  #Tautology    : 355
% 4.76/1.86  #SimpNegUnit  : 1
% 4.76/1.86  #BackRed      : 9
% 4.76/1.86  
% 4.76/1.86  #Partial instantiations: 0
% 4.76/1.86  #Strategies tried      : 1
% 4.76/1.86  
% 4.76/1.86  Timing (in seconds)
% 4.76/1.86  ----------------------
% 4.76/1.86  Preprocessing        : 0.35
% 4.76/1.86  Parsing              : 0.19
% 4.76/1.86  CNF conversion       : 0.02
% 4.76/1.86  Main loop            : 0.74
% 4.76/1.86  Inferencing          : 0.25
% 4.76/1.86  Reduction            : 0.27
% 4.76/1.86  Demodulation         : 0.21
% 4.76/1.86  BG Simplification    : 0.03
% 4.76/1.86  Subsumption          : 0.12
% 4.76/1.86  Abstraction          : 0.04
% 4.76/1.87  MUC search           : 0.00
% 4.76/1.87  Cooper               : 0.00
% 4.76/1.87  Total                : 1.14
% 4.76/1.87  Index Insertion      : 0.00
% 4.76/1.87  Index Deletion       : 0.00
% 4.76/1.87  Index Matching       : 0.00
% 4.76/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
