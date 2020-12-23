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
% DateTime   : Thu Dec  3 10:07:54 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 4.03s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 245 expanded)
%              Number of leaves         :   44 ( 100 expanded)
%              Depth                    :   16
%              Number of atoms          :  163 ( 421 expanded)
%              Number of equality atoms :   60 ( 126 expanded)
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

tff(f_113,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_40,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_82,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_106,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => v4_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1739,plain,(
    ! [A_235,B_236,C_237,D_238] :
      ( k8_relset_1(A_235,B_236,C_237,D_238) = k10_relat_1(C_237,D_238)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1745,plain,(
    ! [D_238] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_238) = k10_relat_1('#skF_3',D_238) ),
    inference(resolution,[status(thm)],[c_46,c_1739])).

tff(c_1290,plain,(
    ! [A_192,B_193,C_194] :
      ( k1_relset_1(A_192,B_193,C_194) = k1_relat_1(C_194)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1299,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1290])).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_91,plain,(
    ! [B_52,A_53] :
      ( v1_relat_1(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_97,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_91])).

tff(c_103,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_97])).

tff(c_191,plain,(
    ! [C_74,A_75,B_76] :
      ( v4_relat_1(C_74,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_199,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_191])).

tff(c_20,plain,(
    ! [B_18,A_17] :
      ( k7_relat_1(B_18,A_17) = B_18
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_219,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_199,c_20])).

tff(c_222,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_219])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( k2_relat_1(k7_relat_1(B_10,A_9)) = k9_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_233,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_12])).

tff(c_237,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_233])).

tff(c_1060,plain,(
    ! [A_151,B_152,C_153,D_154] :
      ( k7_relset_1(A_151,B_152,C_153,D_154) = k9_relat_1(C_153,D_154)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1067,plain,(
    ! [D_154] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_154) = k9_relat_1('#skF_3',D_154) ),
    inference(resolution,[status(thm)],[c_46,c_1060])).

tff(c_502,plain,(
    ! [A_106,B_107,C_108] :
      ( k2_relset_1(A_106,B_107,C_108) = k2_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_511,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_502])).

tff(c_44,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_104,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_522,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_104])).

tff(c_1068,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1067,c_522])).

tff(c_1071,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_1068])).

tff(c_1072,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1309,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1299,c_1072])).

tff(c_1746,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1745,c_1309])).

tff(c_1115,plain,(
    ! [C_168,B_169,A_170] :
      ( v5_relat_1(C_168,B_169)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_170,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1123,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_1115])).

tff(c_1106,plain,(
    ! [C_165,A_166,B_167] :
      ( v4_relat_1(C_165,A_166)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1114,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_1106])).

tff(c_1126,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1114,c_20])).

tff(c_1129,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_1126])).

tff(c_1145,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1129,c_12])).

tff(c_1149,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_1145])).

tff(c_1178,plain,(
    ! [B_175,A_176] :
      ( r1_tarski(k2_relat_1(B_175),A_176)
      | ~ v5_relat_1(B_175,A_176)
      | ~ v1_relat_1(B_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2117,plain,(
    ! [B_266,A_267,A_268] :
      ( r1_tarski(k9_relat_1(B_266,A_267),A_268)
      | ~ v5_relat_1(k7_relat_1(B_266,A_267),A_268)
      | ~ v1_relat_1(k7_relat_1(B_266,A_267))
      | ~ v1_relat_1(B_266) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1178])).

tff(c_2133,plain,(
    ! [A_268] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),A_268)
      | ~ v5_relat_1('#skF_3',A_268)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1129,c_2117])).

tff(c_2142,plain,(
    ! [A_269] :
      ( r1_tarski(k2_relat_1('#skF_3'),A_269)
      | ~ v5_relat_1('#skF_3',A_269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_103,c_1129,c_1149,c_2133])).

tff(c_8,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    ! [B_25,A_24] : k5_relat_1(k6_relat_1(B_25),k6_relat_1(A_24)) = k6_relat_1(k3_xboole_0(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1396,plain,(
    ! [B_209,A_210] :
      ( k9_relat_1(B_209,k2_relat_1(A_210)) = k2_relat_1(k5_relat_1(A_210,B_209))
      | ~ v1_relat_1(B_209)
      | ~ v1_relat_1(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1424,plain,(
    ! [A_23,B_209] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_23),B_209)) = k9_relat_1(B_209,A_23)
      | ~ v1_relat_1(B_209)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1396])).

tff(c_1446,plain,(
    ! [A_211,B_212] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_211),B_212)) = k9_relat_1(B_212,A_211)
      | ~ v1_relat_1(B_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1424])).

tff(c_1473,plain,(
    ! [A_24,B_25] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_24,B_25))) = k9_relat_1(k6_relat_1(A_24),B_25)
      | ~ v1_relat_1(k6_relat_1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1446])).

tff(c_1477,plain,(
    ! [A_24,B_25] : k9_relat_1(k6_relat_1(A_24),B_25) = k3_xboole_0(A_24,B_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_26,c_1473])).

tff(c_42,plain,(
    ! [A_43] : m1_subset_1(k6_relat_1(A_43),k1_zfmisc_1(k2_zfmisc_1(A_43,A_43))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1113,plain,(
    ! [A_43] : v4_relat_1(k6_relat_1(A_43),A_43) ),
    inference(resolution,[status(thm)],[c_42,c_1106])).

tff(c_1248,plain,(
    ! [C_185,B_186,A_187] :
      ( v4_relat_1(C_185,B_186)
      | ~ v4_relat_1(C_185,A_187)
      | ~ v1_relat_1(C_185)
      | ~ r1_tarski(A_187,B_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1250,plain,(
    ! [A_43,B_186] :
      ( v4_relat_1(k6_relat_1(A_43),B_186)
      | ~ v1_relat_1(k6_relat_1(A_43))
      | ~ r1_tarski(A_43,B_186) ) ),
    inference(resolution,[status(thm)],[c_1113,c_1248])).

tff(c_1271,plain,(
    ! [A_189,B_190] :
      ( v4_relat_1(k6_relat_1(A_189),B_190)
      | ~ r1_tarski(A_189,B_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1250])).

tff(c_1276,plain,(
    ! [A_189,B_190] :
      ( k7_relat_1(k6_relat_1(A_189),B_190) = k6_relat_1(A_189)
      | ~ v1_relat_1(k6_relat_1(A_189))
      | ~ r1_tarski(A_189,B_190) ) ),
    inference(resolution,[status(thm)],[c_1271,c_20])).

tff(c_1321,plain,(
    ! [A_198,B_199] :
      ( k7_relat_1(k6_relat_1(A_198),B_199) = k6_relat_1(A_198)
      | ~ r1_tarski(A_198,B_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1276])).

tff(c_1331,plain,(
    ! [A_198,B_199] :
      ( k9_relat_1(k6_relat_1(A_198),B_199) = k2_relat_1(k6_relat_1(A_198))
      | ~ v1_relat_1(k6_relat_1(A_198))
      | ~ r1_tarski(A_198,B_199) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1321,c_12])).

tff(c_1343,plain,(
    ! [A_198,B_199] :
      ( k9_relat_1(k6_relat_1(A_198),B_199) = A_198
      | ~ r1_tarski(A_198,B_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_26,c_1331])).

tff(c_1487,plain,(
    ! [A_198,B_199] :
      ( k3_xboole_0(A_198,B_199) = A_198
      | ~ r1_tarski(A_198,B_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1477,c_1343])).

tff(c_2168,plain,(
    ! [A_270] :
      ( k3_xboole_0(k2_relat_1('#skF_3'),A_270) = k2_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_270) ) ),
    inference(resolution,[status(thm)],[c_2142,c_1487])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( k10_relat_1(B_15,k3_xboole_0(k2_relat_1(B_15),A_14)) = k10_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2187,plain,(
    ! [A_270] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_270)
      | ~ v1_relat_1('#skF_3')
      | ~ v5_relat_1('#skF_3',A_270) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2168,c_16])).

tff(c_2307,plain,(
    ! [A_274] :
      ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',A_274)
      | ~ v5_relat_1('#skF_3',A_274) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_2187])).

tff(c_2321,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1123,c_2307])).

tff(c_18,plain,(
    ! [A_16] :
      ( k10_relat_1(A_16,k2_relat_1(A_16)) = k1_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2326,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2321,c_18])).

tff(c_2333,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_2326])).

tff(c_2335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1746,c_2333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:28:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.80/1.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.67  
% 3.80/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.67  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.80/1.67  
% 3.80/1.67  %Foreground sorts:
% 3.80/1.67  
% 3.80/1.67  
% 3.80/1.67  %Background operators:
% 3.80/1.67  
% 3.80/1.67  
% 3.80/1.67  %Foreground operators:
% 3.80/1.67  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.80/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.67  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.80/1.67  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.80/1.67  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.80/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.80/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.80/1.67  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.80/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.80/1.67  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.80/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.80/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.80/1.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.80/1.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.80/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.80/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.67  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.80/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.80/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.80/1.67  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.80/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.80/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.80/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.80/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.80/1.67  
% 4.03/1.69  tff(f_113, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 4.03/1.69  tff(f_104, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.03/1.69  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.03/1.69  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.03/1.69  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.03/1.69  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.03/1.69  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 4.03/1.69  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 4.03/1.69  tff(f_100, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.03/1.69  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.03/1.69  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.03/1.69  tff(f_40, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 4.03/1.69  tff(f_80, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.03/1.69  tff(f_82, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 4.03/1.69  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 4.03/1.69  tff(f_106, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 4.03/1.69  tff(f_76, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => v4_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t217_relat_1)).
% 4.03/1.69  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 4.03/1.69  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 4.03/1.69  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.03/1.69  tff(c_1739, plain, (![A_235, B_236, C_237, D_238]: (k8_relset_1(A_235, B_236, C_237, D_238)=k10_relat_1(C_237, D_238) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.03/1.69  tff(c_1745, plain, (![D_238]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_238)=k10_relat_1('#skF_3', D_238))), inference(resolution, [status(thm)], [c_46, c_1739])).
% 4.03/1.69  tff(c_1290, plain, (![A_192, B_193, C_194]: (k1_relset_1(A_192, B_193, C_194)=k1_relat_1(C_194) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.03/1.69  tff(c_1299, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1290])).
% 4.03/1.69  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.03/1.69  tff(c_91, plain, (![B_52, A_53]: (v1_relat_1(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.03/1.69  tff(c_97, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_91])).
% 4.03/1.69  tff(c_103, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_97])).
% 4.03/1.69  tff(c_191, plain, (![C_74, A_75, B_76]: (v4_relat_1(C_74, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.03/1.69  tff(c_199, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_191])).
% 4.03/1.69  tff(c_20, plain, (![B_18, A_17]: (k7_relat_1(B_18, A_17)=B_18 | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.03/1.69  tff(c_219, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_199, c_20])).
% 4.03/1.69  tff(c_222, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_219])).
% 4.03/1.69  tff(c_12, plain, (![B_10, A_9]: (k2_relat_1(k7_relat_1(B_10, A_9))=k9_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.03/1.69  tff(c_233, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_222, c_12])).
% 4.03/1.69  tff(c_237, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_233])).
% 4.03/1.69  tff(c_1060, plain, (![A_151, B_152, C_153, D_154]: (k7_relset_1(A_151, B_152, C_153, D_154)=k9_relat_1(C_153, D_154) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.03/1.69  tff(c_1067, plain, (![D_154]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_154)=k9_relat_1('#skF_3', D_154))), inference(resolution, [status(thm)], [c_46, c_1060])).
% 4.03/1.69  tff(c_502, plain, (![A_106, B_107, C_108]: (k2_relset_1(A_106, B_107, C_108)=k2_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.03/1.69  tff(c_511, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_502])).
% 4.03/1.69  tff(c_44, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.03/1.69  tff(c_104, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 4.03/1.69  tff(c_522, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_511, c_104])).
% 4.03/1.69  tff(c_1068, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1067, c_522])).
% 4.03/1.69  tff(c_1071, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_237, c_1068])).
% 4.03/1.69  tff(c_1072, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 4.03/1.69  tff(c_1309, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1299, c_1072])).
% 4.03/1.69  tff(c_1746, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1745, c_1309])).
% 4.03/1.69  tff(c_1115, plain, (![C_168, B_169, A_170]: (v5_relat_1(C_168, B_169) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_170, B_169))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.03/1.69  tff(c_1123, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_1115])).
% 4.03/1.69  tff(c_1106, plain, (![C_165, A_166, B_167]: (v4_relat_1(C_165, A_166) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.03/1.69  tff(c_1114, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_1106])).
% 4.03/1.69  tff(c_1126, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1114, c_20])).
% 4.03/1.69  tff(c_1129, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_103, c_1126])).
% 4.03/1.69  tff(c_1145, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1129, c_12])).
% 4.03/1.69  tff(c_1149, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_1145])).
% 4.03/1.69  tff(c_1178, plain, (![B_175, A_176]: (r1_tarski(k2_relat_1(B_175), A_176) | ~v5_relat_1(B_175, A_176) | ~v1_relat_1(B_175))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.03/1.69  tff(c_2117, plain, (![B_266, A_267, A_268]: (r1_tarski(k9_relat_1(B_266, A_267), A_268) | ~v5_relat_1(k7_relat_1(B_266, A_267), A_268) | ~v1_relat_1(k7_relat_1(B_266, A_267)) | ~v1_relat_1(B_266))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1178])).
% 4.03/1.69  tff(c_2133, plain, (![A_268]: (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), A_268) | ~v5_relat_1('#skF_3', A_268) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1129, c_2117])).
% 4.03/1.69  tff(c_2142, plain, (![A_269]: (r1_tarski(k2_relat_1('#skF_3'), A_269) | ~v5_relat_1('#skF_3', A_269))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_103, c_1129, c_1149, c_2133])).
% 4.03/1.69  tff(c_8, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.03/1.69  tff(c_26, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.03/1.69  tff(c_28, plain, (![B_25, A_24]: (k5_relat_1(k6_relat_1(B_25), k6_relat_1(A_24))=k6_relat_1(k3_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.03/1.69  tff(c_1396, plain, (![B_209, A_210]: (k9_relat_1(B_209, k2_relat_1(A_210))=k2_relat_1(k5_relat_1(A_210, B_209)) | ~v1_relat_1(B_209) | ~v1_relat_1(A_210))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.03/1.69  tff(c_1424, plain, (![A_23, B_209]: (k2_relat_1(k5_relat_1(k6_relat_1(A_23), B_209))=k9_relat_1(B_209, A_23) | ~v1_relat_1(B_209) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1396])).
% 4.03/1.69  tff(c_1446, plain, (![A_211, B_212]: (k2_relat_1(k5_relat_1(k6_relat_1(A_211), B_212))=k9_relat_1(B_212, A_211) | ~v1_relat_1(B_212))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1424])).
% 4.03/1.69  tff(c_1473, plain, (![A_24, B_25]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_24, B_25)))=k9_relat_1(k6_relat_1(A_24), B_25) | ~v1_relat_1(k6_relat_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1446])).
% 4.03/1.69  tff(c_1477, plain, (![A_24, B_25]: (k9_relat_1(k6_relat_1(A_24), B_25)=k3_xboole_0(A_24, B_25))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_26, c_1473])).
% 4.03/1.69  tff(c_42, plain, (![A_43]: (m1_subset_1(k6_relat_1(A_43), k1_zfmisc_1(k2_zfmisc_1(A_43, A_43))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.03/1.69  tff(c_1113, plain, (![A_43]: (v4_relat_1(k6_relat_1(A_43), A_43))), inference(resolution, [status(thm)], [c_42, c_1106])).
% 4.03/1.69  tff(c_1248, plain, (![C_185, B_186, A_187]: (v4_relat_1(C_185, B_186) | ~v4_relat_1(C_185, A_187) | ~v1_relat_1(C_185) | ~r1_tarski(A_187, B_186))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.03/1.69  tff(c_1250, plain, (![A_43, B_186]: (v4_relat_1(k6_relat_1(A_43), B_186) | ~v1_relat_1(k6_relat_1(A_43)) | ~r1_tarski(A_43, B_186))), inference(resolution, [status(thm)], [c_1113, c_1248])).
% 4.03/1.69  tff(c_1271, plain, (![A_189, B_190]: (v4_relat_1(k6_relat_1(A_189), B_190) | ~r1_tarski(A_189, B_190))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1250])).
% 4.03/1.69  tff(c_1276, plain, (![A_189, B_190]: (k7_relat_1(k6_relat_1(A_189), B_190)=k6_relat_1(A_189) | ~v1_relat_1(k6_relat_1(A_189)) | ~r1_tarski(A_189, B_190))), inference(resolution, [status(thm)], [c_1271, c_20])).
% 4.03/1.69  tff(c_1321, plain, (![A_198, B_199]: (k7_relat_1(k6_relat_1(A_198), B_199)=k6_relat_1(A_198) | ~r1_tarski(A_198, B_199))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1276])).
% 4.03/1.69  tff(c_1331, plain, (![A_198, B_199]: (k9_relat_1(k6_relat_1(A_198), B_199)=k2_relat_1(k6_relat_1(A_198)) | ~v1_relat_1(k6_relat_1(A_198)) | ~r1_tarski(A_198, B_199))), inference(superposition, [status(thm), theory('equality')], [c_1321, c_12])).
% 4.03/1.69  tff(c_1343, plain, (![A_198, B_199]: (k9_relat_1(k6_relat_1(A_198), B_199)=A_198 | ~r1_tarski(A_198, B_199))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_26, c_1331])).
% 4.03/1.69  tff(c_1487, plain, (![A_198, B_199]: (k3_xboole_0(A_198, B_199)=A_198 | ~r1_tarski(A_198, B_199))), inference(demodulation, [status(thm), theory('equality')], [c_1477, c_1343])).
% 4.03/1.69  tff(c_2168, plain, (![A_270]: (k3_xboole_0(k2_relat_1('#skF_3'), A_270)=k2_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_270))), inference(resolution, [status(thm)], [c_2142, c_1487])).
% 4.03/1.69  tff(c_16, plain, (![B_15, A_14]: (k10_relat_1(B_15, k3_xboole_0(k2_relat_1(B_15), A_14))=k10_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.03/1.69  tff(c_2187, plain, (![A_270]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_270) | ~v1_relat_1('#skF_3') | ~v5_relat_1('#skF_3', A_270))), inference(superposition, [status(thm), theory('equality')], [c_2168, c_16])).
% 4.03/1.69  tff(c_2307, plain, (![A_274]: (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', A_274) | ~v5_relat_1('#skF_3', A_274))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_2187])).
% 4.03/1.69  tff(c_2321, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1123, c_2307])).
% 4.03/1.69  tff(c_18, plain, (![A_16]: (k10_relat_1(A_16, k2_relat_1(A_16))=k1_relat_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.03/1.69  tff(c_2326, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2321, c_18])).
% 4.03/1.69  tff(c_2333, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_2326])).
% 4.03/1.69  tff(c_2335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1746, c_2333])).
% 4.03/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.03/1.69  
% 4.03/1.69  Inference rules
% 4.03/1.69  ----------------------
% 4.03/1.69  #Ref     : 0
% 4.03/1.69  #Sup     : 506
% 4.03/1.69  #Fact    : 0
% 4.03/1.69  #Define  : 0
% 4.03/1.69  #Split   : 3
% 4.03/1.69  #Chain   : 0
% 4.03/1.69  #Close   : 0
% 4.03/1.69  
% 4.03/1.69  Ordering : KBO
% 4.03/1.69  
% 4.03/1.69  Simplification rules
% 4.03/1.69  ----------------------
% 4.03/1.69  #Subsume      : 41
% 4.03/1.69  #Demod        : 361
% 4.03/1.69  #Tautology    : 228
% 4.03/1.69  #SimpNegUnit  : 1
% 4.03/1.69  #BackRed      : 8
% 4.03/1.69  
% 4.03/1.69  #Partial instantiations: 0
% 4.03/1.69  #Strategies tried      : 1
% 4.03/1.69  
% 4.03/1.69  Timing (in seconds)
% 4.03/1.69  ----------------------
% 4.03/1.70  Preprocessing        : 0.33
% 4.03/1.70  Parsing              : 0.17
% 4.03/1.70  CNF conversion       : 0.02
% 4.03/1.70  Main loop            : 0.59
% 4.03/1.70  Inferencing          : 0.23
% 4.03/1.70  Reduction            : 0.19
% 4.03/1.70  Demodulation         : 0.14
% 4.03/1.70  BG Simplification    : 0.03
% 4.03/1.70  Subsumption          : 0.09
% 4.03/1.70  Abstraction          : 0.03
% 4.03/1.70  MUC search           : 0.00
% 4.03/1.70  Cooper               : 0.00
% 4.03/1.70  Total                : 0.96
% 4.03/1.70  Index Insertion      : 0.00
% 4.03/1.70  Index Deletion       : 0.00
% 4.03/1.70  Index Matching       : 0.00
% 4.03/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
