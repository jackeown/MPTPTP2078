%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:00 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 228 expanded)
%              Number of leaves         :   41 (  93 expanded)
%              Depth                    :   10
%              Number of atoms          :  183 ( 402 expanded)
%              Number of equality atoms :   69 ( 134 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_50,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(c_20,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_960,plain,(
    ! [B_167,A_168] :
      ( v1_relat_1(B_167)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(A_168))
      | ~ v1_relat_1(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_966,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_960])).

tff(c_970,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_966])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1134,plain,(
    ! [B_198,A_199] :
      ( k5_relat_1(B_198,k6_relat_1(A_199)) = B_198
      | ~ r1_tarski(k2_relat_1(B_198),A_199)
      | ~ v1_relat_1(B_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1151,plain,(
    ! [B_198] :
      ( k5_relat_1(B_198,k6_relat_1(k2_relat_1(B_198))) = B_198
      | ~ v1_relat_1(B_198) ) ),
    inference(resolution,[status(thm)],[c_6,c_1134])).

tff(c_18,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1355,plain,(
    ! [A_225,B_226] :
      ( k10_relat_1(A_225,k1_relat_1(B_226)) = k1_relat_1(k5_relat_1(A_225,B_226))
      | ~ v1_relat_1(B_226)
      | ~ v1_relat_1(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1364,plain,(
    ! [A_225,A_20] :
      ( k1_relat_1(k5_relat_1(A_225,k6_relat_1(A_20))) = k10_relat_1(A_225,A_20)
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ v1_relat_1(A_225) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1355])).

tff(c_1369,plain,(
    ! [A_227,A_228] :
      ( k1_relat_1(k5_relat_1(A_227,k6_relat_1(A_228))) = k10_relat_1(A_227,A_228)
      | ~ v1_relat_1(A_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1364])).

tff(c_1390,plain,(
    ! [B_198] :
      ( k10_relat_1(B_198,k2_relat_1(B_198)) = k1_relat_1(B_198)
      | ~ v1_relat_1(B_198)
      | ~ v1_relat_1(B_198) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1151,c_1369])).

tff(c_971,plain,(
    ! [C_169,A_170,B_171] :
      ( v4_relat_1(C_169,A_170)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_980,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_971])).

tff(c_1084,plain,(
    ! [B_191,A_192] :
      ( k7_relat_1(B_191,A_192) = B_191
      | ~ v4_relat_1(B_191,A_192)
      | ~ v1_relat_1(B_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1090,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_980,c_1084])).

tff(c_1096,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_1090])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( k2_relat_1(k7_relat_1(B_14,A_13)) = k9_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1100,plain,
    ( k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1096,c_22])).

tff(c_1104,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_1100])).

tff(c_1554,plain,(
    ! [A_239,B_240,C_241,D_242] :
      ( k7_relset_1(A_239,B_240,C_241,D_242) = k9_relat_1(C_241,D_242)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1561,plain,(
    ! [D_242] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_242) = k9_relat_1('#skF_3',D_242) ),
    inference(resolution,[status(thm)],[c_52,c_1554])).

tff(c_1452,plain,(
    ! [A_232,B_233,C_234,D_235] :
      ( k8_relset_1(A_232,B_233,C_234,D_235) = k10_relat_1(C_234,D_235)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1459,plain,(
    ! [D_235] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_235) = k10_relat_1('#skF_3',D_235) ),
    inference(resolution,[status(thm)],[c_52,c_1452])).

tff(c_96,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_102,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_52,c_96])).

tff(c_106,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_102])).

tff(c_171,plain,(
    ! [C_74,B_75,A_76] :
      ( v5_relat_1(C_74,B_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_180,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_171])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_270,plain,(
    ! [B_90,A_91] :
      ( k5_relat_1(B_90,k6_relat_1(A_91)) = B_90
      | ~ r1_tarski(k2_relat_1(B_90),A_91)
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_284,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_relat_1(A_8)) = B_9
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_270])).

tff(c_456,plain,(
    ! [A_107,B_108] :
      ( k10_relat_1(A_107,k1_relat_1(B_108)) = k1_relat_1(k5_relat_1(A_107,B_108))
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_465,plain,(
    ! [A_107,A_20] :
      ( k1_relat_1(k5_relat_1(A_107,k6_relat_1(A_20))) = k10_relat_1(A_107,A_20)
      | ~ v1_relat_1(k6_relat_1(A_20))
      | ~ v1_relat_1(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_456])).

tff(c_472,plain,(
    ! [A_111,A_112] :
      ( k1_relat_1(k5_relat_1(A_111,k6_relat_1(A_112))) = k10_relat_1(A_111,A_112)
      | ~ v1_relat_1(A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_465])).

tff(c_815,plain,(
    ! [B_155,A_156] :
      ( k10_relat_1(B_155,A_156) = k1_relat_1(B_155)
      | ~ v1_relat_1(B_155)
      | ~ v5_relat_1(B_155,A_156)
      | ~ v1_relat_1(B_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_472])).

tff(c_833,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_180,c_815])).

tff(c_847,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_833])).

tff(c_652,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( k8_relset_1(A_123,B_124,C_125,D_126) = k10_relat_1(C_125,D_126)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_659,plain,(
    ! [D_126] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_126) = k10_relat_1('#skF_3',D_126) ),
    inference(resolution,[status(thm)],[c_52,c_652])).

tff(c_634,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( k7_relset_1(A_118,B_119,C_120,D_121) = k9_relat_1(C_120,D_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_641,plain,(
    ! [D_121] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_121) = k9_relat_1('#skF_3',D_121) ),
    inference(resolution,[status(thm)],[c_52,c_634])).

tff(c_328,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_relset_1(A_96,B_97,C_98) = k2_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_337,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_328])).

tff(c_50,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_85,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_338,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_85])).

tff(c_642,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_338])).

tff(c_660,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_642])).

tff(c_849,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_660])).

tff(c_854,plain,(
    ! [D_157,B_158,C_159,A_160] :
      ( m1_subset_1(D_157,k1_zfmisc_1(k2_zfmisc_1(B_158,C_159)))
      | ~ r1_tarski(k1_relat_1(D_157),B_158)
      | ~ m1_subset_1(D_157,k1_zfmisc_1(k2_zfmisc_1(A_160,C_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_887,plain,(
    ! [B_163] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_163,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_163) ) ),
    inference(resolution,[status(thm)],[c_52,c_854])).

tff(c_36,plain,(
    ! [C_25,A_23,B_24] :
      ( v4_relat_1(C_25,A_23)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_926,plain,(
    ! [B_164] :
      ( v4_relat_1('#skF_3',B_164)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_164) ) ),
    inference(resolution,[status(thm)],[c_887,c_36])).

tff(c_931,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_926])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( k7_relat_1(B_19,A_18) = B_19
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_934,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_931,c_26])).

tff(c_937,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_934])).

tff(c_941,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_937,c_22])).

tff(c_945,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_941])).

tff(c_947,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_849,c_945])).

tff(c_948,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1461,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1459,c_948])).

tff(c_1582,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1104,c_1561,c_1461])).

tff(c_1585,plain,
    ( k1_relset_1('#skF_2','#skF_1','#skF_3') != k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1390,c_1582])).

tff(c_1587,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_970,c_1585])).

tff(c_1124,plain,(
    ! [C_195,B_196,A_197] :
      ( v5_relat_1(C_195,B_196)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_197,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1133,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1124])).

tff(c_1148,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_relat_1(A_8)) = B_9
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_1134])).

tff(c_1695,plain,(
    ! [B_263,A_264] :
      ( k10_relat_1(B_263,A_264) = k1_relat_1(B_263)
      | ~ v1_relat_1(B_263)
      | ~ v5_relat_1(B_263,A_264)
      | ~ v1_relat_1(B_263) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1148,c_1369])).

tff(c_1704,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1133,c_1695])).

tff(c_1720,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_1704])).

tff(c_1833,plain,(
    ! [A_269,B_270,C_271] :
      ( k8_relset_1(A_269,B_270,C_271,B_270) = k1_relset_1(A_269,B_270,C_271)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_269,B_270))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1838,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1833])).

tff(c_1841,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1720,c_1459,c_1838])).

tff(c_1843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1587,c_1841])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.66  
% 3.48/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.66  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.48/1.66  
% 3.48/1.66  %Foreground sorts:
% 3.48/1.66  
% 3.48/1.66  
% 3.48/1.66  %Background operators:
% 3.48/1.66  
% 3.48/1.66  
% 3.48/1.66  %Foreground operators:
% 3.48/1.66  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.48/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.48/1.66  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.48/1.66  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.48/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.48/1.66  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.48/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.48/1.66  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.48/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.48/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.48/1.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.48/1.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.48/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.48/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.66  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.48/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.48/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.48/1.66  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.48/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.48/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.48/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.48/1.66  
% 3.60/1.68  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.60/1.68  tff(f_116, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 3.60/1.68  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.60/1.68  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.60/1.68  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.60/1.68  tff(f_50, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.60/1.68  tff(f_73, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.60/1.68  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.60/1.68  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.60/1.68  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.60/1.68  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.60/1.68  tff(f_93, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.60/1.68  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.60/1.68  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.60/1.68  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.60/1.68  tff(f_103, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 3.60/1.68  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.60/1.68  tff(c_20, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.60/1.68  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.60/1.68  tff(c_960, plain, (![B_167, A_168]: (v1_relat_1(B_167) | ~m1_subset_1(B_167, k1_zfmisc_1(A_168)) | ~v1_relat_1(A_168))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.60/1.68  tff(c_966, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_960])).
% 3.60/1.68  tff(c_970, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_966])).
% 3.60/1.68  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.60/1.68  tff(c_1134, plain, (![B_198, A_199]: (k5_relat_1(B_198, k6_relat_1(A_199))=B_198 | ~r1_tarski(k2_relat_1(B_198), A_199) | ~v1_relat_1(B_198))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.60/1.68  tff(c_1151, plain, (![B_198]: (k5_relat_1(B_198, k6_relat_1(k2_relat_1(B_198)))=B_198 | ~v1_relat_1(B_198))), inference(resolution, [status(thm)], [c_6, c_1134])).
% 3.60/1.68  tff(c_18, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.60/1.68  tff(c_28, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.60/1.68  tff(c_1355, plain, (![A_225, B_226]: (k10_relat_1(A_225, k1_relat_1(B_226))=k1_relat_1(k5_relat_1(A_225, B_226)) | ~v1_relat_1(B_226) | ~v1_relat_1(A_225))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.60/1.68  tff(c_1364, plain, (![A_225, A_20]: (k1_relat_1(k5_relat_1(A_225, k6_relat_1(A_20)))=k10_relat_1(A_225, A_20) | ~v1_relat_1(k6_relat_1(A_20)) | ~v1_relat_1(A_225))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1355])).
% 3.60/1.68  tff(c_1369, plain, (![A_227, A_228]: (k1_relat_1(k5_relat_1(A_227, k6_relat_1(A_228)))=k10_relat_1(A_227, A_228) | ~v1_relat_1(A_227))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1364])).
% 3.60/1.68  tff(c_1390, plain, (![B_198]: (k10_relat_1(B_198, k2_relat_1(B_198))=k1_relat_1(B_198) | ~v1_relat_1(B_198) | ~v1_relat_1(B_198))), inference(superposition, [status(thm), theory('equality')], [c_1151, c_1369])).
% 3.60/1.68  tff(c_971, plain, (![C_169, A_170, B_171]: (v4_relat_1(C_169, A_170) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.60/1.68  tff(c_980, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_971])).
% 3.60/1.68  tff(c_1084, plain, (![B_191, A_192]: (k7_relat_1(B_191, A_192)=B_191 | ~v4_relat_1(B_191, A_192) | ~v1_relat_1(B_191))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.60/1.68  tff(c_1090, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_980, c_1084])).
% 3.60/1.68  tff(c_1096, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_970, c_1090])).
% 3.60/1.68  tff(c_22, plain, (![B_14, A_13]: (k2_relat_1(k7_relat_1(B_14, A_13))=k9_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.60/1.68  tff(c_1100, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1096, c_22])).
% 3.60/1.68  tff(c_1104, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_970, c_1100])).
% 3.60/1.68  tff(c_1554, plain, (![A_239, B_240, C_241, D_242]: (k7_relset_1(A_239, B_240, C_241, D_242)=k9_relat_1(C_241, D_242) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.60/1.68  tff(c_1561, plain, (![D_242]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_242)=k9_relat_1('#skF_3', D_242))), inference(resolution, [status(thm)], [c_52, c_1554])).
% 3.60/1.68  tff(c_1452, plain, (![A_232, B_233, C_234, D_235]: (k8_relset_1(A_232, B_233, C_234, D_235)=k10_relat_1(C_234, D_235) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.60/1.68  tff(c_1459, plain, (![D_235]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_235)=k10_relat_1('#skF_3', D_235))), inference(resolution, [status(thm)], [c_52, c_1452])).
% 3.60/1.68  tff(c_96, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.60/1.68  tff(c_102, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_52, c_96])).
% 3.60/1.68  tff(c_106, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_102])).
% 3.60/1.68  tff(c_171, plain, (![C_74, B_75, A_76]: (v5_relat_1(C_74, B_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.60/1.68  tff(c_180, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_171])).
% 3.60/1.68  tff(c_16, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.60/1.68  tff(c_270, plain, (![B_90, A_91]: (k5_relat_1(B_90, k6_relat_1(A_91))=B_90 | ~r1_tarski(k2_relat_1(B_90), A_91) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.60/1.68  tff(c_284, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_relat_1(A_8))=B_9 | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(resolution, [status(thm)], [c_16, c_270])).
% 3.60/1.68  tff(c_456, plain, (![A_107, B_108]: (k10_relat_1(A_107, k1_relat_1(B_108))=k1_relat_1(k5_relat_1(A_107, B_108)) | ~v1_relat_1(B_108) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.60/1.68  tff(c_465, plain, (![A_107, A_20]: (k1_relat_1(k5_relat_1(A_107, k6_relat_1(A_20)))=k10_relat_1(A_107, A_20) | ~v1_relat_1(k6_relat_1(A_20)) | ~v1_relat_1(A_107))), inference(superposition, [status(thm), theory('equality')], [c_28, c_456])).
% 3.60/1.68  tff(c_472, plain, (![A_111, A_112]: (k1_relat_1(k5_relat_1(A_111, k6_relat_1(A_112)))=k10_relat_1(A_111, A_112) | ~v1_relat_1(A_111))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_465])).
% 3.60/1.68  tff(c_815, plain, (![B_155, A_156]: (k10_relat_1(B_155, A_156)=k1_relat_1(B_155) | ~v1_relat_1(B_155) | ~v5_relat_1(B_155, A_156) | ~v1_relat_1(B_155))), inference(superposition, [status(thm), theory('equality')], [c_284, c_472])).
% 3.60/1.68  tff(c_833, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_180, c_815])).
% 3.60/1.68  tff(c_847, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_833])).
% 3.60/1.68  tff(c_652, plain, (![A_123, B_124, C_125, D_126]: (k8_relset_1(A_123, B_124, C_125, D_126)=k10_relat_1(C_125, D_126) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.60/1.68  tff(c_659, plain, (![D_126]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_126)=k10_relat_1('#skF_3', D_126))), inference(resolution, [status(thm)], [c_52, c_652])).
% 3.60/1.68  tff(c_634, plain, (![A_118, B_119, C_120, D_121]: (k7_relset_1(A_118, B_119, C_120, D_121)=k9_relat_1(C_120, D_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.60/1.68  tff(c_641, plain, (![D_121]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_121)=k9_relat_1('#skF_3', D_121))), inference(resolution, [status(thm)], [c_52, c_634])).
% 3.60/1.68  tff(c_328, plain, (![A_96, B_97, C_98]: (k2_relset_1(A_96, B_97, C_98)=k2_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.60/1.68  tff(c_337, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_328])).
% 3.60/1.68  tff(c_50, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.60/1.68  tff(c_85, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 3.60/1.68  tff(c_338, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_337, c_85])).
% 3.60/1.68  tff(c_642, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_641, c_338])).
% 3.60/1.68  tff(c_660, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_659, c_642])).
% 3.60/1.68  tff(c_849, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_847, c_660])).
% 3.60/1.68  tff(c_854, plain, (![D_157, B_158, C_159, A_160]: (m1_subset_1(D_157, k1_zfmisc_1(k2_zfmisc_1(B_158, C_159))) | ~r1_tarski(k1_relat_1(D_157), B_158) | ~m1_subset_1(D_157, k1_zfmisc_1(k2_zfmisc_1(A_160, C_159))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.60/1.68  tff(c_887, plain, (![B_163]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_163, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_163))), inference(resolution, [status(thm)], [c_52, c_854])).
% 3.60/1.68  tff(c_36, plain, (![C_25, A_23, B_24]: (v4_relat_1(C_25, A_23) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.60/1.68  tff(c_926, plain, (![B_164]: (v4_relat_1('#skF_3', B_164) | ~r1_tarski(k1_relat_1('#skF_3'), B_164))), inference(resolution, [status(thm)], [c_887, c_36])).
% 3.60/1.68  tff(c_931, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_926])).
% 3.60/1.68  tff(c_26, plain, (![B_19, A_18]: (k7_relat_1(B_19, A_18)=B_19 | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.60/1.68  tff(c_934, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_931, c_26])).
% 3.60/1.68  tff(c_937, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_934])).
% 3.60/1.68  tff(c_941, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_937, c_22])).
% 3.60/1.68  tff(c_945, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_941])).
% 3.60/1.68  tff(c_947, plain, $false, inference(negUnitSimplification, [status(thm)], [c_849, c_945])).
% 3.60/1.68  tff(c_948, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 3.60/1.68  tff(c_1461, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1459, c_948])).
% 3.60/1.68  tff(c_1582, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1104, c_1561, c_1461])).
% 3.60/1.68  tff(c_1585, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1390, c_1582])).
% 3.60/1.68  tff(c_1587, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_970, c_970, c_1585])).
% 3.60/1.68  tff(c_1124, plain, (![C_195, B_196, A_197]: (v5_relat_1(C_195, B_196) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_197, B_196))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.60/1.68  tff(c_1133, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_1124])).
% 3.60/1.68  tff(c_1148, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_relat_1(A_8))=B_9 | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(resolution, [status(thm)], [c_16, c_1134])).
% 3.60/1.68  tff(c_1695, plain, (![B_263, A_264]: (k10_relat_1(B_263, A_264)=k1_relat_1(B_263) | ~v1_relat_1(B_263) | ~v5_relat_1(B_263, A_264) | ~v1_relat_1(B_263))), inference(superposition, [status(thm), theory('equality')], [c_1148, c_1369])).
% 3.60/1.68  tff(c_1704, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1133, c_1695])).
% 3.60/1.68  tff(c_1720, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_970, c_1704])).
% 3.60/1.68  tff(c_1833, plain, (![A_269, B_270, C_271]: (k8_relset_1(A_269, B_270, C_271, B_270)=k1_relset_1(A_269, B_270, C_271) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_269, B_270))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.60/1.68  tff(c_1838, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_1833])).
% 3.60/1.68  tff(c_1841, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1720, c_1459, c_1838])).
% 3.60/1.68  tff(c_1843, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1587, c_1841])).
% 3.60/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.68  
% 3.60/1.68  Inference rules
% 3.60/1.68  ----------------------
% 3.60/1.68  #Ref     : 0
% 3.60/1.68  #Sup     : 374
% 3.60/1.68  #Fact    : 0
% 3.60/1.68  #Define  : 0
% 3.60/1.68  #Split   : 5
% 3.60/1.68  #Chain   : 0
% 3.60/1.68  #Close   : 0
% 3.60/1.68  
% 3.60/1.68  Ordering : KBO
% 3.60/1.68  
% 3.60/1.68  Simplification rules
% 3.60/1.68  ----------------------
% 3.60/1.68  #Subsume      : 18
% 3.60/1.68  #Demod        : 293
% 3.60/1.68  #Tautology    : 198
% 3.60/1.68  #SimpNegUnit  : 2
% 3.60/1.68  #BackRed      : 10
% 3.60/1.68  
% 3.60/1.68  #Partial instantiations: 0
% 3.60/1.68  #Strategies tried      : 1
% 3.60/1.68  
% 3.60/1.68  Timing (in seconds)
% 3.60/1.68  ----------------------
% 3.60/1.68  Preprocessing        : 0.34
% 3.60/1.68  Parsing              : 0.19
% 3.60/1.68  CNF conversion       : 0.02
% 3.60/1.68  Main loop            : 0.50
% 3.60/1.68  Inferencing          : 0.19
% 3.60/1.68  Reduction            : 0.16
% 3.60/1.68  Demodulation         : 0.12
% 3.60/1.69  BG Simplification    : 0.02
% 3.60/1.69  Subsumption          : 0.07
% 3.60/1.69  Abstraction          : 0.03
% 3.60/1.69  MUC search           : 0.00
% 3.60/1.69  Cooper               : 0.00
% 3.60/1.69  Total                : 0.88
% 3.60/1.69  Index Insertion      : 0.00
% 3.60/1.69  Index Deletion       : 0.00
% 3.60/1.69  Index Matching       : 0.00
% 3.60/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
