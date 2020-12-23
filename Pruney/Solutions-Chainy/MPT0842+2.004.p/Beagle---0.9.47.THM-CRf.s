%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:35 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 283 expanded)
%              Number of leaves         :   33 ( 108 expanded)
%              Depth                    :    9
%              Number of atoms          :  251 ( 844 expanded)
%              Number of equality atoms :    9 (  24 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ~ v1_xboole_0(C)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
                   => ! [E] :
                        ( m1_subset_1(E,A)
                       => ( r2_hidden(E,k8_relset_1(A,C,D,B))
                        <=> ? [F] :
                              ( m1_subset_1(F,C)
                              & r2_hidden(k4_tarski(E,F),D)
                              & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1025,plain,(
    ! [C_373,B_374,A_375] :
      ( v5_relat_1(C_373,B_374)
      | ~ m1_subset_1(C_373,k1_zfmisc_1(k2_zfmisc_1(A_375,B_374))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1034,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_1025])).

tff(c_67,plain,(
    ! [C_120,A_121,B_122] :
      ( v1_relat_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_76,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_67])).

tff(c_1334,plain,(
    ! [A_456,B_457,C_458,D_459] :
      ( k8_relset_1(A_456,B_457,C_458,D_459) = k10_relat_1(C_458,D_459)
      | ~ m1_subset_1(C_458,k1_zfmisc_1(k2_zfmisc_1(A_456,B_457))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1341,plain,(
    ! [D_459] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_459) = k10_relat_1('#skF_5',D_459) ),
    inference(resolution,[status(thm)],[c_34,c_1334])).

tff(c_116,plain,(
    ! [C_136,B_137,A_138] :
      ( v5_relat_1(C_136,B_137)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_125,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_116])).

tff(c_720,plain,(
    ! [A_312,B_313,C_314,D_315] :
      ( k8_relset_1(A_312,B_313,C_314,D_315) = k10_relat_1(C_314,D_315)
      | ~ m1_subset_1(C_314,k1_zfmisc_1(k2_zfmisc_1(A_312,B_313))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_727,plain,(
    ! [D_315] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_315) = k10_relat_1('#skF_5',D_315) ),
    inference(resolution,[status(thm)],[c_34,c_720])).

tff(c_409,plain,(
    ! [A_232,B_233,C_234,D_235] :
      ( k8_relset_1(A_232,B_233,C_234,D_235) = k10_relat_1(C_234,D_235)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_416,plain,(
    ! [D_235] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_235) = k10_relat_1('#skF_5',D_235) ),
    inference(resolution,[status(thm)],[c_34,c_409])).

tff(c_56,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | m1_subset_1('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_126,plain,(
    m1_subset_1('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_48,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | r2_hidden('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_77,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_52,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_153,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_251,plain,(
    ! [A_180,B_181,C_182,D_183] :
      ( k8_relset_1(A_180,B_181,C_182,D_183) = k10_relat_1(C_182,D_183)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_262,plain,(
    ! [D_183] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_183) = k10_relat_1('#skF_5',D_183) ),
    inference(resolution,[status(thm)],[c_34,c_251])).

tff(c_42,plain,(
    ! [F_115] :
      ( ~ r2_hidden(F_115,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_115),'#skF_5')
      | ~ m1_subset_1(F_115,'#skF_4')
      | ~ r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_313,plain,(
    ! [F_115] :
      ( ~ r2_hidden(F_115,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_115),'#skF_5')
      | ~ m1_subset_1(F_115,'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_42])).

tff(c_314,plain,(
    ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_20,plain,(
    ! [B_15,C_16,A_14] :
      ( r2_hidden(B_15,k2_relat_1(C_16))
      | ~ r2_hidden(k4_tarski(A_14,B_15),C_16)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_158,plain,
    ( r2_hidden('#skF_7',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_153,c_20])).

tff(c_162,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_158])).

tff(c_338,plain,(
    ! [A_211,C_212,B_213,D_214] :
      ( r2_hidden(A_211,k10_relat_1(C_212,B_213))
      | ~ r2_hidden(D_214,B_213)
      | ~ r2_hidden(k4_tarski(A_211,D_214),C_212)
      | ~ r2_hidden(D_214,k2_relat_1(C_212))
      | ~ v1_relat_1(C_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_360,plain,(
    ! [A_215,C_216] :
      ( r2_hidden(A_215,k10_relat_1(C_216,'#skF_3'))
      | ~ r2_hidden(k4_tarski(A_215,'#skF_7'),C_216)
      | ~ r2_hidden('#skF_7',k2_relat_1(C_216))
      | ~ v1_relat_1(C_216) ) ),
    inference(resolution,[status(thm)],[c_77,c_338])).

tff(c_363,plain,
    ( r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ r2_hidden('#skF_7',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_153,c_360])).

tff(c_366,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_162,c_363])).

tff(c_368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_366])).

tff(c_381,plain,(
    ! [F_218] :
      ( ~ r2_hidden(F_218,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_218),'#skF_5')
      | ~ m1_subset_1(F_218,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_388,plain,
    ( ~ r2_hidden('#skF_7','#skF_3')
    | ~ m1_subset_1('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_153,c_381])).

tff(c_395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_77,c_388])).

tff(c_396,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_418,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_396])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_442,plain,(
    ! [A_242,B_243,C_244] :
      ( r2_hidden('#skF_1'(A_242,B_243,C_244),k2_relat_1(C_244))
      | ~ r2_hidden(A_242,k10_relat_1(C_244,B_243))
      | ~ v1_relat_1(C_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_138,plain,(
    ! [A_142,C_143,B_144] :
      ( m1_subset_1(A_142,C_143)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(C_143))
      | ~ r2_hidden(A_142,B_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_143,plain,(
    ! [A_142,B_2,A_1] :
      ( m1_subset_1(A_142,B_2)
      | ~ r2_hidden(A_142,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_138])).

tff(c_597,plain,(
    ! [A_270,B_271,C_272,B_273] :
      ( m1_subset_1('#skF_1'(A_270,B_271,C_272),B_273)
      | ~ r1_tarski(k2_relat_1(C_272),B_273)
      | ~ r2_hidden(A_270,k10_relat_1(C_272,B_271))
      | ~ v1_relat_1(C_272) ) ),
    inference(resolution,[status(thm)],[c_442,c_143])).

tff(c_630,plain,(
    ! [A_276,B_277,B_278,A_279] :
      ( m1_subset_1('#skF_1'(A_276,B_277,B_278),A_279)
      | ~ r2_hidden(A_276,k10_relat_1(B_278,B_277))
      | ~ v5_relat_1(B_278,A_279)
      | ~ v1_relat_1(B_278) ) ),
    inference(resolution,[status(thm)],[c_10,c_597])).

tff(c_637,plain,(
    ! [A_279] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_279)
      | ~ v5_relat_1('#skF_5',A_279)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_418,c_630])).

tff(c_647,plain,(
    ! [A_280] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_280)
      | ~ v5_relat_1('#skF_5',A_280) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_637])).

tff(c_14,plain,(
    ! [A_8,B_9,C_10] :
      ( r2_hidden('#skF_1'(A_8,B_9,C_10),B_9)
      | ~ r2_hidden(A_8,k10_relat_1(C_10,B_9))
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_8,B_9,C_10] :
      ( r2_hidden(k4_tarski(A_8,'#skF_1'(A_8,B_9,C_10)),C_10)
      | ~ r2_hidden(A_8,k10_relat_1(C_10,B_9))
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_397,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,(
    ! [F_115] :
      ( ~ r2_hidden(F_115,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_115),'#skF_5')
      | ~ m1_subset_1(F_115,'#skF_4')
      | r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_480,plain,(
    ! [F_251] :
      ( ~ r2_hidden(F_251,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_251),'#skF_5')
      | ~ m1_subset_1(F_251,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_397,c_50])).

tff(c_484,plain,(
    ! [B_9] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_9,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_9,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_9))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_480])).

tff(c_556,plain,(
    ! [B_261] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_261,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_261,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_261)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_484])).

tff(c_560,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_556])).

tff(c_563,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_418,c_560])).

tff(c_650,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_647,c_563])).

tff(c_676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_650])).

tff(c_677,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_729,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_727,c_677])).

tff(c_743,plain,(
    ! [A_318,B_319,C_320] :
      ( r2_hidden('#skF_1'(A_318,B_319,C_320),k2_relat_1(C_320))
      | ~ r2_hidden(A_318,k10_relat_1(C_320,B_319))
      | ~ v1_relat_1(C_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_679,plain,(
    ! [A_281,C_282,B_283] :
      ( m1_subset_1(A_281,C_282)
      | ~ m1_subset_1(B_283,k1_zfmisc_1(C_282))
      | ~ r2_hidden(A_281,B_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_684,plain,(
    ! [A_281,B_2,A_1] :
      ( m1_subset_1(A_281,B_2)
      | ~ r2_hidden(A_281,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_679])).

tff(c_933,plain,(
    ! [A_351,B_352,C_353,B_354] :
      ( m1_subset_1('#skF_1'(A_351,B_352,C_353),B_354)
      | ~ r1_tarski(k2_relat_1(C_353),B_354)
      | ~ r2_hidden(A_351,k10_relat_1(C_353,B_352))
      | ~ v1_relat_1(C_353) ) ),
    inference(resolution,[status(thm)],[c_743,c_684])).

tff(c_937,plain,(
    ! [A_355,B_356,B_357,A_358] :
      ( m1_subset_1('#skF_1'(A_355,B_356,B_357),A_358)
      | ~ r2_hidden(A_355,k10_relat_1(B_357,B_356))
      | ~ v5_relat_1(B_357,A_358)
      | ~ v1_relat_1(B_357) ) ),
    inference(resolution,[status(thm)],[c_10,c_933])).

tff(c_944,plain,(
    ! [A_358] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_358)
      | ~ v5_relat_1('#skF_5',A_358)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_729,c_937])).

tff(c_954,plain,(
    ! [A_359] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_359)
      | ~ v5_relat_1('#skF_5',A_359) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_944])).

tff(c_756,plain,(
    ! [A_325,B_326,C_327] :
      ( r2_hidden(k4_tarski(A_325,'#skF_1'(A_325,B_326,C_327)),C_327)
      | ~ r2_hidden(A_325,k10_relat_1(C_327,B_326))
      | ~ v1_relat_1(C_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_678,plain,(
    ~ m1_subset_1('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,(
    ! [F_115] :
      ( ~ r2_hidden(F_115,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_115),'#skF_5')
      | ~ m1_subset_1(F_115,'#skF_4')
      | m1_subset_1('#skF_7','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_718,plain,(
    ! [F_115] :
      ( ~ r2_hidden(F_115,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_115),'#skF_5')
      | ~ m1_subset_1(F_115,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_678,c_54])).

tff(c_760,plain,(
    ! [B_326] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_326,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_326,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_326))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_756,c_718])).

tff(c_863,plain,(
    ! [B_340] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_340,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_340,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_340)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_760])).

tff(c_867,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_863])).

tff(c_870,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_729,c_867])).

tff(c_957,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_954,c_870])).

tff(c_983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_957])).

tff(c_984,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1343,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1341,c_984])).

tff(c_1330,plain,(
    ! [A_453,B_454,C_455] :
      ( r2_hidden('#skF_1'(A_453,B_454,C_455),k2_relat_1(C_455))
      | ~ r2_hidden(A_453,k10_relat_1(C_455,B_454))
      | ~ v1_relat_1(C_455) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1035,plain,(
    ! [A_376,C_377,B_378] :
      ( m1_subset_1(A_376,C_377)
      | ~ m1_subset_1(B_378,k1_zfmisc_1(C_377))
      | ~ r2_hidden(A_376,B_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1040,plain,(
    ! [A_376,B_2,A_1] :
      ( m1_subset_1(A_376,B_2)
      | ~ r2_hidden(A_376,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_1035])).

tff(c_1535,plain,(
    ! [A_494,B_495,C_496,B_497] :
      ( m1_subset_1('#skF_1'(A_494,B_495,C_496),B_497)
      | ~ r1_tarski(k2_relat_1(C_496),B_497)
      | ~ r2_hidden(A_494,k10_relat_1(C_496,B_495))
      | ~ v1_relat_1(C_496) ) ),
    inference(resolution,[status(thm)],[c_1330,c_1040])).

tff(c_1549,plain,(
    ! [A_503,B_504,B_505,A_506] :
      ( m1_subset_1('#skF_1'(A_503,B_504,B_505),A_506)
      | ~ r2_hidden(A_503,k10_relat_1(B_505,B_504))
      | ~ v5_relat_1(B_505,A_506)
      | ~ v1_relat_1(B_505) ) ),
    inference(resolution,[status(thm)],[c_10,c_1535])).

tff(c_1556,plain,(
    ! [A_506] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_506)
      | ~ v5_relat_1('#skF_5',A_506)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1343,c_1549])).

tff(c_1566,plain,(
    ! [A_507] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_507)
      | ~ v5_relat_1('#skF_5',A_507) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1556])).

tff(c_1366,plain,(
    ! [A_466,B_467,C_468] :
      ( r2_hidden(k4_tarski(A_466,'#skF_1'(A_466,B_467,C_468)),C_468)
      | ~ r2_hidden(A_466,k10_relat_1(C_468,B_467))
      | ~ v1_relat_1(C_468) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_985,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [F_115] :
      ( ~ r2_hidden(F_115,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_115),'#skF_5')
      | ~ m1_subset_1(F_115,'#skF_4')
      | r2_hidden('#skF_7','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1328,plain,(
    ! [F_115] :
      ( ~ r2_hidden(F_115,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_115),'#skF_5')
      | ~ m1_subset_1(F_115,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_985,c_46])).

tff(c_1370,plain,(
    ! [B_467] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_467,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_467,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_467))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1366,c_1328])).

tff(c_1451,plain,(
    ! [B_478] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_478,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_478,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_478)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1370])).

tff(c_1455,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_1451])).

tff(c_1458,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1343,c_1455])).

tff(c_1569,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1566,c_1458])).

tff(c_1595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1034,c_1569])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:30:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.61  
% 3.43/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.62  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.43/1.62  
% 3.43/1.62  %Foreground sorts:
% 3.43/1.62  
% 3.43/1.62  
% 3.43/1.62  %Background operators:
% 3.43/1.62  
% 3.43/1.62  
% 3.43/1.62  %Foreground operators:
% 3.43/1.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.43/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.43/1.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.43/1.62  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.43/1.62  tff('#skF_7', type, '#skF_7': $i).
% 3.43/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.43/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.43/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.43/1.62  tff('#skF_6', type, '#skF_6': $i).
% 3.43/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.43/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.43/1.62  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.43/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.43/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.62  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.43/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.43/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.43/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.43/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.62  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.43/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.43/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.43/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.43/1.62  
% 3.82/1.64  tff(f_101, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_relset_1)).
% 3.82/1.64  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.82/1.64  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.82/1.64  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.82/1.64  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 3.82/1.64  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 3.82/1.64  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.82/1.64  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.82/1.64  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.82/1.64  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.82/1.64  tff(c_1025, plain, (![C_373, B_374, A_375]: (v5_relat_1(C_373, B_374) | ~m1_subset_1(C_373, k1_zfmisc_1(k2_zfmisc_1(A_375, B_374))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.82/1.64  tff(c_1034, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_1025])).
% 3.82/1.64  tff(c_67, plain, (![C_120, A_121, B_122]: (v1_relat_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.82/1.64  tff(c_76, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_67])).
% 3.82/1.64  tff(c_1334, plain, (![A_456, B_457, C_458, D_459]: (k8_relset_1(A_456, B_457, C_458, D_459)=k10_relat_1(C_458, D_459) | ~m1_subset_1(C_458, k1_zfmisc_1(k2_zfmisc_1(A_456, B_457))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.82/1.64  tff(c_1341, plain, (![D_459]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_459)=k10_relat_1('#skF_5', D_459))), inference(resolution, [status(thm)], [c_34, c_1334])).
% 3.82/1.64  tff(c_116, plain, (![C_136, B_137, A_138]: (v5_relat_1(C_136, B_137) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.82/1.64  tff(c_125, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_116])).
% 3.82/1.64  tff(c_720, plain, (![A_312, B_313, C_314, D_315]: (k8_relset_1(A_312, B_313, C_314, D_315)=k10_relat_1(C_314, D_315) | ~m1_subset_1(C_314, k1_zfmisc_1(k2_zfmisc_1(A_312, B_313))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.82/1.64  tff(c_727, plain, (![D_315]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_315)=k10_relat_1('#skF_5', D_315))), inference(resolution, [status(thm)], [c_34, c_720])).
% 3.82/1.64  tff(c_409, plain, (![A_232, B_233, C_234, D_235]: (k8_relset_1(A_232, B_233, C_234, D_235)=k10_relat_1(C_234, D_235) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.82/1.64  tff(c_416, plain, (![D_235]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_235)=k10_relat_1('#skF_5', D_235))), inference(resolution, [status(thm)], [c_34, c_409])).
% 3.82/1.64  tff(c_56, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | m1_subset_1('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.82/1.64  tff(c_126, plain, (m1_subset_1('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_56])).
% 3.82/1.64  tff(c_48, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | r2_hidden('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.82/1.64  tff(c_77, plain, (r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 3.82/1.64  tff(c_52, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.82/1.64  tff(c_153, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(splitLeft, [status(thm)], [c_52])).
% 3.82/1.64  tff(c_251, plain, (![A_180, B_181, C_182, D_183]: (k8_relset_1(A_180, B_181, C_182, D_183)=k10_relat_1(C_182, D_183) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.82/1.64  tff(c_262, plain, (![D_183]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_183)=k10_relat_1('#skF_5', D_183))), inference(resolution, [status(thm)], [c_34, c_251])).
% 3.82/1.64  tff(c_42, plain, (![F_115]: (~r2_hidden(F_115, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_115), '#skF_5') | ~m1_subset_1(F_115, '#skF_4') | ~r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.82/1.64  tff(c_313, plain, (![F_115]: (~r2_hidden(F_115, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_115), '#skF_5') | ~m1_subset_1(F_115, '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_42])).
% 3.82/1.64  tff(c_314, plain, (~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_313])).
% 3.82/1.64  tff(c_20, plain, (![B_15, C_16, A_14]: (r2_hidden(B_15, k2_relat_1(C_16)) | ~r2_hidden(k4_tarski(A_14, B_15), C_16) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.82/1.64  tff(c_158, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_153, c_20])).
% 3.82/1.64  tff(c_162, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_158])).
% 3.82/1.64  tff(c_338, plain, (![A_211, C_212, B_213, D_214]: (r2_hidden(A_211, k10_relat_1(C_212, B_213)) | ~r2_hidden(D_214, B_213) | ~r2_hidden(k4_tarski(A_211, D_214), C_212) | ~r2_hidden(D_214, k2_relat_1(C_212)) | ~v1_relat_1(C_212))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.82/1.64  tff(c_360, plain, (![A_215, C_216]: (r2_hidden(A_215, k10_relat_1(C_216, '#skF_3')) | ~r2_hidden(k4_tarski(A_215, '#skF_7'), C_216) | ~r2_hidden('#skF_7', k2_relat_1(C_216)) | ~v1_relat_1(C_216))), inference(resolution, [status(thm)], [c_77, c_338])).
% 3.82/1.64  tff(c_363, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~r2_hidden('#skF_7', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_153, c_360])).
% 3.82/1.64  tff(c_366, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_162, c_363])).
% 3.82/1.64  tff(c_368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_314, c_366])).
% 3.82/1.64  tff(c_381, plain, (![F_218]: (~r2_hidden(F_218, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_218), '#skF_5') | ~m1_subset_1(F_218, '#skF_4'))), inference(splitRight, [status(thm)], [c_313])).
% 3.82/1.64  tff(c_388, plain, (~r2_hidden('#skF_7', '#skF_3') | ~m1_subset_1('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_153, c_381])).
% 3.82/1.64  tff(c_395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_77, c_388])).
% 3.82/1.64  tff(c_396, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_52])).
% 3.82/1.64  tff(c_418, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_416, c_396])).
% 3.82/1.64  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.82/1.64  tff(c_442, plain, (![A_242, B_243, C_244]: (r2_hidden('#skF_1'(A_242, B_243, C_244), k2_relat_1(C_244)) | ~r2_hidden(A_242, k10_relat_1(C_244, B_243)) | ~v1_relat_1(C_244))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.82/1.64  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.82/1.64  tff(c_138, plain, (![A_142, C_143, B_144]: (m1_subset_1(A_142, C_143) | ~m1_subset_1(B_144, k1_zfmisc_1(C_143)) | ~r2_hidden(A_142, B_144))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.82/1.64  tff(c_143, plain, (![A_142, B_2, A_1]: (m1_subset_1(A_142, B_2) | ~r2_hidden(A_142, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_138])).
% 3.82/1.64  tff(c_597, plain, (![A_270, B_271, C_272, B_273]: (m1_subset_1('#skF_1'(A_270, B_271, C_272), B_273) | ~r1_tarski(k2_relat_1(C_272), B_273) | ~r2_hidden(A_270, k10_relat_1(C_272, B_271)) | ~v1_relat_1(C_272))), inference(resolution, [status(thm)], [c_442, c_143])).
% 3.82/1.64  tff(c_630, plain, (![A_276, B_277, B_278, A_279]: (m1_subset_1('#skF_1'(A_276, B_277, B_278), A_279) | ~r2_hidden(A_276, k10_relat_1(B_278, B_277)) | ~v5_relat_1(B_278, A_279) | ~v1_relat_1(B_278))), inference(resolution, [status(thm)], [c_10, c_597])).
% 3.82/1.64  tff(c_637, plain, (![A_279]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_279) | ~v5_relat_1('#skF_5', A_279) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_418, c_630])).
% 3.82/1.64  tff(c_647, plain, (![A_280]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_280) | ~v5_relat_1('#skF_5', A_280))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_637])).
% 3.82/1.64  tff(c_14, plain, (![A_8, B_9, C_10]: (r2_hidden('#skF_1'(A_8, B_9, C_10), B_9) | ~r2_hidden(A_8, k10_relat_1(C_10, B_9)) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.82/1.64  tff(c_16, plain, (![A_8, B_9, C_10]: (r2_hidden(k4_tarski(A_8, '#skF_1'(A_8, B_9, C_10)), C_10) | ~r2_hidden(A_8, k10_relat_1(C_10, B_9)) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.82/1.64  tff(c_397, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 3.82/1.64  tff(c_50, plain, (![F_115]: (~r2_hidden(F_115, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_115), '#skF_5') | ~m1_subset_1(F_115, '#skF_4') | r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.82/1.64  tff(c_480, plain, (![F_251]: (~r2_hidden(F_251, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_251), '#skF_5') | ~m1_subset_1(F_251, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_397, c_50])).
% 3.82/1.64  tff(c_484, plain, (![B_9]: (~r2_hidden('#skF_1'('#skF_6', B_9, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_9, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_9)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_480])).
% 3.82/1.64  tff(c_556, plain, (![B_261]: (~r2_hidden('#skF_1'('#skF_6', B_261, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_261, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_261)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_484])).
% 3.82/1.64  tff(c_560, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14, c_556])).
% 3.82/1.64  tff(c_563, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_418, c_560])).
% 3.82/1.64  tff(c_650, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_647, c_563])).
% 3.82/1.64  tff(c_676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_650])).
% 3.82/1.64  tff(c_677, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_56])).
% 3.82/1.64  tff(c_729, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_727, c_677])).
% 3.82/1.64  tff(c_743, plain, (![A_318, B_319, C_320]: (r2_hidden('#skF_1'(A_318, B_319, C_320), k2_relat_1(C_320)) | ~r2_hidden(A_318, k10_relat_1(C_320, B_319)) | ~v1_relat_1(C_320))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.82/1.64  tff(c_679, plain, (![A_281, C_282, B_283]: (m1_subset_1(A_281, C_282) | ~m1_subset_1(B_283, k1_zfmisc_1(C_282)) | ~r2_hidden(A_281, B_283))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.82/1.64  tff(c_684, plain, (![A_281, B_2, A_1]: (m1_subset_1(A_281, B_2) | ~r2_hidden(A_281, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_679])).
% 3.82/1.64  tff(c_933, plain, (![A_351, B_352, C_353, B_354]: (m1_subset_1('#skF_1'(A_351, B_352, C_353), B_354) | ~r1_tarski(k2_relat_1(C_353), B_354) | ~r2_hidden(A_351, k10_relat_1(C_353, B_352)) | ~v1_relat_1(C_353))), inference(resolution, [status(thm)], [c_743, c_684])).
% 3.82/1.64  tff(c_937, plain, (![A_355, B_356, B_357, A_358]: (m1_subset_1('#skF_1'(A_355, B_356, B_357), A_358) | ~r2_hidden(A_355, k10_relat_1(B_357, B_356)) | ~v5_relat_1(B_357, A_358) | ~v1_relat_1(B_357))), inference(resolution, [status(thm)], [c_10, c_933])).
% 3.82/1.64  tff(c_944, plain, (![A_358]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_358) | ~v5_relat_1('#skF_5', A_358) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_729, c_937])).
% 3.82/1.64  tff(c_954, plain, (![A_359]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_359) | ~v5_relat_1('#skF_5', A_359))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_944])).
% 3.82/1.64  tff(c_756, plain, (![A_325, B_326, C_327]: (r2_hidden(k4_tarski(A_325, '#skF_1'(A_325, B_326, C_327)), C_327) | ~r2_hidden(A_325, k10_relat_1(C_327, B_326)) | ~v1_relat_1(C_327))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.82/1.64  tff(c_678, plain, (~m1_subset_1('#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 3.82/1.64  tff(c_54, plain, (![F_115]: (~r2_hidden(F_115, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_115), '#skF_5') | ~m1_subset_1(F_115, '#skF_4') | m1_subset_1('#skF_7', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.82/1.64  tff(c_718, plain, (![F_115]: (~r2_hidden(F_115, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_115), '#skF_5') | ~m1_subset_1(F_115, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_678, c_54])).
% 3.82/1.64  tff(c_760, plain, (![B_326]: (~r2_hidden('#skF_1'('#skF_6', B_326, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_326, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_326)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_756, c_718])).
% 3.82/1.64  tff(c_863, plain, (![B_340]: (~r2_hidden('#skF_1'('#skF_6', B_340, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_340, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_340)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_760])).
% 3.82/1.64  tff(c_867, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14, c_863])).
% 3.82/1.64  tff(c_870, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_729, c_867])).
% 3.82/1.64  tff(c_957, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_954, c_870])).
% 3.82/1.64  tff(c_983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_957])).
% 3.82/1.64  tff(c_984, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_48])).
% 3.82/1.64  tff(c_1343, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1341, c_984])).
% 3.82/1.64  tff(c_1330, plain, (![A_453, B_454, C_455]: (r2_hidden('#skF_1'(A_453, B_454, C_455), k2_relat_1(C_455)) | ~r2_hidden(A_453, k10_relat_1(C_455, B_454)) | ~v1_relat_1(C_455))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.82/1.64  tff(c_1035, plain, (![A_376, C_377, B_378]: (m1_subset_1(A_376, C_377) | ~m1_subset_1(B_378, k1_zfmisc_1(C_377)) | ~r2_hidden(A_376, B_378))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.82/1.64  tff(c_1040, plain, (![A_376, B_2, A_1]: (m1_subset_1(A_376, B_2) | ~r2_hidden(A_376, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_1035])).
% 3.82/1.64  tff(c_1535, plain, (![A_494, B_495, C_496, B_497]: (m1_subset_1('#skF_1'(A_494, B_495, C_496), B_497) | ~r1_tarski(k2_relat_1(C_496), B_497) | ~r2_hidden(A_494, k10_relat_1(C_496, B_495)) | ~v1_relat_1(C_496))), inference(resolution, [status(thm)], [c_1330, c_1040])).
% 3.82/1.64  tff(c_1549, plain, (![A_503, B_504, B_505, A_506]: (m1_subset_1('#skF_1'(A_503, B_504, B_505), A_506) | ~r2_hidden(A_503, k10_relat_1(B_505, B_504)) | ~v5_relat_1(B_505, A_506) | ~v1_relat_1(B_505))), inference(resolution, [status(thm)], [c_10, c_1535])).
% 3.82/1.64  tff(c_1556, plain, (![A_506]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_506) | ~v5_relat_1('#skF_5', A_506) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1343, c_1549])).
% 3.82/1.64  tff(c_1566, plain, (![A_507]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_507) | ~v5_relat_1('#skF_5', A_507))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1556])).
% 3.82/1.64  tff(c_1366, plain, (![A_466, B_467, C_468]: (r2_hidden(k4_tarski(A_466, '#skF_1'(A_466, B_467, C_468)), C_468) | ~r2_hidden(A_466, k10_relat_1(C_468, B_467)) | ~v1_relat_1(C_468))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.82/1.64  tff(c_985, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 3.82/1.64  tff(c_46, plain, (![F_115]: (~r2_hidden(F_115, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_115), '#skF_5') | ~m1_subset_1(F_115, '#skF_4') | r2_hidden('#skF_7', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.82/1.64  tff(c_1328, plain, (![F_115]: (~r2_hidden(F_115, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_115), '#skF_5') | ~m1_subset_1(F_115, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_985, c_46])).
% 3.82/1.64  tff(c_1370, plain, (![B_467]: (~r2_hidden('#skF_1'('#skF_6', B_467, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_467, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_467)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1366, c_1328])).
% 3.82/1.64  tff(c_1451, plain, (![B_478]: (~r2_hidden('#skF_1'('#skF_6', B_478, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_478, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_478)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1370])).
% 3.82/1.64  tff(c_1455, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14, c_1451])).
% 3.82/1.64  tff(c_1458, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1343, c_1455])).
% 3.82/1.64  tff(c_1569, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1566, c_1458])).
% 3.82/1.64  tff(c_1595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1034, c_1569])).
% 3.82/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.64  
% 3.82/1.64  Inference rules
% 3.82/1.64  ----------------------
% 3.82/1.64  #Ref     : 0
% 3.82/1.64  #Sup     : 321
% 3.82/1.64  #Fact    : 0
% 3.82/1.64  #Define  : 0
% 3.82/1.64  #Split   : 10
% 3.82/1.64  #Chain   : 0
% 3.82/1.64  #Close   : 0
% 3.82/1.64  
% 3.82/1.64  Ordering : KBO
% 3.82/1.64  
% 3.82/1.64  Simplification rules
% 3.82/1.64  ----------------------
% 3.82/1.64  #Subsume      : 48
% 3.82/1.64  #Demod        : 77
% 3.82/1.64  #Tautology    : 38
% 3.82/1.64  #SimpNegUnit  : 5
% 3.82/1.64  #BackRed      : 8
% 3.82/1.64  
% 3.82/1.64  #Partial instantiations: 0
% 3.82/1.64  #Strategies tried      : 1
% 3.82/1.64  
% 3.82/1.64  Timing (in seconds)
% 3.82/1.64  ----------------------
% 3.82/1.64  Preprocessing        : 0.32
% 3.82/1.64  Parsing              : 0.17
% 3.82/1.64  CNF conversion       : 0.03
% 3.82/1.64  Main loop            : 0.53
% 3.82/1.64  Inferencing          : 0.21
% 3.82/1.64  Reduction            : 0.15
% 3.82/1.64  Demodulation         : 0.10
% 3.82/1.64  BG Simplification    : 0.02
% 3.82/1.64  Subsumption          : 0.09
% 3.82/1.64  Abstraction          : 0.03
% 3.82/1.65  MUC search           : 0.00
% 3.82/1.65  Cooper               : 0.00
% 3.82/1.65  Total                : 0.90
% 3.82/1.65  Index Insertion      : 0.00
% 3.82/1.65  Index Deletion       : 0.00
% 3.82/1.65  Index Matching       : 0.00
% 3.82/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
