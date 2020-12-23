%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:37 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 316 expanded)
%              Number of leaves         :   34 ( 119 expanded)
%              Depth                    :    9
%              Number of atoms          :  266 ( 910 expanded)
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

tff(f_106,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1118,plain,(
    ! [C_404,B_405,A_406] :
      ( v5_relat_1(C_404,B_405)
      | ~ m1_subset_1(C_404,k1_zfmisc_1(k2_zfmisc_1(A_406,B_405))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1127,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1118])).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1073,plain,(
    ! [B_392,A_393] :
      ( v1_relat_1(B_392)
      | ~ m1_subset_1(B_392,k1_zfmisc_1(A_393))
      | ~ v1_relat_1(A_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1079,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_1073])).

tff(c_1083,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1079])).

tff(c_1178,plain,(
    ! [A_441,B_442,C_443,D_444] :
      ( k8_relset_1(A_441,B_442,C_443,D_444) = k10_relat_1(C_443,D_444)
      | ~ m1_subset_1(C_443,k1_zfmisc_1(k2_zfmisc_1(A_441,B_442))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1185,plain,(
    ! [D_444] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_444) = k10_relat_1('#skF_5',D_444) ),
    inference(resolution,[status(thm)],[c_36,c_1178])).

tff(c_774,plain,(
    ! [C_301,B_302,A_303] :
      ( v5_relat_1(C_301,B_302)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_303,B_302))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_783,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_774])).

tff(c_71,plain,(
    ! [B_124,A_125] :
      ( v1_relat_1(B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(A_125))
      | ~ v1_relat_1(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_77,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_71])).

tff(c_81,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_77])).

tff(c_830,plain,(
    ! [A_334,B_335,C_336,D_337] :
      ( k8_relset_1(A_334,B_335,C_336,D_337) = k10_relat_1(C_336,D_337)
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_334,B_335))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_837,plain,(
    ! [D_337] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_337) = k10_relat_1('#skF_5',D_337) ),
    inference(resolution,[status(thm)],[c_36,c_830])).

tff(c_121,plain,(
    ! [C_138,B_139,A_140] :
      ( v5_relat_1(C_138,B_139)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_140,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_130,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_121])).

tff(c_541,plain,(
    ! [A_254,B_255,C_256,D_257] :
      ( k8_relset_1(A_254,B_255,C_256,D_257) = k10_relat_1(C_256,D_257)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_548,plain,(
    ! [D_257] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_257) = k10_relat_1('#skF_5',D_257) ),
    inference(resolution,[status(thm)],[c_36,c_541])).

tff(c_58,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | m1_subset_1('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_120,plain,(
    m1_subset_1('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_50,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | r2_hidden('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_70,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_54,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_156,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_262,plain,(
    ! [A_184,B_185,C_186,D_187] :
      ( k8_relset_1(A_184,B_185,C_186,D_187) = k10_relat_1(C_186,D_187)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_273,plain,(
    ! [D_187] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_187) = k10_relat_1('#skF_5',D_187) ),
    inference(resolution,[status(thm)],[c_36,c_262])).

tff(c_44,plain,(
    ! [F_117] :
      ( ~ r2_hidden(F_117,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_117),'#skF_5')
      | ~ m1_subset_1(F_117,'#skF_4')
      | ~ r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_338,plain,(
    ! [F_117] :
      ( ~ r2_hidden(F_117,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_117),'#skF_5')
      | ~ m1_subset_1(F_117,'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_44])).

tff(c_339,plain,(
    ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_338])).

tff(c_24,plain,(
    ! [B_20,C_21,A_19] :
      ( r2_hidden(B_20,k2_relat_1(C_21))
      | ~ r2_hidden(k4_tarski(A_19,B_20),C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_161,plain,
    ( r2_hidden('#skF_7',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_156,c_24])).

tff(c_165,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_161])).

tff(c_379,plain,(
    ! [A_222,C_223,B_224,D_225] :
      ( r2_hidden(A_222,k10_relat_1(C_223,B_224))
      | ~ r2_hidden(D_225,B_224)
      | ~ r2_hidden(k4_tarski(A_222,D_225),C_223)
      | ~ r2_hidden(D_225,k2_relat_1(C_223))
      | ~ v1_relat_1(C_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_401,plain,(
    ! [A_226,C_227] :
      ( r2_hidden(A_226,k10_relat_1(C_227,'#skF_3'))
      | ~ r2_hidden(k4_tarski(A_226,'#skF_7'),C_227)
      | ~ r2_hidden('#skF_7',k2_relat_1(C_227))
      | ~ v1_relat_1(C_227) ) ),
    inference(resolution,[status(thm)],[c_70,c_379])).

tff(c_404,plain,
    ( r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ r2_hidden('#skF_7',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_156,c_401])).

tff(c_407,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_165,c_404])).

tff(c_409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_339,c_407])).

tff(c_500,plain,(
    ! [F_235] :
      ( ~ r2_hidden(F_235,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_235),'#skF_5')
      | ~ m1_subset_1(F_235,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_338])).

tff(c_507,plain,
    ( ~ r2_hidden('#skF_7','#skF_3')
    | ~ m1_subset_1('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_156,c_500])).

tff(c_514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_70,c_507])).

tff(c_515,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_550,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_515])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_537,plain,(
    ! [A_251,B_252,C_253] :
      ( r2_hidden('#skF_1'(A_251,B_252,C_253),k2_relat_1(C_253))
      | ~ r2_hidden(A_251,k10_relat_1(C_253,B_252))
      | ~ v1_relat_1(C_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_142,plain,(
    ! [A_144,C_145,B_146] :
      ( m1_subset_1(A_144,C_145)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(C_145))
      | ~ r2_hidden(A_144,B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_147,plain,(
    ! [A_144,B_2,A_1] :
      ( m1_subset_1(A_144,B_2)
      | ~ r2_hidden(A_144,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_142])).

tff(c_724,plain,(
    ! [A_292,B_293,C_294,B_295] :
      ( m1_subset_1('#skF_1'(A_292,B_293,C_294),B_295)
      | ~ r1_tarski(k2_relat_1(C_294),B_295)
      | ~ r2_hidden(A_292,k10_relat_1(C_294,B_293))
      | ~ v1_relat_1(C_294) ) ),
    inference(resolution,[status(thm)],[c_537,c_147])).

tff(c_728,plain,(
    ! [A_296,B_297,B_298,A_299] :
      ( m1_subset_1('#skF_1'(A_296,B_297,B_298),A_299)
      | ~ r2_hidden(A_296,k10_relat_1(B_298,B_297))
      | ~ v5_relat_1(B_298,A_299)
      | ~ v1_relat_1(B_298) ) ),
    inference(resolution,[status(thm)],[c_12,c_724])).

tff(c_733,plain,(
    ! [A_299] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_299)
      | ~ v5_relat_1('#skF_5',A_299)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_550,c_728])).

tff(c_742,plain,(
    ! [A_300] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_300)
      | ~ v5_relat_1('#skF_5',A_300) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_733])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden('#skF_1'(A_13,B_14,C_15),B_14)
      | ~ r2_hidden(A_13,k10_relat_1(C_15,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden(k4_tarski(A_13,'#skF_1'(A_13,B_14,C_15)),C_15)
      | ~ r2_hidden(A_13,k10_relat_1(C_15,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_516,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [F_117] :
      ( ~ r2_hidden(F_117,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_117),'#skF_5')
      | ~ m1_subset_1(F_117,'#skF_4')
      | r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_594,plain,(
    ! [F_266] :
      ( ~ r2_hidden(F_266,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_266),'#skF_5')
      | ~ m1_subset_1(F_266,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_516,c_52])).

tff(c_598,plain,(
    ! [B_14] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_14,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_14,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_14))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_20,c_594])).

tff(c_681,plain,(
    ! [B_279] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_279,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_279,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_279)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_598])).

tff(c_685,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_681])).

tff(c_688,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_550,c_685])).

tff(c_745,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_742,c_688])).

tff(c_771,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_745])).

tff(c_772,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_839,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_772])).

tff(c_863,plain,(
    ! [A_344,B_345,C_346] :
      ( r2_hidden('#skF_1'(A_344,B_345,C_346),k2_relat_1(C_346))
      | ~ r2_hidden(A_344,k10_relat_1(C_346,B_345))
      | ~ v1_relat_1(C_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_795,plain,(
    ! [A_307,C_308,B_309] :
      ( m1_subset_1(A_307,C_308)
      | ~ m1_subset_1(B_309,k1_zfmisc_1(C_308))
      | ~ r2_hidden(A_307,B_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_800,plain,(
    ! [A_307,B_2,A_1] :
      ( m1_subset_1(A_307,B_2)
      | ~ r2_hidden(A_307,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_795])).

tff(c_1017,plain,(
    ! [A_378,B_379,C_380,B_381] :
      ( m1_subset_1('#skF_1'(A_378,B_379,C_380),B_381)
      | ~ r1_tarski(k2_relat_1(C_380),B_381)
      | ~ r2_hidden(A_378,k10_relat_1(C_380,B_379))
      | ~ v1_relat_1(C_380) ) ),
    inference(resolution,[status(thm)],[c_863,c_800])).

tff(c_1026,plain,(
    ! [A_387,B_388,B_389,A_390] :
      ( m1_subset_1('#skF_1'(A_387,B_388,B_389),A_390)
      | ~ r2_hidden(A_387,k10_relat_1(B_389,B_388))
      | ~ v5_relat_1(B_389,A_390)
      | ~ v1_relat_1(B_389) ) ),
    inference(resolution,[status(thm)],[c_12,c_1017])).

tff(c_1031,plain,(
    ! [A_390] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_390)
      | ~ v5_relat_1('#skF_5',A_390)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_839,c_1026])).

tff(c_1040,plain,(
    ! [A_391] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_391)
      | ~ v5_relat_1('#skF_5',A_391) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1031])).

tff(c_867,plain,(
    ! [A_347,B_348,C_349] :
      ( r2_hidden(k4_tarski(A_347,'#skF_1'(A_347,B_348,C_349)),C_349)
      | ~ r2_hidden(A_347,k10_relat_1(C_349,B_348))
      | ~ v1_relat_1(C_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_773,plain,(
    ~ m1_subset_1('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,(
    ! [F_117] :
      ( ~ r2_hidden(F_117,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_117),'#skF_5')
      | ~ m1_subset_1(F_117,'#skF_4')
      | m1_subset_1('#skF_7','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_822,plain,(
    ! [F_117] :
      ( ~ r2_hidden(F_117,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_117),'#skF_5')
      | ~ m1_subset_1(F_117,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_773,c_56])).

tff(c_871,plain,(
    ! [B_348] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_348,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_348,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_348))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_867,c_822])).

tff(c_952,plain,(
    ! [B_359] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_359,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_359,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_359)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_871])).

tff(c_956,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_952])).

tff(c_959,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_839,c_956])).

tff(c_1043,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1040,c_959])).

tff(c_1069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_1043])).

tff(c_1070,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1188,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1185,c_1070])).

tff(c_1174,plain,(
    ! [A_438,B_439,C_440] :
      ( r2_hidden('#skF_1'(A_438,B_439,C_440),k2_relat_1(C_440))
      | ~ r2_hidden(A_438,k10_relat_1(C_440,B_439))
      | ~ v1_relat_1(C_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1144,plain,(
    ! [A_412,C_413,B_414] :
      ( m1_subset_1(A_412,C_413)
      | ~ m1_subset_1(B_414,k1_zfmisc_1(C_413))
      | ~ r2_hidden(A_412,B_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1149,plain,(
    ! [A_412,B_2,A_1] :
      ( m1_subset_1(A_412,B_2)
      | ~ r2_hidden(A_412,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_1144])).

tff(c_1356,plain,(
    ! [A_476,B_477,C_478,B_479] :
      ( m1_subset_1('#skF_1'(A_476,B_477,C_478),B_479)
      | ~ r1_tarski(k2_relat_1(C_478),B_479)
      | ~ r2_hidden(A_476,k10_relat_1(C_478,B_477))
      | ~ v1_relat_1(C_478) ) ),
    inference(resolution,[status(thm)],[c_1174,c_1149])).

tff(c_1360,plain,(
    ! [A_480,B_481,B_482,A_483] :
      ( m1_subset_1('#skF_1'(A_480,B_481,B_482),A_483)
      | ~ r2_hidden(A_480,k10_relat_1(B_482,B_481))
      | ~ v5_relat_1(B_482,A_483)
      | ~ v1_relat_1(B_482) ) ),
    inference(resolution,[status(thm)],[c_12,c_1356])).

tff(c_1365,plain,(
    ! [A_483] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_483)
      | ~ v5_relat_1('#skF_5',A_483)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1188,c_1360])).

tff(c_1374,plain,(
    ! [A_484] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_484)
      | ~ v5_relat_1('#skF_5',A_484) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1083,c_1365])).

tff(c_1211,plain,(
    ! [A_451,B_452,C_453] :
      ( r2_hidden(k4_tarski(A_451,'#skF_1'(A_451,B_452,C_453)),C_453)
      | ~ r2_hidden(A_451,k10_relat_1(C_453,B_452))
      | ~ v1_relat_1(C_453) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1071,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [F_117] :
      ( ~ r2_hidden(F_117,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_117),'#skF_5')
      | ~ m1_subset_1(F_117,'#skF_4')
      | r2_hidden('#skF_7','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1163,plain,(
    ! [F_117] :
      ( ~ r2_hidden(F_117,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_117),'#skF_5')
      | ~ m1_subset_1(F_117,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1071,c_48])).

tff(c_1218,plain,(
    ! [B_452] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_452,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_452,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_452))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1211,c_1163])).

tff(c_1319,plain,(
    ! [B_469] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_469,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_469,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_469)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1083,c_1218])).

tff(c_1323,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_1319])).

tff(c_1326,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1083,c_1188,c_1323])).

tff(c_1377,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1374,c_1326])).

tff(c_1403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1127,c_1377])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:36:10 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.59/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.59  
% 3.59/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.59  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.59/1.59  
% 3.59/1.59  %Foreground sorts:
% 3.59/1.59  
% 3.59/1.59  
% 3.59/1.59  %Background operators:
% 3.59/1.59  
% 3.59/1.59  
% 3.59/1.59  %Foreground operators:
% 3.59/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.59/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.59/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.59/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.59/1.59  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.59/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.59/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.59/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.59/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.59/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.59/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.59/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.59/1.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.59/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.59/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.59/1.59  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.59/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.59/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.59/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.59/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.59/1.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.59/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.59/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.59/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.59/1.59  
% 3.59/1.61  tff(f_106, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_relset_1)).
% 3.59/1.61  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.59/1.61  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.59/1.61  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.59/1.61  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.59/1.61  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 3.59/1.61  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 3.59/1.61  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.59/1.61  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.59/1.61  tff(f_35, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.59/1.61  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.59/1.61  tff(c_1118, plain, (![C_404, B_405, A_406]: (v5_relat_1(C_404, B_405) | ~m1_subset_1(C_404, k1_zfmisc_1(k2_zfmisc_1(A_406, B_405))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.59/1.61  tff(c_1127, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_1118])).
% 3.59/1.61  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.59/1.61  tff(c_1073, plain, (![B_392, A_393]: (v1_relat_1(B_392) | ~m1_subset_1(B_392, k1_zfmisc_1(A_393)) | ~v1_relat_1(A_393))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.59/1.61  tff(c_1079, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_1073])).
% 3.59/1.61  tff(c_1083, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1079])).
% 3.59/1.61  tff(c_1178, plain, (![A_441, B_442, C_443, D_444]: (k8_relset_1(A_441, B_442, C_443, D_444)=k10_relat_1(C_443, D_444) | ~m1_subset_1(C_443, k1_zfmisc_1(k2_zfmisc_1(A_441, B_442))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.59/1.61  tff(c_1185, plain, (![D_444]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_444)=k10_relat_1('#skF_5', D_444))), inference(resolution, [status(thm)], [c_36, c_1178])).
% 3.59/1.61  tff(c_774, plain, (![C_301, B_302, A_303]: (v5_relat_1(C_301, B_302) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(A_303, B_302))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.59/1.61  tff(c_783, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_774])).
% 3.59/1.61  tff(c_71, plain, (![B_124, A_125]: (v1_relat_1(B_124) | ~m1_subset_1(B_124, k1_zfmisc_1(A_125)) | ~v1_relat_1(A_125))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.59/1.61  tff(c_77, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_36, c_71])).
% 3.59/1.61  tff(c_81, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_77])).
% 3.59/1.61  tff(c_830, plain, (![A_334, B_335, C_336, D_337]: (k8_relset_1(A_334, B_335, C_336, D_337)=k10_relat_1(C_336, D_337) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_334, B_335))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.59/1.61  tff(c_837, plain, (![D_337]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_337)=k10_relat_1('#skF_5', D_337))), inference(resolution, [status(thm)], [c_36, c_830])).
% 3.59/1.61  tff(c_121, plain, (![C_138, B_139, A_140]: (v5_relat_1(C_138, B_139) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_140, B_139))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.59/1.61  tff(c_130, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_121])).
% 3.59/1.61  tff(c_541, plain, (![A_254, B_255, C_256, D_257]: (k8_relset_1(A_254, B_255, C_256, D_257)=k10_relat_1(C_256, D_257) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.59/1.61  tff(c_548, plain, (![D_257]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_257)=k10_relat_1('#skF_5', D_257))), inference(resolution, [status(thm)], [c_36, c_541])).
% 3.59/1.61  tff(c_58, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | m1_subset_1('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.59/1.61  tff(c_120, plain, (m1_subset_1('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_58])).
% 3.59/1.61  tff(c_50, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | r2_hidden('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.59/1.61  tff(c_70, plain, (r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 3.59/1.61  tff(c_54, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.59/1.61  tff(c_156, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(splitLeft, [status(thm)], [c_54])).
% 3.59/1.61  tff(c_262, plain, (![A_184, B_185, C_186, D_187]: (k8_relset_1(A_184, B_185, C_186, D_187)=k10_relat_1(C_186, D_187) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.59/1.61  tff(c_273, plain, (![D_187]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_187)=k10_relat_1('#skF_5', D_187))), inference(resolution, [status(thm)], [c_36, c_262])).
% 3.59/1.61  tff(c_44, plain, (![F_117]: (~r2_hidden(F_117, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_117), '#skF_5') | ~m1_subset_1(F_117, '#skF_4') | ~r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.59/1.61  tff(c_338, plain, (![F_117]: (~r2_hidden(F_117, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_117), '#skF_5') | ~m1_subset_1(F_117, '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_273, c_44])).
% 3.59/1.61  tff(c_339, plain, (~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_338])).
% 3.59/1.61  tff(c_24, plain, (![B_20, C_21, A_19]: (r2_hidden(B_20, k2_relat_1(C_21)) | ~r2_hidden(k4_tarski(A_19, B_20), C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.59/1.61  tff(c_161, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_156, c_24])).
% 3.59/1.61  tff(c_165, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_161])).
% 3.59/1.61  tff(c_379, plain, (![A_222, C_223, B_224, D_225]: (r2_hidden(A_222, k10_relat_1(C_223, B_224)) | ~r2_hidden(D_225, B_224) | ~r2_hidden(k4_tarski(A_222, D_225), C_223) | ~r2_hidden(D_225, k2_relat_1(C_223)) | ~v1_relat_1(C_223))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.59/1.61  tff(c_401, plain, (![A_226, C_227]: (r2_hidden(A_226, k10_relat_1(C_227, '#skF_3')) | ~r2_hidden(k4_tarski(A_226, '#skF_7'), C_227) | ~r2_hidden('#skF_7', k2_relat_1(C_227)) | ~v1_relat_1(C_227))), inference(resolution, [status(thm)], [c_70, c_379])).
% 3.59/1.61  tff(c_404, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~r2_hidden('#skF_7', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_156, c_401])).
% 3.59/1.61  tff(c_407, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_165, c_404])).
% 3.59/1.61  tff(c_409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_339, c_407])).
% 3.59/1.61  tff(c_500, plain, (![F_235]: (~r2_hidden(F_235, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_235), '#skF_5') | ~m1_subset_1(F_235, '#skF_4'))), inference(splitRight, [status(thm)], [c_338])).
% 3.59/1.61  tff(c_507, plain, (~r2_hidden('#skF_7', '#skF_3') | ~m1_subset_1('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_156, c_500])).
% 3.59/1.61  tff(c_514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_70, c_507])).
% 3.59/1.61  tff(c_515, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_54])).
% 3.59/1.61  tff(c_550, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_548, c_515])).
% 3.59/1.61  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.59/1.61  tff(c_537, plain, (![A_251, B_252, C_253]: (r2_hidden('#skF_1'(A_251, B_252, C_253), k2_relat_1(C_253)) | ~r2_hidden(A_251, k10_relat_1(C_253, B_252)) | ~v1_relat_1(C_253))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.59/1.61  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.59/1.61  tff(c_142, plain, (![A_144, C_145, B_146]: (m1_subset_1(A_144, C_145) | ~m1_subset_1(B_146, k1_zfmisc_1(C_145)) | ~r2_hidden(A_144, B_146))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.59/1.61  tff(c_147, plain, (![A_144, B_2, A_1]: (m1_subset_1(A_144, B_2) | ~r2_hidden(A_144, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_142])).
% 3.59/1.61  tff(c_724, plain, (![A_292, B_293, C_294, B_295]: (m1_subset_1('#skF_1'(A_292, B_293, C_294), B_295) | ~r1_tarski(k2_relat_1(C_294), B_295) | ~r2_hidden(A_292, k10_relat_1(C_294, B_293)) | ~v1_relat_1(C_294))), inference(resolution, [status(thm)], [c_537, c_147])).
% 3.59/1.61  tff(c_728, plain, (![A_296, B_297, B_298, A_299]: (m1_subset_1('#skF_1'(A_296, B_297, B_298), A_299) | ~r2_hidden(A_296, k10_relat_1(B_298, B_297)) | ~v5_relat_1(B_298, A_299) | ~v1_relat_1(B_298))), inference(resolution, [status(thm)], [c_12, c_724])).
% 3.59/1.61  tff(c_733, plain, (![A_299]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_299) | ~v5_relat_1('#skF_5', A_299) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_550, c_728])).
% 3.59/1.61  tff(c_742, plain, (![A_300]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_300) | ~v5_relat_1('#skF_5', A_300))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_733])).
% 3.59/1.61  tff(c_18, plain, (![A_13, B_14, C_15]: (r2_hidden('#skF_1'(A_13, B_14, C_15), B_14) | ~r2_hidden(A_13, k10_relat_1(C_15, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.59/1.61  tff(c_20, plain, (![A_13, B_14, C_15]: (r2_hidden(k4_tarski(A_13, '#skF_1'(A_13, B_14, C_15)), C_15) | ~r2_hidden(A_13, k10_relat_1(C_15, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.59/1.61  tff(c_516, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_54])).
% 3.59/1.61  tff(c_52, plain, (![F_117]: (~r2_hidden(F_117, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_117), '#skF_5') | ~m1_subset_1(F_117, '#skF_4') | r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.59/1.61  tff(c_594, plain, (![F_266]: (~r2_hidden(F_266, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_266), '#skF_5') | ~m1_subset_1(F_266, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_516, c_52])).
% 3.59/1.61  tff(c_598, plain, (![B_14]: (~r2_hidden('#skF_1'('#skF_6', B_14, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_14, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_14)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_20, c_594])).
% 3.59/1.61  tff(c_681, plain, (![B_279]: (~r2_hidden('#skF_1'('#skF_6', B_279, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_279, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_279)))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_598])).
% 3.59/1.61  tff(c_685, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_681])).
% 3.59/1.61  tff(c_688, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_550, c_685])).
% 3.59/1.61  tff(c_745, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_742, c_688])).
% 3.59/1.61  tff(c_771, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_745])).
% 3.59/1.61  tff(c_772, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_58])).
% 3.59/1.61  tff(c_839, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_837, c_772])).
% 3.59/1.61  tff(c_863, plain, (![A_344, B_345, C_346]: (r2_hidden('#skF_1'(A_344, B_345, C_346), k2_relat_1(C_346)) | ~r2_hidden(A_344, k10_relat_1(C_346, B_345)) | ~v1_relat_1(C_346))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.59/1.61  tff(c_795, plain, (![A_307, C_308, B_309]: (m1_subset_1(A_307, C_308) | ~m1_subset_1(B_309, k1_zfmisc_1(C_308)) | ~r2_hidden(A_307, B_309))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.59/1.61  tff(c_800, plain, (![A_307, B_2, A_1]: (m1_subset_1(A_307, B_2) | ~r2_hidden(A_307, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_795])).
% 3.59/1.61  tff(c_1017, plain, (![A_378, B_379, C_380, B_381]: (m1_subset_1('#skF_1'(A_378, B_379, C_380), B_381) | ~r1_tarski(k2_relat_1(C_380), B_381) | ~r2_hidden(A_378, k10_relat_1(C_380, B_379)) | ~v1_relat_1(C_380))), inference(resolution, [status(thm)], [c_863, c_800])).
% 3.59/1.61  tff(c_1026, plain, (![A_387, B_388, B_389, A_390]: (m1_subset_1('#skF_1'(A_387, B_388, B_389), A_390) | ~r2_hidden(A_387, k10_relat_1(B_389, B_388)) | ~v5_relat_1(B_389, A_390) | ~v1_relat_1(B_389))), inference(resolution, [status(thm)], [c_12, c_1017])).
% 3.59/1.61  tff(c_1031, plain, (![A_390]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_390) | ~v5_relat_1('#skF_5', A_390) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_839, c_1026])).
% 3.59/1.61  tff(c_1040, plain, (![A_391]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_391) | ~v5_relat_1('#skF_5', A_391))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1031])).
% 3.59/1.61  tff(c_867, plain, (![A_347, B_348, C_349]: (r2_hidden(k4_tarski(A_347, '#skF_1'(A_347, B_348, C_349)), C_349) | ~r2_hidden(A_347, k10_relat_1(C_349, B_348)) | ~v1_relat_1(C_349))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.59/1.62  tff(c_773, plain, (~m1_subset_1('#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 3.59/1.62  tff(c_56, plain, (![F_117]: (~r2_hidden(F_117, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_117), '#skF_5') | ~m1_subset_1(F_117, '#skF_4') | m1_subset_1('#skF_7', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.59/1.62  tff(c_822, plain, (![F_117]: (~r2_hidden(F_117, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_117), '#skF_5') | ~m1_subset_1(F_117, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_773, c_56])).
% 3.59/1.62  tff(c_871, plain, (![B_348]: (~r2_hidden('#skF_1'('#skF_6', B_348, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_348, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_348)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_867, c_822])).
% 3.59/1.62  tff(c_952, plain, (![B_359]: (~r2_hidden('#skF_1'('#skF_6', B_359, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_359, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_359)))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_871])).
% 3.59/1.62  tff(c_956, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_952])).
% 3.59/1.62  tff(c_959, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_839, c_956])).
% 3.59/1.62  tff(c_1043, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1040, c_959])).
% 3.59/1.62  tff(c_1069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_783, c_1043])).
% 3.59/1.62  tff(c_1070, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_50])).
% 3.59/1.62  tff(c_1188, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1185, c_1070])).
% 3.59/1.62  tff(c_1174, plain, (![A_438, B_439, C_440]: (r2_hidden('#skF_1'(A_438, B_439, C_440), k2_relat_1(C_440)) | ~r2_hidden(A_438, k10_relat_1(C_440, B_439)) | ~v1_relat_1(C_440))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.59/1.62  tff(c_1144, plain, (![A_412, C_413, B_414]: (m1_subset_1(A_412, C_413) | ~m1_subset_1(B_414, k1_zfmisc_1(C_413)) | ~r2_hidden(A_412, B_414))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.59/1.62  tff(c_1149, plain, (![A_412, B_2, A_1]: (m1_subset_1(A_412, B_2) | ~r2_hidden(A_412, A_1) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_1144])).
% 3.59/1.62  tff(c_1356, plain, (![A_476, B_477, C_478, B_479]: (m1_subset_1('#skF_1'(A_476, B_477, C_478), B_479) | ~r1_tarski(k2_relat_1(C_478), B_479) | ~r2_hidden(A_476, k10_relat_1(C_478, B_477)) | ~v1_relat_1(C_478))), inference(resolution, [status(thm)], [c_1174, c_1149])).
% 3.59/1.62  tff(c_1360, plain, (![A_480, B_481, B_482, A_483]: (m1_subset_1('#skF_1'(A_480, B_481, B_482), A_483) | ~r2_hidden(A_480, k10_relat_1(B_482, B_481)) | ~v5_relat_1(B_482, A_483) | ~v1_relat_1(B_482))), inference(resolution, [status(thm)], [c_12, c_1356])).
% 3.59/1.62  tff(c_1365, plain, (![A_483]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_483) | ~v5_relat_1('#skF_5', A_483) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1188, c_1360])).
% 3.59/1.62  tff(c_1374, plain, (![A_484]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_484) | ~v5_relat_1('#skF_5', A_484))), inference(demodulation, [status(thm), theory('equality')], [c_1083, c_1365])).
% 3.59/1.62  tff(c_1211, plain, (![A_451, B_452, C_453]: (r2_hidden(k4_tarski(A_451, '#skF_1'(A_451, B_452, C_453)), C_453) | ~r2_hidden(A_451, k10_relat_1(C_453, B_452)) | ~v1_relat_1(C_453))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.59/1.62  tff(c_1071, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 3.59/1.62  tff(c_48, plain, (![F_117]: (~r2_hidden(F_117, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_117), '#skF_5') | ~m1_subset_1(F_117, '#skF_4') | r2_hidden('#skF_7', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.59/1.62  tff(c_1163, plain, (![F_117]: (~r2_hidden(F_117, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_117), '#skF_5') | ~m1_subset_1(F_117, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1071, c_48])).
% 3.59/1.62  tff(c_1218, plain, (![B_452]: (~r2_hidden('#skF_1'('#skF_6', B_452, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_452, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_452)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1211, c_1163])).
% 3.59/1.62  tff(c_1319, plain, (![B_469]: (~r2_hidden('#skF_1'('#skF_6', B_469, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_469, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_469)))), inference(demodulation, [status(thm), theory('equality')], [c_1083, c_1218])).
% 3.59/1.62  tff(c_1323, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_1319])).
% 3.59/1.62  tff(c_1326, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1083, c_1188, c_1323])).
% 3.59/1.62  tff(c_1377, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1374, c_1326])).
% 3.59/1.62  tff(c_1403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1127, c_1377])).
% 3.59/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.62  
% 3.59/1.62  Inference rules
% 3.59/1.62  ----------------------
% 3.59/1.62  #Ref     : 0
% 3.59/1.62  #Sup     : 274
% 3.59/1.62  #Fact    : 0
% 3.59/1.62  #Define  : 0
% 3.59/1.62  #Split   : 13
% 3.59/1.62  #Chain   : 0
% 3.59/1.62  #Close   : 0
% 3.59/1.62  
% 3.59/1.62  Ordering : KBO
% 3.59/1.62  
% 3.59/1.62  Simplification rules
% 3.59/1.62  ----------------------
% 3.59/1.62  #Subsume      : 27
% 3.59/1.62  #Demod        : 74
% 3.59/1.62  #Tautology    : 33
% 3.59/1.62  #SimpNegUnit  : 4
% 3.59/1.62  #BackRed      : 6
% 3.59/1.62  
% 3.59/1.62  #Partial instantiations: 0
% 3.59/1.62  #Strategies tried      : 1
% 3.59/1.62  
% 3.59/1.62  Timing (in seconds)
% 3.59/1.62  ----------------------
% 3.59/1.62  Preprocessing        : 0.33
% 3.59/1.62  Parsing              : 0.17
% 3.59/1.62  CNF conversion       : 0.03
% 3.59/1.62  Main loop            : 0.50
% 3.59/1.62  Inferencing          : 0.20
% 3.59/1.62  Reduction            : 0.14
% 3.59/1.62  Demodulation         : 0.09
% 3.59/1.62  BG Simplification    : 0.02
% 3.59/1.62  Subsumption          : 0.09
% 3.59/1.62  Abstraction          : 0.02
% 3.59/1.62  MUC search           : 0.00
% 3.59/1.62  Cooper               : 0.00
% 3.59/1.62  Total                : 0.89
% 3.59/1.62  Index Insertion      : 0.00
% 3.59/1.62  Index Deletion       : 0.00
% 3.59/1.62  Index Matching       : 0.00
% 3.59/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
