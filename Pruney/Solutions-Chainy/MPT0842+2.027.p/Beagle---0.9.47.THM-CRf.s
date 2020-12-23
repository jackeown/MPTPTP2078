%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:39 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 311 expanded)
%              Number of leaves         :   31 ( 117 expanded)
%              Depth                    :    9
%              Number of atoms          :  230 ( 898 expanded)
%              Number of equality atoms :   16 (  33 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_98,negated_conjecture,(
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

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_6,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_52,plain,(
    ! [B_119,A_120] :
      ( v1_relat_1(B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_120))
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_55,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_28,c_52])).

tff(c_58,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_55])).

tff(c_685,plain,(
    ! [A_271,B_272,C_273,D_274] :
      ( k8_relset_1(A_271,B_272,C_273,D_274) = k10_relat_1(C_273,D_274)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(A_271,B_272))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_692,plain,(
    ! [D_274] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_274) = k10_relat_1('#skF_5',D_274) ),
    inference(resolution,[status(thm)],[c_28,c_685])).

tff(c_509,plain,(
    ! [A_226,B_227,C_228,D_229] :
      ( k8_relset_1(A_226,B_227,C_228,D_229) = k10_relat_1(C_228,D_229)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_516,plain,(
    ! [D_229] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_229) = k10_relat_1('#skF_5',D_229) ),
    inference(resolution,[status(thm)],[c_28,c_509])).

tff(c_350,plain,(
    ! [A_188,B_189,C_190,D_191] :
      ( k8_relset_1(A_188,B_189,C_190,D_191) = k10_relat_1(C_190,D_191)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_357,plain,(
    ! [D_191] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_191) = k10_relat_1('#skF_5',D_191) ),
    inference(resolution,[status(thm)],[c_28,c_350])).

tff(c_50,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | m1_subset_1('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_65,plain,(
    m1_subset_1('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_42,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | r2_hidden('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_63,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_46,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_77,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_155,plain,(
    ! [A_149,B_150,C_151,D_152] :
      ( k8_relset_1(A_149,B_150,C_151,D_152) = k10_relat_1(C_151,D_152)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_162,plain,(
    ! [D_152] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_152) = k10_relat_1('#skF_5',D_152) ),
    inference(resolution,[status(thm)],[c_28,c_155])).

tff(c_36,plain,(
    ! [F_116] :
      ( ~ r2_hidden(F_116,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_116),'#skF_5')
      | ~ m1_subset_1(F_116,'#skF_4')
      | ~ r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_227,plain,(
    ! [F_116] :
      ( ~ r2_hidden(F_116,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_116),'#skF_5')
      | ~ m1_subset_1(F_116,'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_36])).

tff(c_228,plain,(
    ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_16,plain,(
    ! [B_16,C_17,A_15] :
      ( r2_hidden(B_16,k2_relat_1(C_17))
      | ~ r2_hidden(k4_tarski(A_15,B_16),C_17)
      | ~ v1_relat_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_81,plain,
    ( r2_hidden('#skF_7',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_77,c_16])).

tff(c_87,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_81])).

tff(c_230,plain,(
    ! [A_166,C_167,B_168,D_169] :
      ( r2_hidden(A_166,k10_relat_1(C_167,B_168))
      | ~ r2_hidden(D_169,B_168)
      | ~ r2_hidden(k4_tarski(A_166,D_169),C_167)
      | ~ r2_hidden(D_169,k2_relat_1(C_167))
      | ~ v1_relat_1(C_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_252,plain,(
    ! [A_170,C_171] :
      ( r2_hidden(A_170,k10_relat_1(C_171,'#skF_3'))
      | ~ r2_hidden(k4_tarski(A_170,'#skF_7'),C_171)
      | ~ r2_hidden('#skF_7',k2_relat_1(C_171))
      | ~ v1_relat_1(C_171) ) ),
    inference(resolution,[status(thm)],[c_63,c_230])).

tff(c_255,plain,
    ( r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ r2_hidden('#skF_7',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_77,c_252])).

tff(c_258,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_87,c_255])).

tff(c_260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_228,c_258])).

tff(c_273,plain,(
    ! [F_172] :
      ( ~ r2_hidden(F_172,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_172),'#skF_5')
      | ~ m1_subset_1(F_172,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_280,plain,
    ( ~ r2_hidden('#skF_7','#skF_3')
    | ~ m1_subset_1('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_77,c_273])).

tff(c_287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_63,c_280])).

tff(c_288,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_358,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_288])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden('#skF_1'(A_9,B_10,C_11),k2_relat_1(C_11))
      | ~ r2_hidden(A_9,k10_relat_1(C_11,B_10))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_68,plain,(
    ! [A_131,B_132,C_133] :
      ( k2_relset_1(A_131,B_132,C_133) = k2_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_72,plain,(
    k2_relset_1('#skF_2','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_68])).

tff(c_292,plain,(
    ! [A_176,B_177,C_178] :
      ( m1_subset_1(k2_relset_1(A_176,B_177,C_178),k1_zfmisc_1(B_177))
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_304,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_292])).

tff(c_309,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_304])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_319,plain,(
    ! [A_182] :
      ( m1_subset_1(A_182,'#skF_4')
      | ~ r2_hidden(A_182,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_309,c_2])).

tff(c_323,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1('#skF_1'(A_9,B_10,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_9,k10_relat_1('#skF_5',B_10))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14,c_319])).

tff(c_330,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1('#skF_1'(A_9,B_10,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_9,k10_relat_1('#skF_5',B_10)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_323])).

tff(c_371,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_358,c_330])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden('#skF_1'(A_9,B_10,C_11),B_10)
      | ~ r2_hidden(A_9,k10_relat_1(C_11,B_10))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden(k4_tarski(A_9,'#skF_1'(A_9,B_10,C_11)),C_11)
      | ~ r2_hidden(A_9,k10_relat_1(C_11,B_10))
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_289,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,(
    ! [F_116] :
      ( ~ r2_hidden(F_116,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_116),'#skF_5')
      | ~ m1_subset_1(F_116,'#skF_4')
      | r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_409,plain,(
    ! [F_199] :
      ( ~ r2_hidden(F_199,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_199),'#skF_5')
      | ~ m1_subset_1(F_199,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_44])).

tff(c_413,plain,(
    ! [B_10] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_10,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_10,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_10))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_409])).

tff(c_441,plain,(
    ! [B_206] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_206,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_206,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_206)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_413])).

tff(c_445,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_441])).

tff(c_449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_358,c_371,c_445])).

tff(c_450,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_519,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_450])).

tff(c_529,plain,(
    ! [A_232,B_233,C_234] :
      ( r2_hidden('#skF_1'(A_232,B_233,C_234),k2_relat_1(C_234))
      | ~ r2_hidden(A_232,k10_relat_1(C_234,B_233))
      | ~ v1_relat_1(C_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_454,plain,(
    ! [A_213,B_214,C_215] :
      ( k2_relset_1(A_213,B_214,C_215) = k2_relat_1(C_215)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_458,plain,(
    k2_relset_1('#skF_2','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_454])).

tff(c_464,plain,(
    ! [A_216,B_217,C_218] :
      ( m1_subset_1(k2_relset_1(A_216,B_217,C_218),k1_zfmisc_1(B_217))
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_216,B_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_476,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_464])).

tff(c_481,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_476])).

tff(c_487,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_4')
      | ~ r2_hidden(A_1,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_481,c_2])).

tff(c_533,plain,(
    ! [A_232,B_233] :
      ( m1_subset_1('#skF_1'(A_232,B_233,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_232,k10_relat_1('#skF_5',B_233))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_529,c_487])).

tff(c_537,plain,(
    ! [A_235,B_236] :
      ( m1_subset_1('#skF_1'(A_235,B_236,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_235,k10_relat_1('#skF_5',B_236)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_533])).

tff(c_545,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_519,c_537])).

tff(c_547,plain,(
    ! [A_237,B_238,C_239] :
      ( r2_hidden(k4_tarski(A_237,'#skF_1'(A_237,B_238,C_239)),C_239)
      | ~ r2_hidden(A_237,k10_relat_1(C_239,B_238))
      | ~ v1_relat_1(C_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_451,plain,(
    ~ m1_subset_1('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [F_116] :
      ( ~ r2_hidden(F_116,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_116),'#skF_5')
      | ~ m1_subset_1(F_116,'#skF_4')
      | m1_subset_1('#skF_7','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_517,plain,(
    ! [F_116] :
      ( ~ r2_hidden(F_116,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_116),'#skF_5')
      | ~ m1_subset_1(F_116,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_451,c_48])).

tff(c_555,plain,(
    ! [B_238] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_238,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_238,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_238))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_547,c_517])).

tff(c_614,plain,(
    ! [B_249] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_249,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_249,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_249)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_555])).

tff(c_618,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_614])).

tff(c_622,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_519,c_545,c_618])).

tff(c_623,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_693,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_623])).

tff(c_703,plain,(
    ! [A_276,B_277,C_278] :
      ( r2_hidden('#skF_1'(A_276,B_277,C_278),k2_relat_1(C_278))
      | ~ r2_hidden(A_276,k10_relat_1(C_278,B_277))
      | ~ v1_relat_1(C_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_632,plain,(
    ! [A_258,B_259,C_260] :
      ( k2_relset_1(A_258,B_259,C_260) = k2_relat_1(C_260)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_636,plain,(
    k2_relset_1('#skF_2','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_632])).

tff(c_641,plain,(
    ! [A_261,B_262,C_263] :
      ( m1_subset_1(k2_relset_1(A_261,B_262,C_263),k1_zfmisc_1(B_262))
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_261,B_262))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_653,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_636,c_641])).

tff(c_658,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_653])).

tff(c_664,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_4')
      | ~ r2_hidden(A_1,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_658,c_2])).

tff(c_707,plain,(
    ! [A_276,B_277] :
      ( m1_subset_1('#skF_1'(A_276,B_277,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_276,k10_relat_1('#skF_5',B_277))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_703,c_664])).

tff(c_711,plain,(
    ! [A_279,B_280] :
      ( m1_subset_1('#skF_1'(A_279,B_280,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_279,k10_relat_1('#skF_5',B_280)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_707])).

tff(c_719,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_693,c_711])).

tff(c_721,plain,(
    ! [A_281,B_282,C_283] :
      ( r2_hidden(k4_tarski(A_281,'#skF_1'(A_281,B_282,C_283)),C_283)
      | ~ r2_hidden(A_281,k10_relat_1(C_283,B_282))
      | ~ v1_relat_1(C_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_624,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,(
    ! [F_116] :
      ( ~ r2_hidden(F_116,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_116),'#skF_5')
      | ~ m1_subset_1(F_116,'#skF_4')
      | r2_hidden('#skF_7','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_630,plain,(
    ! [F_116] :
      ( ~ r2_hidden(F_116,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_116),'#skF_5')
      | ~ m1_subset_1(F_116,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_624,c_40])).

tff(c_733,plain,(
    ! [B_282] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_282,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_282,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_282))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_721,c_630])).

tff(c_788,plain,(
    ! [B_293] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_293,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_293,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_293)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_733])).

tff(c_792,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_788])).

tff(c_796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_693,c_719,c_792])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.62  
% 2.70/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.62  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.70/1.62  
% 2.70/1.62  %Foreground sorts:
% 2.70/1.62  
% 2.70/1.62  
% 2.70/1.62  %Background operators:
% 2.70/1.62  
% 2.70/1.62  
% 2.70/1.62  %Foreground operators:
% 2.70/1.62  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.70/1.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.70/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.70/1.62  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.70/1.62  tff('#skF_7', type, '#skF_7': $i).
% 2.70/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.70/1.62  tff('#skF_5', type, '#skF_5': $i).
% 2.70/1.62  tff('#skF_6', type, '#skF_6': $i).
% 2.70/1.62  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.62  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.70/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.62  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.70/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.70/1.62  tff('#skF_4', type, '#skF_4': $i).
% 2.70/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.70/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.70/1.62  
% 3.03/1.64  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.03/1.64  tff(f_98, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_relset_1)).
% 3.03/1.64  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.03/1.64  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.03/1.64  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 3.03/1.64  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 3.03/1.64  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.03/1.64  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.03/1.64  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.03/1.64  tff(c_6, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.03/1.64  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.03/1.64  tff(c_52, plain, (![B_119, A_120]: (v1_relat_1(B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(A_120)) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.03/1.64  tff(c_55, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_52])).
% 3.03/1.64  tff(c_58, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_55])).
% 3.03/1.64  tff(c_685, plain, (![A_271, B_272, C_273, D_274]: (k8_relset_1(A_271, B_272, C_273, D_274)=k10_relat_1(C_273, D_274) | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.03/1.64  tff(c_692, plain, (![D_274]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_274)=k10_relat_1('#skF_5', D_274))), inference(resolution, [status(thm)], [c_28, c_685])).
% 3.03/1.64  tff(c_509, plain, (![A_226, B_227, C_228, D_229]: (k8_relset_1(A_226, B_227, C_228, D_229)=k10_relat_1(C_228, D_229) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.03/1.64  tff(c_516, plain, (![D_229]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_229)=k10_relat_1('#skF_5', D_229))), inference(resolution, [status(thm)], [c_28, c_509])).
% 3.03/1.64  tff(c_350, plain, (![A_188, B_189, C_190, D_191]: (k8_relset_1(A_188, B_189, C_190, D_191)=k10_relat_1(C_190, D_191) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.03/1.64  tff(c_357, plain, (![D_191]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_191)=k10_relat_1('#skF_5', D_191))), inference(resolution, [status(thm)], [c_28, c_350])).
% 3.03/1.64  tff(c_50, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | m1_subset_1('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.03/1.64  tff(c_65, plain, (m1_subset_1('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 3.03/1.64  tff(c_42, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | r2_hidden('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.03/1.64  tff(c_63, plain, (r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_42])).
% 3.03/1.64  tff(c_46, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.03/1.64  tff(c_77, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(splitLeft, [status(thm)], [c_46])).
% 3.03/1.64  tff(c_155, plain, (![A_149, B_150, C_151, D_152]: (k8_relset_1(A_149, B_150, C_151, D_152)=k10_relat_1(C_151, D_152) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.03/1.64  tff(c_162, plain, (![D_152]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_152)=k10_relat_1('#skF_5', D_152))), inference(resolution, [status(thm)], [c_28, c_155])).
% 3.03/1.64  tff(c_36, plain, (![F_116]: (~r2_hidden(F_116, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_116), '#skF_5') | ~m1_subset_1(F_116, '#skF_4') | ~r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.03/1.64  tff(c_227, plain, (![F_116]: (~r2_hidden(F_116, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_116), '#skF_5') | ~m1_subset_1(F_116, '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_36])).
% 3.03/1.64  tff(c_228, plain, (~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_227])).
% 3.03/1.64  tff(c_16, plain, (![B_16, C_17, A_15]: (r2_hidden(B_16, k2_relat_1(C_17)) | ~r2_hidden(k4_tarski(A_15, B_16), C_17) | ~v1_relat_1(C_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.03/1.64  tff(c_81, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_77, c_16])).
% 3.03/1.64  tff(c_87, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_81])).
% 3.03/1.64  tff(c_230, plain, (![A_166, C_167, B_168, D_169]: (r2_hidden(A_166, k10_relat_1(C_167, B_168)) | ~r2_hidden(D_169, B_168) | ~r2_hidden(k4_tarski(A_166, D_169), C_167) | ~r2_hidden(D_169, k2_relat_1(C_167)) | ~v1_relat_1(C_167))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.03/1.64  tff(c_252, plain, (![A_170, C_171]: (r2_hidden(A_170, k10_relat_1(C_171, '#skF_3')) | ~r2_hidden(k4_tarski(A_170, '#skF_7'), C_171) | ~r2_hidden('#skF_7', k2_relat_1(C_171)) | ~v1_relat_1(C_171))), inference(resolution, [status(thm)], [c_63, c_230])).
% 3.03/1.64  tff(c_255, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~r2_hidden('#skF_7', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_77, c_252])).
% 3.03/1.64  tff(c_258, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_87, c_255])).
% 3.03/1.64  tff(c_260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_228, c_258])).
% 3.03/1.64  tff(c_273, plain, (![F_172]: (~r2_hidden(F_172, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_172), '#skF_5') | ~m1_subset_1(F_172, '#skF_4'))), inference(splitRight, [status(thm)], [c_227])).
% 3.03/1.64  tff(c_280, plain, (~r2_hidden('#skF_7', '#skF_3') | ~m1_subset_1('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_77, c_273])).
% 3.03/1.64  tff(c_287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_63, c_280])).
% 3.03/1.64  tff(c_288, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_46])).
% 3.03/1.64  tff(c_358, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_357, c_288])).
% 3.03/1.64  tff(c_14, plain, (![A_9, B_10, C_11]: (r2_hidden('#skF_1'(A_9, B_10, C_11), k2_relat_1(C_11)) | ~r2_hidden(A_9, k10_relat_1(C_11, B_10)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.03/1.64  tff(c_68, plain, (![A_131, B_132, C_133]: (k2_relset_1(A_131, B_132, C_133)=k2_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.03/1.64  tff(c_72, plain, (k2_relset_1('#skF_2', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_68])).
% 3.03/1.64  tff(c_292, plain, (![A_176, B_177, C_178]: (m1_subset_1(k2_relset_1(A_176, B_177, C_178), k1_zfmisc_1(B_177)) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.03/1.64  tff(c_304, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_72, c_292])).
% 3.03/1.64  tff(c_309, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_304])).
% 3.03/1.64  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.03/1.64  tff(c_319, plain, (![A_182]: (m1_subset_1(A_182, '#skF_4') | ~r2_hidden(A_182, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_309, c_2])).
% 3.03/1.64  tff(c_323, plain, (![A_9, B_10]: (m1_subset_1('#skF_1'(A_9, B_10, '#skF_5'), '#skF_4') | ~r2_hidden(A_9, k10_relat_1('#skF_5', B_10)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_14, c_319])).
% 3.03/1.64  tff(c_330, plain, (![A_9, B_10]: (m1_subset_1('#skF_1'(A_9, B_10, '#skF_5'), '#skF_4') | ~r2_hidden(A_9, k10_relat_1('#skF_5', B_10)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_323])).
% 3.03/1.64  tff(c_371, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_358, c_330])).
% 3.03/1.64  tff(c_10, plain, (![A_9, B_10, C_11]: (r2_hidden('#skF_1'(A_9, B_10, C_11), B_10) | ~r2_hidden(A_9, k10_relat_1(C_11, B_10)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.03/1.64  tff(c_12, plain, (![A_9, B_10, C_11]: (r2_hidden(k4_tarski(A_9, '#skF_1'(A_9, B_10, C_11)), C_11) | ~r2_hidden(A_9, k10_relat_1(C_11, B_10)) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.03/1.64  tff(c_289, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 3.03/1.64  tff(c_44, plain, (![F_116]: (~r2_hidden(F_116, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_116), '#skF_5') | ~m1_subset_1(F_116, '#skF_4') | r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.03/1.64  tff(c_409, plain, (![F_199]: (~r2_hidden(F_199, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_199), '#skF_5') | ~m1_subset_1(F_199, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_289, c_44])).
% 3.03/1.64  tff(c_413, plain, (![B_10]: (~r2_hidden('#skF_1'('#skF_6', B_10, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_10, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_10)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_409])).
% 3.03/1.64  tff(c_441, plain, (![B_206]: (~r2_hidden('#skF_1'('#skF_6', B_206, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_206, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_206)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_413])).
% 3.03/1.64  tff(c_445, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_441])).
% 3.03/1.64  tff(c_449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_358, c_371, c_445])).
% 3.03/1.64  tff(c_450, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_50])).
% 3.03/1.64  tff(c_519, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_516, c_450])).
% 3.03/1.64  tff(c_529, plain, (![A_232, B_233, C_234]: (r2_hidden('#skF_1'(A_232, B_233, C_234), k2_relat_1(C_234)) | ~r2_hidden(A_232, k10_relat_1(C_234, B_233)) | ~v1_relat_1(C_234))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.03/1.64  tff(c_454, plain, (![A_213, B_214, C_215]: (k2_relset_1(A_213, B_214, C_215)=k2_relat_1(C_215) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.03/1.64  tff(c_458, plain, (k2_relset_1('#skF_2', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_454])).
% 3.03/1.64  tff(c_464, plain, (![A_216, B_217, C_218]: (m1_subset_1(k2_relset_1(A_216, B_217, C_218), k1_zfmisc_1(B_217)) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_216, B_217))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.03/1.64  tff(c_476, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_458, c_464])).
% 3.03/1.64  tff(c_481, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_476])).
% 3.03/1.64  tff(c_487, plain, (![A_1]: (m1_subset_1(A_1, '#skF_4') | ~r2_hidden(A_1, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_481, c_2])).
% 3.03/1.64  tff(c_533, plain, (![A_232, B_233]: (m1_subset_1('#skF_1'(A_232, B_233, '#skF_5'), '#skF_4') | ~r2_hidden(A_232, k10_relat_1('#skF_5', B_233)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_529, c_487])).
% 3.03/1.64  tff(c_537, plain, (![A_235, B_236]: (m1_subset_1('#skF_1'(A_235, B_236, '#skF_5'), '#skF_4') | ~r2_hidden(A_235, k10_relat_1('#skF_5', B_236)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_533])).
% 3.03/1.64  tff(c_545, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_519, c_537])).
% 3.03/1.64  tff(c_547, plain, (![A_237, B_238, C_239]: (r2_hidden(k4_tarski(A_237, '#skF_1'(A_237, B_238, C_239)), C_239) | ~r2_hidden(A_237, k10_relat_1(C_239, B_238)) | ~v1_relat_1(C_239))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.03/1.64  tff(c_451, plain, (~m1_subset_1('#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 3.03/1.64  tff(c_48, plain, (![F_116]: (~r2_hidden(F_116, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_116), '#skF_5') | ~m1_subset_1(F_116, '#skF_4') | m1_subset_1('#skF_7', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.03/1.64  tff(c_517, plain, (![F_116]: (~r2_hidden(F_116, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_116), '#skF_5') | ~m1_subset_1(F_116, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_451, c_48])).
% 3.03/1.64  tff(c_555, plain, (![B_238]: (~r2_hidden('#skF_1'('#skF_6', B_238, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_238, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_238)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_547, c_517])).
% 3.03/1.64  tff(c_614, plain, (![B_249]: (~r2_hidden('#skF_1'('#skF_6', B_249, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_249, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_249)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_555])).
% 3.03/1.64  tff(c_618, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_614])).
% 3.03/1.64  tff(c_622, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_519, c_545, c_618])).
% 3.03/1.64  tff(c_623, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_42])).
% 3.03/1.64  tff(c_693, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_692, c_623])).
% 3.03/1.64  tff(c_703, plain, (![A_276, B_277, C_278]: (r2_hidden('#skF_1'(A_276, B_277, C_278), k2_relat_1(C_278)) | ~r2_hidden(A_276, k10_relat_1(C_278, B_277)) | ~v1_relat_1(C_278))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.03/1.64  tff(c_632, plain, (![A_258, B_259, C_260]: (k2_relset_1(A_258, B_259, C_260)=k2_relat_1(C_260) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.03/1.64  tff(c_636, plain, (k2_relset_1('#skF_2', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_632])).
% 3.03/1.64  tff(c_641, plain, (![A_261, B_262, C_263]: (m1_subset_1(k2_relset_1(A_261, B_262, C_263), k1_zfmisc_1(B_262)) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_261, B_262))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.03/1.64  tff(c_653, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_636, c_641])).
% 3.03/1.64  tff(c_658, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_653])).
% 3.03/1.64  tff(c_664, plain, (![A_1]: (m1_subset_1(A_1, '#skF_4') | ~r2_hidden(A_1, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_658, c_2])).
% 3.03/1.64  tff(c_707, plain, (![A_276, B_277]: (m1_subset_1('#skF_1'(A_276, B_277, '#skF_5'), '#skF_4') | ~r2_hidden(A_276, k10_relat_1('#skF_5', B_277)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_703, c_664])).
% 3.03/1.64  tff(c_711, plain, (![A_279, B_280]: (m1_subset_1('#skF_1'(A_279, B_280, '#skF_5'), '#skF_4') | ~r2_hidden(A_279, k10_relat_1('#skF_5', B_280)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_707])).
% 3.03/1.64  tff(c_719, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_693, c_711])).
% 3.03/1.64  tff(c_721, plain, (![A_281, B_282, C_283]: (r2_hidden(k4_tarski(A_281, '#skF_1'(A_281, B_282, C_283)), C_283) | ~r2_hidden(A_281, k10_relat_1(C_283, B_282)) | ~v1_relat_1(C_283))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.03/1.64  tff(c_624, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 3.03/1.64  tff(c_40, plain, (![F_116]: (~r2_hidden(F_116, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_116), '#skF_5') | ~m1_subset_1(F_116, '#skF_4') | r2_hidden('#skF_7', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.03/1.64  tff(c_630, plain, (![F_116]: (~r2_hidden(F_116, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_116), '#skF_5') | ~m1_subset_1(F_116, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_624, c_40])).
% 3.03/1.64  tff(c_733, plain, (![B_282]: (~r2_hidden('#skF_1'('#skF_6', B_282, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_282, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_282)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_721, c_630])).
% 3.03/1.64  tff(c_788, plain, (![B_293]: (~r2_hidden('#skF_1'('#skF_6', B_293, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_293, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_293)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_733])).
% 3.03/1.64  tff(c_792, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_788])).
% 3.03/1.64  tff(c_796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_693, c_719, c_792])).
% 3.03/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.64  
% 3.03/1.64  Inference rules
% 3.03/1.64  ----------------------
% 3.03/1.64  #Ref     : 0
% 3.03/1.64  #Sup     : 142
% 3.03/1.64  #Fact    : 0
% 3.03/1.64  #Define  : 0
% 3.03/1.64  #Split   : 9
% 3.03/1.64  #Chain   : 0
% 3.03/1.64  #Close   : 0
% 3.03/1.64  
% 3.03/1.64  Ordering : KBO
% 3.03/1.64  
% 3.03/1.64  Simplification rules
% 3.03/1.64  ----------------------
% 3.03/1.64  #Subsume      : 15
% 3.03/1.64  #Demod        : 55
% 3.03/1.64  #Tautology    : 26
% 3.03/1.64  #SimpNegUnit  : 4
% 3.03/1.64  #BackRed      : 3
% 3.03/1.64  
% 3.03/1.64  #Partial instantiations: 0
% 3.03/1.64  #Strategies tried      : 1
% 3.03/1.64  
% 3.03/1.64  Timing (in seconds)
% 3.03/1.64  ----------------------
% 3.03/1.65  Preprocessing        : 0.30
% 3.03/1.65  Parsing              : 0.15
% 3.03/1.65  CNF conversion       : 0.03
% 3.03/1.65  Main loop            : 0.36
% 3.03/1.65  Inferencing          : 0.14
% 3.03/1.65  Reduction            : 0.10
% 3.03/1.65  Demodulation         : 0.07
% 3.03/1.65  BG Simplification    : 0.02
% 3.03/1.65  Subsumption          : 0.06
% 3.03/1.65  Abstraction          : 0.02
% 3.03/1.65  MUC search           : 0.00
% 3.03/1.65  Cooper               : 0.00
% 3.03/1.65  Total                : 0.70
% 3.03/1.65  Index Insertion      : 0.00
% 3.03/1.65  Index Deletion       : 0.00
% 3.03/1.65  Index Matching       : 0.00
% 3.03/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
