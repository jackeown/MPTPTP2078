%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:38 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 300 expanded)
%              Number of leaves         :   35 ( 115 expanded)
%              Depth                    :    9
%              Number of atoms          :  235 ( 841 expanded)
%              Number of equality atoms :   17 (  31 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_108,negated_conjecture,(
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

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_26,plain,(
    ! [A_52,B_53] : v1_relat_1(k2_zfmisc_1(A_52,B_53)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_69,plain,(
    ! [B_163,A_164] :
      ( v1_relat_1(B_163)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(A_164))
      | ~ v1_relat_1(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_72,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_44,c_69])).

tff(c_75,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_72])).

tff(c_1314,plain,(
    ! [A_400,B_401,C_402,D_403] :
      ( k8_relset_1(A_400,B_401,C_402,D_403) = k10_relat_1(C_402,D_403)
      | ~ m1_subset_1(C_402,k1_zfmisc_1(k2_zfmisc_1(A_400,B_401))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1321,plain,(
    ! [D_403] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_403) = k10_relat_1('#skF_9',D_403) ),
    inference(resolution,[status(thm)],[c_44,c_1314])).

tff(c_861,plain,(
    ! [A_314,B_315,C_316,D_317] :
      ( k8_relset_1(A_314,B_315,C_316,D_317) = k10_relat_1(C_316,D_317)
      | ~ m1_subset_1(C_316,k1_zfmisc_1(k2_zfmisc_1(A_314,B_315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_868,plain,(
    ! [D_317] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_317) = k10_relat_1('#skF_9',D_317) ),
    inference(resolution,[status(thm)],[c_44,c_861])).

tff(c_372,plain,(
    ! [A_226,B_227,C_228,D_229] :
      ( k8_relset_1(A_226,B_227,C_228,D_229) = k10_relat_1(C_228,D_229)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_379,plain,(
    ! [D_229] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_229) = k10_relat_1('#skF_9',D_229) ),
    inference(resolution,[status(thm)],[c_44,c_372])).

tff(c_66,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_76,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_58,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_78,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_62,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_96,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_239,plain,(
    ! [D_203,A_204,B_205,E_206] :
      ( r2_hidden(D_203,k10_relat_1(A_204,B_205))
      | ~ r2_hidden(E_206,B_205)
      | ~ r2_hidden(k4_tarski(D_203,E_206),A_204)
      | ~ v1_relat_1(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_258,plain,(
    ! [D_207,A_208] :
      ( r2_hidden(D_207,k10_relat_1(A_208,'#skF_7'))
      | ~ r2_hidden(k4_tarski(D_207,'#skF_11'),A_208)
      | ~ v1_relat_1(A_208) ) ),
    inference(resolution,[status(thm)],[c_78,c_239])).

tff(c_264,plain,
    ( r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_96,c_258])).

tff(c_268,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_264])).

tff(c_205,plain,(
    ! [A_192,B_193,C_194,D_195] :
      ( k8_relset_1(A_192,B_193,C_194,D_195) = k10_relat_1(C_194,D_195)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_216,plain,(
    ! [D_195] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_195) = k10_relat_1('#skF_9',D_195) ),
    inference(resolution,[status(thm)],[c_44,c_205])).

tff(c_52,plain,(
    ! [F_158] :
      ( ~ r2_hidden(F_158,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_158),'#skF_9')
      | ~ m1_subset_1(F_158,'#skF_8')
      | ~ r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_286,plain,(
    ! [F_209] :
      ( ~ r2_hidden(F_209,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_209),'#skF_9')
      | ~ m1_subset_1(F_209,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_216,c_52])).

tff(c_297,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_96,c_286])).

tff(c_307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_78,c_297])).

tff(c_308,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_394,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_308])).

tff(c_30,plain,(
    ! [A_54,B_55,C_56] :
      ( r2_hidden('#skF_5'(A_54,B_55,C_56),B_55)
      | ~ r2_hidden(A_54,k10_relat_1(C_56,B_55))
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    ! [A_54,B_55,C_56] :
      ( r2_hidden(k4_tarski(A_54,'#skF_5'(A_54,B_55,C_56)),C_56)
      | ~ r2_hidden(A_54,k10_relat_1(C_56,B_55))
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_309,plain,(
    ~ r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_60,plain,(
    ! [F_158] :
      ( ~ r2_hidden(F_158,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_158),'#skF_9')
      | ~ m1_subset_1(F_158,'#skF_8')
      | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_418,plain,(
    ! [F_234] :
      ( ~ r2_hidden(F_234,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_234),'#skF_9')
      | ~ m1_subset_1(F_234,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_60])).

tff(c_422,plain,(
    ! [B_55] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_55,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_55,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_55))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32,c_418])).

tff(c_537,plain,(
    ! [B_262] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_262,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_262,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_262)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_422])).

tff(c_545,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_30,c_537])).

tff(c_551,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_394,c_545])).

tff(c_86,plain,(
    ! [A_168,B_169,C_170] :
      ( k2_relset_1(A_168,B_169,C_170) = k2_relat_1(C_170)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_90,plain,(
    k2_relset_1('#skF_6','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_44,c_86])).

tff(c_326,plain,(
    ! [A_214,B_215,C_216] :
      ( m1_subset_1(k2_relset_1(A_214,B_215,C_216),k1_zfmisc_1(B_215))
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_214,B_215))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_336,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_326])).

tff(c_340,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_336])).

tff(c_363,plain,(
    ! [A_223,B_224,C_225] :
      ( r2_hidden('#skF_5'(A_223,B_224,C_225),k2_relat_1(C_225))
      | ~ r2_hidden(A_223,k10_relat_1(C_225,B_224))
      | ~ v1_relat_1(C_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_713,plain,(
    ! [A_285,B_286,C_287,A_288] :
      ( r2_hidden('#skF_5'(A_285,B_286,C_287),A_288)
      | ~ m1_subset_1(k2_relat_1(C_287),k1_zfmisc_1(A_288))
      | ~ r2_hidden(A_285,k10_relat_1(C_287,B_286))
      | ~ v1_relat_1(C_287) ) ),
    inference(resolution,[status(thm)],[c_363,c_2])).

tff(c_715,plain,(
    ! [A_285,B_286] :
      ( r2_hidden('#skF_5'(A_285,B_286,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_285,k10_relat_1('#skF_9',B_286))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_340,c_713])).

tff(c_719,plain,(
    ! [A_289,B_290] :
      ( r2_hidden('#skF_5'(A_289,B_290,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_289,k10_relat_1('#skF_9',B_290)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_715])).

tff(c_4,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_738,plain,(
    ! [A_292,B_293] :
      ( m1_subset_1('#skF_5'(A_292,B_293,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_292,k10_relat_1('#skF_9',B_293)) ) ),
    inference(resolution,[status(thm)],[c_719,c_4])).

tff(c_765,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_394,c_738])).

tff(c_785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_551,c_765])).

tff(c_786,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_871,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_868,c_786])).

tff(c_894,plain,(
    ! [A_319,B_320,C_321] :
      ( r2_hidden(k4_tarski(A_319,'#skF_5'(A_319,B_320,C_321)),C_321)
      | ~ r2_hidden(A_319,k10_relat_1(C_321,B_320))
      | ~ v1_relat_1(C_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_787,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,(
    ! [F_158] :
      ( ~ r2_hidden(F_158,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_158),'#skF_9')
      | ~ m1_subset_1(F_158,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_859,plain,(
    ! [F_158] :
      ( ~ r2_hidden(F_158,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_158),'#skF_9')
      | ~ m1_subset_1(F_158,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_787,c_56])).

tff(c_898,plain,(
    ! [B_320] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_320,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_320,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_320))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_894,c_859])).

tff(c_1037,plain,(
    ! [B_350] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_350,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_350,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_350)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_898])).

tff(c_1045,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_30,c_1037])).

tff(c_1051,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_871,c_1045])).

tff(c_795,plain,(
    ! [A_294,B_295,C_296] :
      ( k2_relset_1(A_294,B_295,C_296) = k2_relat_1(C_296)
      | ~ m1_subset_1(C_296,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_799,plain,(
    k2_relset_1('#skF_6','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_44,c_795])).

tff(c_815,plain,(
    ! [A_301,B_302,C_303] :
      ( m1_subset_1(k2_relset_1(A_301,B_302,C_303),k1_zfmisc_1(B_302))
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_301,B_302))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_825,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_799,c_815])).

tff(c_829,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_825])).

tff(c_835,plain,(
    ! [A_304,B_305,C_306] :
      ( r2_hidden('#skF_5'(A_304,B_305,C_306),k2_relat_1(C_306))
      | ~ r2_hidden(A_304,k10_relat_1(C_306,B_305))
      | ~ v1_relat_1(C_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1172,plain,(
    ! [A_369,B_370,C_371,A_372] :
      ( r2_hidden('#skF_5'(A_369,B_370,C_371),A_372)
      | ~ m1_subset_1(k2_relat_1(C_371),k1_zfmisc_1(A_372))
      | ~ r2_hidden(A_369,k10_relat_1(C_371,B_370))
      | ~ v1_relat_1(C_371) ) ),
    inference(resolution,[status(thm)],[c_835,c_2])).

tff(c_1174,plain,(
    ! [A_369,B_370] :
      ( r2_hidden('#skF_5'(A_369,B_370,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_369,k10_relat_1('#skF_9',B_370))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_829,c_1172])).

tff(c_1178,plain,(
    ! [A_373,B_374] :
      ( r2_hidden('#skF_5'(A_373,B_374,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_373,k10_relat_1('#skF_9',B_374)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1174])).

tff(c_1189,plain,(
    ! [A_375,B_376] :
      ( m1_subset_1('#skF_5'(A_375,B_376,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_375,k10_relat_1('#skF_9',B_376)) ) ),
    inference(resolution,[status(thm)],[c_1178,c_4])).

tff(c_1220,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_871,c_1189])).

tff(c_1237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1051,c_1220])).

tff(c_1238,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1343,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1321,c_1238])).

tff(c_1322,plain,(
    ! [A_404,B_405,C_406] :
      ( r2_hidden(k4_tarski(A_404,'#skF_5'(A_404,B_405,C_406)),C_406)
      | ~ r2_hidden(A_404,k10_relat_1(C_406,B_405))
      | ~ v1_relat_1(C_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1239,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_64,plain,(
    ! [F_158] :
      ( ~ r2_hidden(F_158,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_158),'#skF_9')
      | ~ m1_subset_1(F_158,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1288,plain,(
    ! [F_158] :
      ( ~ r2_hidden(F_158,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_158),'#skF_9')
      | ~ m1_subset_1(F_158,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1239,c_64])).

tff(c_1329,plain,(
    ! [B_405] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_405,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_405,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_405))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1322,c_1288])).

tff(c_1453,plain,(
    ! [B_429] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_429,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_429,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_429)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1329])).

tff(c_1457,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_30,c_1453])).

tff(c_1460,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1343,c_1457])).

tff(c_1251,plain,(
    ! [A_381,B_382,C_383] :
      ( k2_relset_1(A_381,B_382,C_383) = k2_relat_1(C_383)
      | ~ m1_subset_1(C_383,k1_zfmisc_1(k2_zfmisc_1(A_381,B_382))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1255,plain,(
    k2_relset_1('#skF_6','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_44,c_1251])).

tff(c_1268,plain,(
    ! [A_387,B_388,C_389] :
      ( m1_subset_1(k2_relset_1(A_387,B_388,C_389),k1_zfmisc_1(B_388))
      | ~ m1_subset_1(C_389,k1_zfmisc_1(k2_zfmisc_1(A_387,B_388))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1278,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1255,c_1268])).

tff(c_1282,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1278])).

tff(c_1306,plain,(
    ! [A_397,B_398,C_399] :
      ( r2_hidden('#skF_5'(A_397,B_398,C_399),k2_relat_1(C_399))
      | ~ r2_hidden(A_397,k10_relat_1(C_399,B_398))
      | ~ v1_relat_1(C_399) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1645,plain,(
    ! [A_458,B_459,C_460,A_461] :
      ( r2_hidden('#skF_5'(A_458,B_459,C_460),A_461)
      | ~ m1_subset_1(k2_relat_1(C_460),k1_zfmisc_1(A_461))
      | ~ r2_hidden(A_458,k10_relat_1(C_460,B_459))
      | ~ v1_relat_1(C_460) ) ),
    inference(resolution,[status(thm)],[c_1306,c_2])).

tff(c_1647,plain,(
    ! [A_458,B_459] :
      ( r2_hidden('#skF_5'(A_458,B_459,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_458,k10_relat_1('#skF_9',B_459))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1282,c_1645])).

tff(c_1652,plain,(
    ! [A_465,B_466] :
      ( r2_hidden('#skF_5'(A_465,B_466,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_465,k10_relat_1('#skF_9',B_466)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1647])).

tff(c_1663,plain,(
    ! [A_467,B_468] :
      ( m1_subset_1('#skF_5'(A_467,B_468,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_467,k10_relat_1('#skF_9',B_468)) ) ),
    inference(resolution,[status(thm)],[c_1652,c_4])).

tff(c_1690,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_1343,c_1663])).

tff(c_1710,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1460,c_1690])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.10/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.10/1.70  
% 4.10/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.10/1.71  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 4.10/1.71  
% 4.10/1.71  %Foreground sorts:
% 4.10/1.71  
% 4.10/1.71  
% 4.10/1.71  %Background operators:
% 4.10/1.71  
% 4.10/1.71  
% 4.10/1.71  %Foreground operators:
% 4.10/1.71  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.10/1.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.10/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.10/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.10/1.71  tff('#skF_11', type, '#skF_11': $i).
% 4.10/1.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.10/1.71  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.10/1.71  tff('#skF_7', type, '#skF_7': $i).
% 4.10/1.71  tff('#skF_10', type, '#skF_10': $i).
% 4.10/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.10/1.71  tff('#skF_6', type, '#skF_6': $i).
% 4.10/1.71  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.10/1.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.10/1.71  tff('#skF_9', type, '#skF_9': $i).
% 4.10/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.10/1.71  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.10/1.71  tff('#skF_8', type, '#skF_8': $i).
% 4.10/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.10/1.71  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.10/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.10/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.10/1.71  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.10/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.10/1.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.10/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.10/1.71  
% 4.10/1.73  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.10/1.73  tff(f_108, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_relset_1)).
% 4.10/1.73  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.10/1.73  tff(f_81, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.10/1.73  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 4.10/1.73  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 4.10/1.73  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.10/1.73  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.10/1.73  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.10/1.73  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.10/1.73  tff(c_26, plain, (![A_52, B_53]: (v1_relat_1(k2_zfmisc_1(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.10/1.73  tff(c_44, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.10/1.73  tff(c_69, plain, (![B_163, A_164]: (v1_relat_1(B_163) | ~m1_subset_1(B_163, k1_zfmisc_1(A_164)) | ~v1_relat_1(A_164))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.10/1.73  tff(c_72, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_44, c_69])).
% 4.10/1.73  tff(c_75, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_72])).
% 4.10/1.73  tff(c_1314, plain, (![A_400, B_401, C_402, D_403]: (k8_relset_1(A_400, B_401, C_402, D_403)=k10_relat_1(C_402, D_403) | ~m1_subset_1(C_402, k1_zfmisc_1(k2_zfmisc_1(A_400, B_401))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.10/1.73  tff(c_1321, plain, (![D_403]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_403)=k10_relat_1('#skF_9', D_403))), inference(resolution, [status(thm)], [c_44, c_1314])).
% 4.10/1.73  tff(c_861, plain, (![A_314, B_315, C_316, D_317]: (k8_relset_1(A_314, B_315, C_316, D_317)=k10_relat_1(C_316, D_317) | ~m1_subset_1(C_316, k1_zfmisc_1(k2_zfmisc_1(A_314, B_315))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.10/1.73  tff(c_868, plain, (![D_317]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_317)=k10_relat_1('#skF_9', D_317))), inference(resolution, [status(thm)], [c_44, c_861])).
% 4.10/1.73  tff(c_372, plain, (![A_226, B_227, C_228, D_229]: (k8_relset_1(A_226, B_227, C_228, D_229)=k10_relat_1(C_228, D_229) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.10/1.73  tff(c_379, plain, (![D_229]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_229)=k10_relat_1('#skF_9', D_229))), inference(resolution, [status(thm)], [c_44, c_372])).
% 4.10/1.73  tff(c_66, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.10/1.73  tff(c_76, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_66])).
% 4.10/1.73  tff(c_58, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.10/1.73  tff(c_78, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_58])).
% 4.10/1.73  tff(c_62, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.10/1.73  tff(c_96, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitLeft, [status(thm)], [c_62])).
% 4.10/1.73  tff(c_239, plain, (![D_203, A_204, B_205, E_206]: (r2_hidden(D_203, k10_relat_1(A_204, B_205)) | ~r2_hidden(E_206, B_205) | ~r2_hidden(k4_tarski(D_203, E_206), A_204) | ~v1_relat_1(A_204))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.10/1.73  tff(c_258, plain, (![D_207, A_208]: (r2_hidden(D_207, k10_relat_1(A_208, '#skF_7')) | ~r2_hidden(k4_tarski(D_207, '#skF_11'), A_208) | ~v1_relat_1(A_208))), inference(resolution, [status(thm)], [c_78, c_239])).
% 4.10/1.73  tff(c_264, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_96, c_258])).
% 4.10/1.73  tff(c_268, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_264])).
% 4.10/1.73  tff(c_205, plain, (![A_192, B_193, C_194, D_195]: (k8_relset_1(A_192, B_193, C_194, D_195)=k10_relat_1(C_194, D_195) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.10/1.73  tff(c_216, plain, (![D_195]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_195)=k10_relat_1('#skF_9', D_195))), inference(resolution, [status(thm)], [c_44, c_205])).
% 4.10/1.73  tff(c_52, plain, (![F_158]: (~r2_hidden(F_158, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_158), '#skF_9') | ~m1_subset_1(F_158, '#skF_8') | ~r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.10/1.73  tff(c_286, plain, (![F_209]: (~r2_hidden(F_209, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_209), '#skF_9') | ~m1_subset_1(F_209, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_216, c_52])).
% 4.10/1.73  tff(c_297, plain, (~r2_hidden('#skF_11', '#skF_7') | ~m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_96, c_286])).
% 4.10/1.73  tff(c_307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_78, c_297])).
% 4.10/1.73  tff(c_308, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_62])).
% 4.10/1.73  tff(c_394, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_379, c_308])).
% 4.10/1.73  tff(c_30, plain, (![A_54, B_55, C_56]: (r2_hidden('#skF_5'(A_54, B_55, C_56), B_55) | ~r2_hidden(A_54, k10_relat_1(C_56, B_55)) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.10/1.73  tff(c_32, plain, (![A_54, B_55, C_56]: (r2_hidden(k4_tarski(A_54, '#skF_5'(A_54, B_55, C_56)), C_56) | ~r2_hidden(A_54, k10_relat_1(C_56, B_55)) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.10/1.73  tff(c_309, plain, (~r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitRight, [status(thm)], [c_62])).
% 4.10/1.73  tff(c_60, plain, (![F_158]: (~r2_hidden(F_158, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_158), '#skF_9') | ~m1_subset_1(F_158, '#skF_8') | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.10/1.73  tff(c_418, plain, (![F_234]: (~r2_hidden(F_234, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_234), '#skF_9') | ~m1_subset_1(F_234, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_309, c_60])).
% 4.10/1.73  tff(c_422, plain, (![B_55]: (~r2_hidden('#skF_5'('#skF_10', B_55, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_55, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_55)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_32, c_418])).
% 4.10/1.73  tff(c_537, plain, (![B_262]: (~r2_hidden('#skF_5'('#skF_10', B_262, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_262, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_262)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_422])).
% 4.10/1.73  tff(c_545, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_30, c_537])).
% 4.10/1.73  tff(c_551, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_394, c_545])).
% 4.10/1.73  tff(c_86, plain, (![A_168, B_169, C_170]: (k2_relset_1(A_168, B_169, C_170)=k2_relat_1(C_170) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.10/1.73  tff(c_90, plain, (k2_relset_1('#skF_6', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_44, c_86])).
% 4.10/1.73  tff(c_326, plain, (![A_214, B_215, C_216]: (m1_subset_1(k2_relset_1(A_214, B_215, C_216), k1_zfmisc_1(B_215)) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_214, B_215))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.10/1.73  tff(c_336, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_326])).
% 4.10/1.73  tff(c_340, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_336])).
% 4.10/1.73  tff(c_363, plain, (![A_223, B_224, C_225]: (r2_hidden('#skF_5'(A_223, B_224, C_225), k2_relat_1(C_225)) | ~r2_hidden(A_223, k10_relat_1(C_225, B_224)) | ~v1_relat_1(C_225))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.10/1.73  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.10/1.73  tff(c_713, plain, (![A_285, B_286, C_287, A_288]: (r2_hidden('#skF_5'(A_285, B_286, C_287), A_288) | ~m1_subset_1(k2_relat_1(C_287), k1_zfmisc_1(A_288)) | ~r2_hidden(A_285, k10_relat_1(C_287, B_286)) | ~v1_relat_1(C_287))), inference(resolution, [status(thm)], [c_363, c_2])).
% 4.10/1.73  tff(c_715, plain, (![A_285, B_286]: (r2_hidden('#skF_5'(A_285, B_286, '#skF_9'), '#skF_8') | ~r2_hidden(A_285, k10_relat_1('#skF_9', B_286)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_340, c_713])).
% 4.10/1.73  tff(c_719, plain, (![A_289, B_290]: (r2_hidden('#skF_5'(A_289, B_290, '#skF_9'), '#skF_8') | ~r2_hidden(A_289, k10_relat_1('#skF_9', B_290)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_715])).
% 4.10/1.73  tff(c_4, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.10/1.73  tff(c_738, plain, (![A_292, B_293]: (m1_subset_1('#skF_5'(A_292, B_293, '#skF_9'), '#skF_8') | ~r2_hidden(A_292, k10_relat_1('#skF_9', B_293)))), inference(resolution, [status(thm)], [c_719, c_4])).
% 4.10/1.73  tff(c_765, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_394, c_738])).
% 4.10/1.73  tff(c_785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_551, c_765])).
% 4.10/1.73  tff(c_786, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_58])).
% 4.10/1.73  tff(c_871, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_868, c_786])).
% 4.10/1.73  tff(c_894, plain, (![A_319, B_320, C_321]: (r2_hidden(k4_tarski(A_319, '#skF_5'(A_319, B_320, C_321)), C_321) | ~r2_hidden(A_319, k10_relat_1(C_321, B_320)) | ~v1_relat_1(C_321))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.10/1.73  tff(c_787, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_58])).
% 4.10/1.73  tff(c_56, plain, (![F_158]: (~r2_hidden(F_158, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_158), '#skF_9') | ~m1_subset_1(F_158, '#skF_8') | r2_hidden('#skF_11', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.10/1.73  tff(c_859, plain, (![F_158]: (~r2_hidden(F_158, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_158), '#skF_9') | ~m1_subset_1(F_158, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_787, c_56])).
% 4.10/1.73  tff(c_898, plain, (![B_320]: (~r2_hidden('#skF_5'('#skF_10', B_320, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_320, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_320)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_894, c_859])).
% 4.10/1.73  tff(c_1037, plain, (![B_350]: (~r2_hidden('#skF_5'('#skF_10', B_350, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_350, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_350)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_898])).
% 4.10/1.73  tff(c_1045, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_30, c_1037])).
% 4.10/1.73  tff(c_1051, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_871, c_1045])).
% 4.10/1.73  tff(c_795, plain, (![A_294, B_295, C_296]: (k2_relset_1(A_294, B_295, C_296)=k2_relat_1(C_296) | ~m1_subset_1(C_296, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.10/1.73  tff(c_799, plain, (k2_relset_1('#skF_6', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_44, c_795])).
% 4.10/1.73  tff(c_815, plain, (![A_301, B_302, C_303]: (m1_subset_1(k2_relset_1(A_301, B_302, C_303), k1_zfmisc_1(B_302)) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_301, B_302))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.10/1.73  tff(c_825, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_799, c_815])).
% 4.10/1.73  tff(c_829, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_825])).
% 4.10/1.73  tff(c_835, plain, (![A_304, B_305, C_306]: (r2_hidden('#skF_5'(A_304, B_305, C_306), k2_relat_1(C_306)) | ~r2_hidden(A_304, k10_relat_1(C_306, B_305)) | ~v1_relat_1(C_306))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.10/1.73  tff(c_1172, plain, (![A_369, B_370, C_371, A_372]: (r2_hidden('#skF_5'(A_369, B_370, C_371), A_372) | ~m1_subset_1(k2_relat_1(C_371), k1_zfmisc_1(A_372)) | ~r2_hidden(A_369, k10_relat_1(C_371, B_370)) | ~v1_relat_1(C_371))), inference(resolution, [status(thm)], [c_835, c_2])).
% 4.10/1.73  tff(c_1174, plain, (![A_369, B_370]: (r2_hidden('#skF_5'(A_369, B_370, '#skF_9'), '#skF_8') | ~r2_hidden(A_369, k10_relat_1('#skF_9', B_370)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_829, c_1172])).
% 4.10/1.73  tff(c_1178, plain, (![A_373, B_374]: (r2_hidden('#skF_5'(A_373, B_374, '#skF_9'), '#skF_8') | ~r2_hidden(A_373, k10_relat_1('#skF_9', B_374)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1174])).
% 4.10/1.73  tff(c_1189, plain, (![A_375, B_376]: (m1_subset_1('#skF_5'(A_375, B_376, '#skF_9'), '#skF_8') | ~r2_hidden(A_375, k10_relat_1('#skF_9', B_376)))), inference(resolution, [status(thm)], [c_1178, c_4])).
% 4.10/1.73  tff(c_1220, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_871, c_1189])).
% 4.10/1.73  tff(c_1237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1051, c_1220])).
% 4.10/1.73  tff(c_1238, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_66])).
% 4.10/1.73  tff(c_1343, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1321, c_1238])).
% 4.10/1.73  tff(c_1322, plain, (![A_404, B_405, C_406]: (r2_hidden(k4_tarski(A_404, '#skF_5'(A_404, B_405, C_406)), C_406) | ~r2_hidden(A_404, k10_relat_1(C_406, B_405)) | ~v1_relat_1(C_406))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.10/1.73  tff(c_1239, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_66])).
% 4.10/1.73  tff(c_64, plain, (![F_158]: (~r2_hidden(F_158, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_158), '#skF_9') | ~m1_subset_1(F_158, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.10/1.73  tff(c_1288, plain, (![F_158]: (~r2_hidden(F_158, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_158), '#skF_9') | ~m1_subset_1(F_158, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1239, c_64])).
% 4.10/1.73  tff(c_1329, plain, (![B_405]: (~r2_hidden('#skF_5'('#skF_10', B_405, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_405, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_405)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1322, c_1288])).
% 4.10/1.73  tff(c_1453, plain, (![B_429]: (~r2_hidden('#skF_5'('#skF_10', B_429, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_429, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_429)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1329])).
% 4.10/1.73  tff(c_1457, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_30, c_1453])).
% 4.10/1.73  tff(c_1460, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1343, c_1457])).
% 4.10/1.73  tff(c_1251, plain, (![A_381, B_382, C_383]: (k2_relset_1(A_381, B_382, C_383)=k2_relat_1(C_383) | ~m1_subset_1(C_383, k1_zfmisc_1(k2_zfmisc_1(A_381, B_382))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.10/1.73  tff(c_1255, plain, (k2_relset_1('#skF_6', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_44, c_1251])).
% 4.10/1.73  tff(c_1268, plain, (![A_387, B_388, C_389]: (m1_subset_1(k2_relset_1(A_387, B_388, C_389), k1_zfmisc_1(B_388)) | ~m1_subset_1(C_389, k1_zfmisc_1(k2_zfmisc_1(A_387, B_388))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.10/1.73  tff(c_1278, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_1255, c_1268])).
% 4.10/1.73  tff(c_1282, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1278])).
% 4.10/1.73  tff(c_1306, plain, (![A_397, B_398, C_399]: (r2_hidden('#skF_5'(A_397, B_398, C_399), k2_relat_1(C_399)) | ~r2_hidden(A_397, k10_relat_1(C_399, B_398)) | ~v1_relat_1(C_399))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.10/1.73  tff(c_1645, plain, (![A_458, B_459, C_460, A_461]: (r2_hidden('#skF_5'(A_458, B_459, C_460), A_461) | ~m1_subset_1(k2_relat_1(C_460), k1_zfmisc_1(A_461)) | ~r2_hidden(A_458, k10_relat_1(C_460, B_459)) | ~v1_relat_1(C_460))), inference(resolution, [status(thm)], [c_1306, c_2])).
% 4.10/1.73  tff(c_1647, plain, (![A_458, B_459]: (r2_hidden('#skF_5'(A_458, B_459, '#skF_9'), '#skF_8') | ~r2_hidden(A_458, k10_relat_1('#skF_9', B_459)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1282, c_1645])).
% 4.10/1.73  tff(c_1652, plain, (![A_465, B_466]: (r2_hidden('#skF_5'(A_465, B_466, '#skF_9'), '#skF_8') | ~r2_hidden(A_465, k10_relat_1('#skF_9', B_466)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1647])).
% 4.10/1.73  tff(c_1663, plain, (![A_467, B_468]: (m1_subset_1('#skF_5'(A_467, B_468, '#skF_9'), '#skF_8') | ~r2_hidden(A_467, k10_relat_1('#skF_9', B_468)))), inference(resolution, [status(thm)], [c_1652, c_4])).
% 4.10/1.73  tff(c_1690, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_1343, c_1663])).
% 4.10/1.73  tff(c_1710, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1460, c_1690])).
% 4.10/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.10/1.73  
% 4.10/1.73  Inference rules
% 4.10/1.73  ----------------------
% 4.10/1.73  #Ref     : 0
% 4.10/1.73  #Sup     : 353
% 4.10/1.73  #Fact    : 0
% 4.10/1.73  #Define  : 0
% 4.10/1.73  #Split   : 13
% 4.10/1.73  #Chain   : 0
% 4.10/1.73  #Close   : 0
% 4.10/1.73  
% 4.10/1.73  Ordering : KBO
% 4.10/1.73  
% 4.10/1.73  Simplification rules
% 4.10/1.73  ----------------------
% 4.10/1.73  #Subsume      : 18
% 4.10/1.73  #Demod        : 81
% 4.10/1.73  #Tautology    : 27
% 4.10/1.73  #SimpNegUnit  : 6
% 4.10/1.73  #BackRed      : 9
% 4.10/1.73  
% 4.10/1.73  #Partial instantiations: 0
% 4.10/1.73  #Strategies tried      : 1
% 4.10/1.73  
% 4.10/1.73  Timing (in seconds)
% 4.10/1.73  ----------------------
% 4.10/1.73  Preprocessing        : 0.36
% 4.10/1.73  Parsing              : 0.18
% 4.10/1.73  CNF conversion       : 0.04
% 4.10/1.73  Main loop            : 0.59
% 4.10/1.74  Inferencing          : 0.22
% 4.10/1.74  Reduction            : 0.16
% 4.10/1.74  Demodulation         : 0.11
% 4.10/1.74  BG Simplification    : 0.03
% 4.10/1.74  Subsumption          : 0.12
% 4.10/1.74  Abstraction          : 0.04
% 4.10/1.74  MUC search           : 0.00
% 4.10/1.74  Cooper               : 0.00
% 4.10/1.74  Total                : 1.00
% 4.10/1.74  Index Insertion      : 0.00
% 4.10/1.74  Index Deletion       : 0.00
% 4.10/1.74  Index Matching       : 0.00
% 4.10/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
