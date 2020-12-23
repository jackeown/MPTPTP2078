%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:37 EST 2020

% Result     : Theorem 6.39s
% Output     : CNFRefutation 6.39s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 290 expanded)
%              Number of leaves         :   29 ( 108 expanded)
%              Depth                    :    8
%              Number of atoms          :  237 ( 876 expanded)
%              Number of equality atoms :    9 (  24 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(f_96,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_54,plain,(
    ! [C_118,A_119,B_120] :
      ( v1_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_58,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_54])).

tff(c_3421,plain,(
    ! [A_690,B_691,C_692,D_693] :
      ( k8_relset_1(A_690,B_691,C_692,D_693) = k10_relat_1(C_692,D_693)
      | ~ m1_subset_1(C_692,k1_zfmisc_1(k2_zfmisc_1(A_690,B_691))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3424,plain,(
    ! [D_693] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_693) = k10_relat_1('#skF_5',D_693) ),
    inference(resolution,[status(thm)],[c_30,c_3421])).

tff(c_2181,plain,(
    ! [A_488,B_489,C_490,D_491] :
      ( k8_relset_1(A_488,B_489,C_490,D_491) = k10_relat_1(C_490,D_491)
      | ~ m1_subset_1(C_490,k1_zfmisc_1(k2_zfmisc_1(A_488,B_489))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2184,plain,(
    ! [D_491] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_491) = k10_relat_1('#skF_5',D_491) ),
    inference(resolution,[status(thm)],[c_30,c_2181])).

tff(c_844,plain,(
    ! [A_264,B_265,C_266,D_267] :
      ( k8_relset_1(A_264,B_265,C_266,D_267) = k10_relat_1(C_266,D_267)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(A_264,B_265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_847,plain,(
    ! [D_267] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_267) = k10_relat_1('#skF_5',D_267) ),
    inference(resolution,[status(thm)],[c_30,c_844])).

tff(c_52,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | m1_subset_1('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_60,plain,(
    m1_subset_1('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_44,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | r2_hidden('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_59,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_48,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_74,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_227,plain,(
    ! [A_160,B_161,C_162,D_163] :
      ( k8_relset_1(A_160,B_161,C_162,D_163) = k10_relat_1(C_162,D_163)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_234,plain,(
    ! [D_163] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_163) = k10_relat_1('#skF_5',D_163) ),
    inference(resolution,[status(thm)],[c_30,c_227])).

tff(c_38,plain,(
    ! [F_115] :
      ( ~ r2_hidden(F_115,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_115),'#skF_5')
      | ~ m1_subset_1(F_115,'#skF_4')
      | ~ r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_276,plain,(
    ! [F_115] :
      ( ~ r2_hidden(F_115,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_115),'#skF_5')
      | ~ m1_subset_1(F_115,'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_38])).

tff(c_277,plain,(
    ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_20,plain,(
    ! [B_18,C_19,A_17] :
      ( r2_hidden(B_18,k2_relat_1(C_19))
      | ~ r2_hidden(k4_tarski(A_17,B_18),C_19)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_77,plain,
    ( r2_hidden('#skF_7',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_20])).

tff(c_88,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_77])).

tff(c_341,plain,(
    ! [A_196,C_197,B_198,D_199] :
      ( r2_hidden(A_196,k10_relat_1(C_197,B_198))
      | ~ r2_hidden(D_199,B_198)
      | ~ r2_hidden(k4_tarski(A_196,D_199),C_197)
      | ~ r2_hidden(D_199,k2_relat_1(C_197))
      | ~ v1_relat_1(C_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_699,plain,(
    ! [A_243,C_244] :
      ( r2_hidden(A_243,k10_relat_1(C_244,'#skF_3'))
      | ~ r2_hidden(k4_tarski(A_243,'#skF_7'),C_244)
      | ~ r2_hidden('#skF_7',k2_relat_1(C_244))
      | ~ v1_relat_1(C_244) ) ),
    inference(resolution,[status(thm)],[c_59,c_341])).

tff(c_741,plain,
    ( r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ r2_hidden('#skF_7',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_699])).

tff(c_754,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_88,c_741])).

tff(c_756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_754])).

tff(c_771,plain,(
    ! [F_245] :
      ( ~ r2_hidden(F_245,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_245),'#skF_5')
      | ~ m1_subset_1(F_245,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_778,plain,
    ( ~ r2_hidden('#skF_7','#skF_3')
    | ~ m1_subset_1('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_771])).

tff(c_785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_59,c_778])).

tff(c_786,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_850,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_786])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] :
      ( r2_hidden('#skF_1'(A_11,B_12,C_13),B_12)
      | ~ r2_hidden(A_11,k10_relat_1(C_13,B_12))
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( r2_hidden(k4_tarski(A_11,'#skF_1'(A_11,B_12,C_13)),C_13)
      | ~ r2_hidden(A_11,k10_relat_1(C_13,B_12))
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_787,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [F_115] :
      ( ~ r2_hidden(F_115,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_115),'#skF_5')
      | ~ m1_subset_1(F_115,'#skF_4')
      | r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_905,plain,(
    ! [F_273] :
      ( ~ r2_hidden(F_273,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_273),'#skF_5')
      | ~ m1_subset_1(F_273,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_787,c_46])).

tff(c_909,plain,(
    ! [B_12] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_12,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_12,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_12))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_905])).

tff(c_1198,plain,(
    ! [B_327] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_327,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_327,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_327)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_909])).

tff(c_1206,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_1198])).

tff(c_1212,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_850,c_1206])).

tff(c_873,plain,(
    ! [A_269,B_270,C_271] :
      ( r2_hidden(k4_tarski(A_269,'#skF_1'(A_269,B_270,C_271)),C_271)
      | ~ r2_hidden(A_269,k10_relat_1(C_271,B_270))
      | ~ v1_relat_1(C_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1319,plain,(
    ! [A_350,B_351,C_352,A_353] :
      ( r2_hidden(k4_tarski(A_350,'#skF_1'(A_350,B_351,C_352)),A_353)
      | ~ m1_subset_1(C_352,k1_zfmisc_1(A_353))
      | ~ r2_hidden(A_350,k10_relat_1(C_352,B_351))
      | ~ v1_relat_1(C_352) ) ),
    inference(resolution,[status(thm)],[c_873,c_8])).

tff(c_4,plain,(
    ! [B_2,D_4,A_1,C_3] :
      ( r2_hidden(B_2,D_4)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1855,plain,(
    ! [D_416,B_414,C_413,A_415,C_417] :
      ( r2_hidden('#skF_1'(A_415,B_414,C_413),D_416)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(C_417,D_416)))
      | ~ r2_hidden(A_415,k10_relat_1(C_413,B_414))
      | ~ v1_relat_1(C_413) ) ),
    inference(resolution,[status(thm)],[c_1319,c_4])).

tff(c_1863,plain,(
    ! [A_415,B_414] :
      ( r2_hidden('#skF_1'(A_415,B_414,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_415,k10_relat_1('#skF_5',B_414))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_1855])).

tff(c_1933,plain,(
    ! [A_423,B_424] :
      ( r2_hidden('#skF_1'(A_423,B_424,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_423,k10_relat_1('#skF_5',B_424)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1863])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1950,plain,(
    ! [A_425,B_426] :
      ( m1_subset_1('#skF_1'(A_425,B_426,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_425,k10_relat_1('#skF_5',B_426)) ) ),
    inference(resolution,[status(thm)],[c_1933,c_10])).

tff(c_1977,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_850,c_1950])).

tff(c_1995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1212,c_1977])).

tff(c_1997,plain,(
    ~ m1_subset_1('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2002,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_2013,plain,(
    ! [C_435,A_436,B_437] :
      ( r2_hidden(C_435,A_436)
      | ~ r2_hidden(C_435,B_437)
      | ~ m1_subset_1(B_437,k1_zfmisc_1(A_436)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2032,plain,(
    ! [A_440] :
      ( r2_hidden(k4_tarski('#skF_6','#skF_7'),A_440)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_440)) ) ),
    inference(resolution,[status(thm)],[c_2002,c_2013])).

tff(c_2097,plain,(
    ! [D_449,C_450] :
      ( r2_hidden('#skF_7',D_449)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(C_450,D_449))) ) ),
    inference(resolution,[status(thm)],[c_2032,c_4])).

tff(c_2101,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_2097])).

tff(c_2106,plain,(
    m1_subset_1('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_2101,c_10])).

tff(c_2111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1997,c_2106])).

tff(c_2112,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2187,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2184,c_2112])).

tff(c_2197,plain,(
    ! [A_493,B_494,C_495] :
      ( r2_hidden(k4_tarski(A_493,'#skF_1'(A_493,B_494,C_495)),C_495)
      | ~ r2_hidden(A_493,k10_relat_1(C_495,B_494))
      | ~ v1_relat_1(C_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_50,plain,(
    ! [F_115] :
      ( ~ r2_hidden(F_115,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_115),'#skF_5')
      | ~ m1_subset_1(F_115,'#skF_4')
      | m1_subset_1('#skF_7','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2119,plain,(
    ! [F_115] :
      ( ~ r2_hidden(F_115,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_115),'#skF_5')
      | ~ m1_subset_1(F_115,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1997,c_50])).

tff(c_2220,plain,(
    ! [B_494] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_494,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_494,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_494))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2197,c_2119])).

tff(c_2288,plain,(
    ! [B_508] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_508,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_508,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_508)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2220])).

tff(c_2292,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_2288])).

tff(c_2295,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2187,c_2292])).

tff(c_2767,plain,(
    ! [A_585,B_586,C_587,A_588] :
      ( r2_hidden(k4_tarski(A_585,'#skF_1'(A_585,B_586,C_587)),A_588)
      | ~ m1_subset_1(C_587,k1_zfmisc_1(A_588))
      | ~ r2_hidden(A_585,k10_relat_1(C_587,B_586))
      | ~ v1_relat_1(C_587) ) ),
    inference(resolution,[status(thm)],[c_2197,c_8])).

tff(c_3286,plain,(
    ! [C_652,B_653,C_651,A_649,D_650] :
      ( r2_hidden('#skF_1'(A_649,B_653,C_651),D_650)
      | ~ m1_subset_1(C_651,k1_zfmisc_1(k2_zfmisc_1(C_652,D_650)))
      | ~ r2_hidden(A_649,k10_relat_1(C_651,B_653))
      | ~ v1_relat_1(C_651) ) ),
    inference(resolution,[status(thm)],[c_2767,c_4])).

tff(c_3297,plain,(
    ! [A_649,B_653] :
      ( r2_hidden('#skF_1'(A_649,B_653,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_649,k10_relat_1('#skF_5',B_653))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_3286])).

tff(c_3304,plain,(
    ! [A_654,B_655] :
      ( r2_hidden('#skF_1'(A_654,B_655,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_654,k10_relat_1('#skF_5',B_655)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_3297])).

tff(c_3321,plain,(
    ! [A_656,B_657] :
      ( m1_subset_1('#skF_1'(A_656,B_657,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_656,k10_relat_1('#skF_5',B_657)) ) ),
    inference(resolution,[status(thm)],[c_3304,c_10])).

tff(c_3344,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2187,c_3321])).

tff(c_3365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2295,c_3344])).

tff(c_3366,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_4389,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3424,c_3366])).

tff(c_4424,plain,(
    ! [A_848,B_849,C_850] :
      ( r2_hidden(k4_tarski(A_848,'#skF_1'(A_848,B_849,C_850)),C_850)
      | ~ r2_hidden(A_848,k10_relat_1(C_850,B_849))
      | ~ v1_relat_1(C_850) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3367,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,(
    ! [F_115] :
      ( ~ r2_hidden(F_115,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_115),'#skF_5')
      | ~ m1_subset_1(F_115,'#skF_4')
      | r2_hidden('#skF_7','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4399,plain,(
    ! [F_115] :
      ( ~ r2_hidden(F_115,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_115),'#skF_5')
      | ~ m1_subset_1(F_115,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3367,c_42])).

tff(c_4428,plain,(
    ! [B_849] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_849,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_849,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_849))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4424,c_4399])).

tff(c_4487,plain,(
    ! [B_854] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_854,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_854,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_854)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4428])).

tff(c_4491,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_4487])).

tff(c_4494,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_4389,c_4491])).

tff(c_4901,plain,(
    ! [A_927,B_928,C_929,A_930] :
      ( r2_hidden(k4_tarski(A_927,'#skF_1'(A_927,B_928,C_929)),A_930)
      | ~ m1_subset_1(C_929,k1_zfmisc_1(A_930))
      | ~ r2_hidden(A_927,k10_relat_1(C_929,B_928))
      | ~ v1_relat_1(C_929) ) ),
    inference(resolution,[status(thm)],[c_4424,c_8])).

tff(c_5388,plain,(
    ! [C_992,A_991,B_988,D_989,C_990] :
      ( r2_hidden('#skF_1'(A_991,B_988,C_992),D_989)
      | ~ m1_subset_1(C_992,k1_zfmisc_1(k2_zfmisc_1(C_990,D_989)))
      | ~ r2_hidden(A_991,k10_relat_1(C_992,B_988))
      | ~ v1_relat_1(C_992) ) ),
    inference(resolution,[status(thm)],[c_4901,c_4])).

tff(c_5399,plain,(
    ! [A_991,B_988] :
      ( r2_hidden('#skF_1'(A_991,B_988,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_991,k10_relat_1('#skF_5',B_988))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_5388])).

tff(c_5406,plain,(
    ! [A_993,B_994] :
      ( r2_hidden('#skF_1'(A_993,B_994,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_993,k10_relat_1('#skF_5',B_994)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_5399])).

tff(c_5423,plain,(
    ! [A_995,B_996] :
      ( m1_subset_1('#skF_1'(A_995,B_996,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_995,k10_relat_1('#skF_5',B_996)) ) ),
    inference(resolution,[status(thm)],[c_5406,c_10])).

tff(c_5450,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4389,c_5423])).

tff(c_5468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4494,c_5450])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.39/2.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.39/2.27  
% 6.39/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.39/2.27  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 6.39/2.27  
% 6.39/2.27  %Foreground sorts:
% 6.39/2.27  
% 6.39/2.27  
% 6.39/2.27  %Background operators:
% 6.39/2.27  
% 6.39/2.27  
% 6.39/2.27  %Foreground operators:
% 6.39/2.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.39/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.39/2.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.39/2.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.39/2.27  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 6.39/2.27  tff('#skF_7', type, '#skF_7': $i).
% 6.39/2.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.39/2.27  tff('#skF_5', type, '#skF_5': $i).
% 6.39/2.27  tff('#skF_6', type, '#skF_6': $i).
% 6.39/2.27  tff('#skF_2', type, '#skF_2': $i).
% 6.39/2.27  tff('#skF_3', type, '#skF_3': $i).
% 6.39/2.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.39/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.39/2.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.39/2.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.39/2.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.39/2.27  tff('#skF_4', type, '#skF_4': $i).
% 6.39/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.39/2.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.39/2.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.39/2.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.39/2.27  
% 6.39/2.29  tff(f_96, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_relset_1)).
% 6.39/2.29  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.39/2.29  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 6.39/2.29  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 6.39/2.29  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 6.39/2.29  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 6.39/2.29  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 6.39/2.29  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 6.39/2.29  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.39/2.29  tff(c_54, plain, (![C_118, A_119, B_120]: (v1_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.39/2.29  tff(c_58, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_54])).
% 6.39/2.29  tff(c_3421, plain, (![A_690, B_691, C_692, D_693]: (k8_relset_1(A_690, B_691, C_692, D_693)=k10_relat_1(C_692, D_693) | ~m1_subset_1(C_692, k1_zfmisc_1(k2_zfmisc_1(A_690, B_691))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.39/2.29  tff(c_3424, plain, (![D_693]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_693)=k10_relat_1('#skF_5', D_693))), inference(resolution, [status(thm)], [c_30, c_3421])).
% 6.39/2.29  tff(c_2181, plain, (![A_488, B_489, C_490, D_491]: (k8_relset_1(A_488, B_489, C_490, D_491)=k10_relat_1(C_490, D_491) | ~m1_subset_1(C_490, k1_zfmisc_1(k2_zfmisc_1(A_488, B_489))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.39/2.29  tff(c_2184, plain, (![D_491]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_491)=k10_relat_1('#skF_5', D_491))), inference(resolution, [status(thm)], [c_30, c_2181])).
% 6.39/2.29  tff(c_844, plain, (![A_264, B_265, C_266, D_267]: (k8_relset_1(A_264, B_265, C_266, D_267)=k10_relat_1(C_266, D_267) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(A_264, B_265))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.39/2.29  tff(c_847, plain, (![D_267]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_267)=k10_relat_1('#skF_5', D_267))), inference(resolution, [status(thm)], [c_30, c_844])).
% 6.39/2.29  tff(c_52, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | m1_subset_1('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.39/2.29  tff(c_60, plain, (m1_subset_1('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 6.39/2.29  tff(c_44, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | r2_hidden('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.39/2.29  tff(c_59, plain, (r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 6.39/2.29  tff(c_48, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.39/2.29  tff(c_74, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(splitLeft, [status(thm)], [c_48])).
% 6.39/2.29  tff(c_227, plain, (![A_160, B_161, C_162, D_163]: (k8_relset_1(A_160, B_161, C_162, D_163)=k10_relat_1(C_162, D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.39/2.29  tff(c_234, plain, (![D_163]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_163)=k10_relat_1('#skF_5', D_163))), inference(resolution, [status(thm)], [c_30, c_227])).
% 6.39/2.29  tff(c_38, plain, (![F_115]: (~r2_hidden(F_115, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_115), '#skF_5') | ~m1_subset_1(F_115, '#skF_4') | ~r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.39/2.29  tff(c_276, plain, (![F_115]: (~r2_hidden(F_115, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_115), '#skF_5') | ~m1_subset_1(F_115, '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_38])).
% 6.39/2.29  tff(c_277, plain, (~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_276])).
% 6.39/2.29  tff(c_20, plain, (![B_18, C_19, A_17]: (r2_hidden(B_18, k2_relat_1(C_19)) | ~r2_hidden(k4_tarski(A_17, B_18), C_19) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.39/2.29  tff(c_77, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_20])).
% 6.39/2.29  tff(c_88, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_77])).
% 6.39/2.29  tff(c_341, plain, (![A_196, C_197, B_198, D_199]: (r2_hidden(A_196, k10_relat_1(C_197, B_198)) | ~r2_hidden(D_199, B_198) | ~r2_hidden(k4_tarski(A_196, D_199), C_197) | ~r2_hidden(D_199, k2_relat_1(C_197)) | ~v1_relat_1(C_197))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.39/2.29  tff(c_699, plain, (![A_243, C_244]: (r2_hidden(A_243, k10_relat_1(C_244, '#skF_3')) | ~r2_hidden(k4_tarski(A_243, '#skF_7'), C_244) | ~r2_hidden('#skF_7', k2_relat_1(C_244)) | ~v1_relat_1(C_244))), inference(resolution, [status(thm)], [c_59, c_341])).
% 6.39/2.29  tff(c_741, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~r2_hidden('#skF_7', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_74, c_699])).
% 6.39/2.29  tff(c_754, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_88, c_741])).
% 6.39/2.29  tff(c_756, plain, $false, inference(negUnitSimplification, [status(thm)], [c_277, c_754])).
% 6.39/2.29  tff(c_771, plain, (![F_245]: (~r2_hidden(F_245, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_245), '#skF_5') | ~m1_subset_1(F_245, '#skF_4'))), inference(splitRight, [status(thm)], [c_276])).
% 6.39/2.29  tff(c_778, plain, (~r2_hidden('#skF_7', '#skF_3') | ~m1_subset_1('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_74, c_771])).
% 6.39/2.29  tff(c_785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_59, c_778])).
% 6.39/2.29  tff(c_786, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_48])).
% 6.39/2.29  tff(c_850, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_847, c_786])).
% 6.39/2.29  tff(c_14, plain, (![A_11, B_12, C_13]: (r2_hidden('#skF_1'(A_11, B_12, C_13), B_12) | ~r2_hidden(A_11, k10_relat_1(C_13, B_12)) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.39/2.29  tff(c_16, plain, (![A_11, B_12, C_13]: (r2_hidden(k4_tarski(A_11, '#skF_1'(A_11, B_12, C_13)), C_13) | ~r2_hidden(A_11, k10_relat_1(C_13, B_12)) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.39/2.29  tff(c_787, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_48])).
% 6.39/2.29  tff(c_46, plain, (![F_115]: (~r2_hidden(F_115, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_115), '#skF_5') | ~m1_subset_1(F_115, '#skF_4') | r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.39/2.29  tff(c_905, plain, (![F_273]: (~r2_hidden(F_273, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_273), '#skF_5') | ~m1_subset_1(F_273, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_787, c_46])).
% 6.39/2.29  tff(c_909, plain, (![B_12]: (~r2_hidden('#skF_1'('#skF_6', B_12, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_12, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_12)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_905])).
% 6.39/2.29  tff(c_1198, plain, (![B_327]: (~r2_hidden('#skF_1'('#skF_6', B_327, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_327, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_327)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_909])).
% 6.39/2.29  tff(c_1206, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14, c_1198])).
% 6.39/2.29  tff(c_1212, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_850, c_1206])).
% 6.39/2.29  tff(c_873, plain, (![A_269, B_270, C_271]: (r2_hidden(k4_tarski(A_269, '#skF_1'(A_269, B_270, C_271)), C_271) | ~r2_hidden(A_269, k10_relat_1(C_271, B_270)) | ~v1_relat_1(C_271))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.39/2.29  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.39/2.29  tff(c_1319, plain, (![A_350, B_351, C_352, A_353]: (r2_hidden(k4_tarski(A_350, '#skF_1'(A_350, B_351, C_352)), A_353) | ~m1_subset_1(C_352, k1_zfmisc_1(A_353)) | ~r2_hidden(A_350, k10_relat_1(C_352, B_351)) | ~v1_relat_1(C_352))), inference(resolution, [status(thm)], [c_873, c_8])).
% 6.39/2.29  tff(c_4, plain, (![B_2, D_4, A_1, C_3]: (r2_hidden(B_2, D_4) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.39/2.29  tff(c_1855, plain, (![D_416, B_414, C_413, A_415, C_417]: (r2_hidden('#skF_1'(A_415, B_414, C_413), D_416) | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(C_417, D_416))) | ~r2_hidden(A_415, k10_relat_1(C_413, B_414)) | ~v1_relat_1(C_413))), inference(resolution, [status(thm)], [c_1319, c_4])).
% 6.39/2.29  tff(c_1863, plain, (![A_415, B_414]: (r2_hidden('#skF_1'(A_415, B_414, '#skF_5'), '#skF_4') | ~r2_hidden(A_415, k10_relat_1('#skF_5', B_414)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_1855])).
% 6.39/2.29  tff(c_1933, plain, (![A_423, B_424]: (r2_hidden('#skF_1'(A_423, B_424, '#skF_5'), '#skF_4') | ~r2_hidden(A_423, k10_relat_1('#skF_5', B_424)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1863])).
% 6.39/2.29  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.39/2.29  tff(c_1950, plain, (![A_425, B_426]: (m1_subset_1('#skF_1'(A_425, B_426, '#skF_5'), '#skF_4') | ~r2_hidden(A_425, k10_relat_1('#skF_5', B_426)))), inference(resolution, [status(thm)], [c_1933, c_10])).
% 6.39/2.29  tff(c_1977, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_850, c_1950])).
% 6.39/2.29  tff(c_1995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1212, c_1977])).
% 6.39/2.29  tff(c_1997, plain, (~m1_subset_1('#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 6.39/2.29  tff(c_2002, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(splitLeft, [status(thm)], [c_48])).
% 6.39/2.29  tff(c_2013, plain, (![C_435, A_436, B_437]: (r2_hidden(C_435, A_436) | ~r2_hidden(C_435, B_437) | ~m1_subset_1(B_437, k1_zfmisc_1(A_436)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.39/2.29  tff(c_2032, plain, (![A_440]: (r2_hidden(k4_tarski('#skF_6', '#skF_7'), A_440) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_440)))), inference(resolution, [status(thm)], [c_2002, c_2013])).
% 6.39/2.29  tff(c_2097, plain, (![D_449, C_450]: (r2_hidden('#skF_7', D_449) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(C_450, D_449))))), inference(resolution, [status(thm)], [c_2032, c_4])).
% 6.39/2.29  tff(c_2101, plain, (r2_hidden('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_2097])).
% 6.39/2.29  tff(c_2106, plain, (m1_subset_1('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_2101, c_10])).
% 6.39/2.29  tff(c_2111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1997, c_2106])).
% 6.39/2.29  tff(c_2112, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_48])).
% 6.39/2.29  tff(c_2187, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2184, c_2112])).
% 6.39/2.29  tff(c_2197, plain, (![A_493, B_494, C_495]: (r2_hidden(k4_tarski(A_493, '#skF_1'(A_493, B_494, C_495)), C_495) | ~r2_hidden(A_493, k10_relat_1(C_495, B_494)) | ~v1_relat_1(C_495))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.39/2.29  tff(c_50, plain, (![F_115]: (~r2_hidden(F_115, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_115), '#skF_5') | ~m1_subset_1(F_115, '#skF_4') | m1_subset_1('#skF_7', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.39/2.29  tff(c_2119, plain, (![F_115]: (~r2_hidden(F_115, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_115), '#skF_5') | ~m1_subset_1(F_115, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1997, c_50])).
% 6.39/2.29  tff(c_2220, plain, (![B_494]: (~r2_hidden('#skF_1'('#skF_6', B_494, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_494, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_494)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_2197, c_2119])).
% 6.39/2.29  tff(c_2288, plain, (![B_508]: (~r2_hidden('#skF_1'('#skF_6', B_508, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_508, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_508)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2220])).
% 6.39/2.29  tff(c_2292, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14, c_2288])).
% 6.39/2.29  tff(c_2295, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2187, c_2292])).
% 6.39/2.29  tff(c_2767, plain, (![A_585, B_586, C_587, A_588]: (r2_hidden(k4_tarski(A_585, '#skF_1'(A_585, B_586, C_587)), A_588) | ~m1_subset_1(C_587, k1_zfmisc_1(A_588)) | ~r2_hidden(A_585, k10_relat_1(C_587, B_586)) | ~v1_relat_1(C_587))), inference(resolution, [status(thm)], [c_2197, c_8])).
% 6.39/2.29  tff(c_3286, plain, (![C_652, B_653, C_651, A_649, D_650]: (r2_hidden('#skF_1'(A_649, B_653, C_651), D_650) | ~m1_subset_1(C_651, k1_zfmisc_1(k2_zfmisc_1(C_652, D_650))) | ~r2_hidden(A_649, k10_relat_1(C_651, B_653)) | ~v1_relat_1(C_651))), inference(resolution, [status(thm)], [c_2767, c_4])).
% 6.39/2.29  tff(c_3297, plain, (![A_649, B_653]: (r2_hidden('#skF_1'(A_649, B_653, '#skF_5'), '#skF_4') | ~r2_hidden(A_649, k10_relat_1('#skF_5', B_653)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_3286])).
% 6.39/2.29  tff(c_3304, plain, (![A_654, B_655]: (r2_hidden('#skF_1'(A_654, B_655, '#skF_5'), '#skF_4') | ~r2_hidden(A_654, k10_relat_1('#skF_5', B_655)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_3297])).
% 6.39/2.29  tff(c_3321, plain, (![A_656, B_657]: (m1_subset_1('#skF_1'(A_656, B_657, '#skF_5'), '#skF_4') | ~r2_hidden(A_656, k10_relat_1('#skF_5', B_657)))), inference(resolution, [status(thm)], [c_3304, c_10])).
% 6.39/2.29  tff(c_3344, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_2187, c_3321])).
% 6.39/2.29  tff(c_3365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2295, c_3344])).
% 6.39/2.29  tff(c_3366, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_44])).
% 6.39/2.29  tff(c_4389, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3424, c_3366])).
% 6.39/2.29  tff(c_4424, plain, (![A_848, B_849, C_850]: (r2_hidden(k4_tarski(A_848, '#skF_1'(A_848, B_849, C_850)), C_850) | ~r2_hidden(A_848, k10_relat_1(C_850, B_849)) | ~v1_relat_1(C_850))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.39/2.29  tff(c_3367, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 6.39/2.29  tff(c_42, plain, (![F_115]: (~r2_hidden(F_115, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_115), '#skF_5') | ~m1_subset_1(F_115, '#skF_4') | r2_hidden('#skF_7', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.39/2.29  tff(c_4399, plain, (![F_115]: (~r2_hidden(F_115, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_115), '#skF_5') | ~m1_subset_1(F_115, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_3367, c_42])).
% 6.39/2.29  tff(c_4428, plain, (![B_849]: (~r2_hidden('#skF_1'('#skF_6', B_849, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_849, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_849)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_4424, c_4399])).
% 6.39/2.29  tff(c_4487, plain, (![B_854]: (~r2_hidden('#skF_1'('#skF_6', B_854, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_854, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_854)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_4428])).
% 6.39/2.29  tff(c_4491, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_14, c_4487])).
% 6.39/2.29  tff(c_4494, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_4389, c_4491])).
% 6.39/2.29  tff(c_4901, plain, (![A_927, B_928, C_929, A_930]: (r2_hidden(k4_tarski(A_927, '#skF_1'(A_927, B_928, C_929)), A_930) | ~m1_subset_1(C_929, k1_zfmisc_1(A_930)) | ~r2_hidden(A_927, k10_relat_1(C_929, B_928)) | ~v1_relat_1(C_929))), inference(resolution, [status(thm)], [c_4424, c_8])).
% 6.39/2.29  tff(c_5388, plain, (![C_992, A_991, B_988, D_989, C_990]: (r2_hidden('#skF_1'(A_991, B_988, C_992), D_989) | ~m1_subset_1(C_992, k1_zfmisc_1(k2_zfmisc_1(C_990, D_989))) | ~r2_hidden(A_991, k10_relat_1(C_992, B_988)) | ~v1_relat_1(C_992))), inference(resolution, [status(thm)], [c_4901, c_4])).
% 6.39/2.29  tff(c_5399, plain, (![A_991, B_988]: (r2_hidden('#skF_1'(A_991, B_988, '#skF_5'), '#skF_4') | ~r2_hidden(A_991, k10_relat_1('#skF_5', B_988)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_5388])).
% 6.39/2.29  tff(c_5406, plain, (![A_993, B_994]: (r2_hidden('#skF_1'(A_993, B_994, '#skF_5'), '#skF_4') | ~r2_hidden(A_993, k10_relat_1('#skF_5', B_994)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_5399])).
% 6.39/2.29  tff(c_5423, plain, (![A_995, B_996]: (m1_subset_1('#skF_1'(A_995, B_996, '#skF_5'), '#skF_4') | ~r2_hidden(A_995, k10_relat_1('#skF_5', B_996)))), inference(resolution, [status(thm)], [c_5406, c_10])).
% 6.39/2.29  tff(c_5450, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_4389, c_5423])).
% 6.39/2.29  tff(c_5468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4494, c_5450])).
% 6.39/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.39/2.29  
% 6.39/2.29  Inference rules
% 6.39/2.29  ----------------------
% 6.39/2.29  #Ref     : 0
% 6.39/2.29  #Sup     : 1229
% 6.39/2.29  #Fact    : 0
% 6.39/2.29  #Define  : 0
% 6.39/2.29  #Split   : 21
% 6.39/2.29  #Chain   : 0
% 6.39/2.29  #Close   : 0
% 6.39/2.29  
% 6.39/2.29  Ordering : KBO
% 6.39/2.29  
% 6.39/2.29  Simplification rules
% 6.39/2.29  ----------------------
% 6.39/2.29  #Subsume      : 75
% 6.39/2.29  #Demod        : 122
% 6.39/2.29  #Tautology    : 41
% 6.39/2.29  #SimpNegUnit  : 12
% 6.39/2.29  #BackRed      : 12
% 6.39/2.29  
% 6.39/2.29  #Partial instantiations: 0
% 6.39/2.30  #Strategies tried      : 1
% 6.39/2.30  
% 6.39/2.30  Timing (in seconds)
% 6.39/2.30  ----------------------
% 6.59/2.30  Preprocessing        : 0.31
% 6.59/2.30  Parsing              : 0.15
% 6.59/2.30  CNF conversion       : 0.03
% 6.59/2.30  Main loop            : 1.16
% 6.59/2.30  Inferencing          : 0.45
% 6.59/2.30  Reduction            : 0.31
% 6.59/2.30  Demodulation         : 0.20
% 6.59/2.30  BG Simplification    : 0.05
% 6.59/2.30  Subsumption          : 0.24
% 6.59/2.30  Abstraction          : 0.05
% 6.59/2.30  MUC search           : 0.00
% 6.59/2.30  Cooper               : 0.00
% 6.59/2.30  Total                : 1.51
% 6.59/2.30  Index Insertion      : 0.00
% 6.59/2.30  Index Deletion       : 0.00
% 6.59/2.30  Index Matching       : 0.00
% 6.59/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
