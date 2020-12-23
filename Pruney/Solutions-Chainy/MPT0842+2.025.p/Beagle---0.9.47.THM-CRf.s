%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:39 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 330 expanded)
%              Number of leaves         :   34 ( 125 expanded)
%              Depth                    :    9
%              Number of atoms          :  240 ( 945 expanded)
%              Number of equality atoms :   19 (  38 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_48,axiom,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_59,axiom,(
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

tff(c_18,plain,(
    ! [A_26,B_27] : v1_relat_1(k2_zfmisc_1(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_36,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_60,plain,(
    ! [B_135,A_136] :
      ( v1_relat_1(B_135)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(A_136))
      | ~ v1_relat_1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_63,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_36,c_60])).

tff(c_66,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_63])).

tff(c_1117,plain,(
    ! [A_333,B_334,C_335,D_336] :
      ( k8_relset_1(A_333,B_334,C_335,D_336) = k10_relat_1(C_335,D_336)
      | ~ m1_subset_1(C_335,k1_zfmisc_1(k2_zfmisc_1(A_333,B_334))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1124,plain,(
    ! [D_336] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_336) = k10_relat_1('#skF_9',D_336) ),
    inference(resolution,[status(thm)],[c_36,c_1117])).

tff(c_869,plain,(
    ! [A_288,B_289,C_290,D_291] :
      ( k8_relset_1(A_288,B_289,C_290,D_291) = k10_relat_1(C_290,D_291)
      | ~ m1_subset_1(C_290,k1_zfmisc_1(k2_zfmisc_1(A_288,B_289))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_876,plain,(
    ! [D_291] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_291) = k10_relat_1('#skF_9',D_291) ),
    inference(resolution,[status(thm)],[c_36,c_869])).

tff(c_506,plain,(
    ! [A_219,B_220,C_221,D_222] :
      ( k8_relset_1(A_219,B_220,C_221,D_222) = k10_relat_1(C_221,D_222)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_513,plain,(
    ! [D_222] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_222) = k10_relat_1('#skF_9',D_222) ),
    inference(resolution,[status(thm)],[c_36,c_506])).

tff(c_58,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_69,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_50,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_68,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_54,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_75,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_156,plain,(
    ! [A_161,B_162,C_163,D_164] :
      ( k8_relset_1(A_161,B_162,C_163,D_164) = k10_relat_1(C_163,D_164)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_163,plain,(
    ! [D_164] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_164) = k10_relat_1('#skF_9',D_164) ),
    inference(resolution,[status(thm)],[c_36,c_156])).

tff(c_44,plain,(
    ! [F_132] :
      ( ~ r2_hidden(F_132,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_132),'#skF_9')
      | ~ m1_subset_1(F_132,'#skF_8')
      | ~ r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_331,plain,(
    ! [F_132] :
      ( ~ r2_hidden(F_132,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_132),'#skF_9')
      | ~ m1_subset_1(F_132,'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_44])).

tff(c_332,plain,(
    ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_8,plain,(
    ! [C_22,A_7,D_25] :
      ( r2_hidden(C_22,k2_relat_1(A_7))
      | ~ r2_hidden(k4_tarski(D_25,C_22),A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_79,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_75,c_8])).

tff(c_353,plain,(
    ! [A_192,C_193,B_194,D_195] :
      ( r2_hidden(A_192,k10_relat_1(C_193,B_194))
      | ~ r2_hidden(D_195,B_194)
      | ~ r2_hidden(k4_tarski(A_192,D_195),C_193)
      | ~ r2_hidden(D_195,k2_relat_1(C_193))
      | ~ v1_relat_1(C_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_393,plain,(
    ! [A_196,C_197] :
      ( r2_hidden(A_196,k10_relat_1(C_197,'#skF_7'))
      | ~ r2_hidden(k4_tarski(A_196,'#skF_11'),C_197)
      | ~ r2_hidden('#skF_11',k2_relat_1(C_197))
      | ~ v1_relat_1(C_197) ) ),
    inference(resolution,[status(thm)],[c_68,c_353])).

tff(c_400,plain,
    ( r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_75,c_393])).

tff(c_404,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_79,c_400])).

tff(c_406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_332,c_404])).

tff(c_418,plain,(
    ! [F_201] :
      ( ~ r2_hidden(F_201,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_201),'#skF_9')
      | ~ m1_subset_1(F_201,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_425,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_75,c_418])).

tff(c_432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_68,c_425])).

tff(c_433,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_514,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_433])).

tff(c_524,plain,(
    ! [A_224,B_225,C_226] :
      ( r2_hidden('#skF_5'(A_224,B_225,C_226),k2_relat_1(C_226))
      | ~ r2_hidden(A_224,k10_relat_1(C_226,B_225))
      | ~ v1_relat_1(C_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_436,plain,(
    ! [A_202,B_203,C_204] :
      ( k2_relset_1(A_202,B_203,C_204) = k2_relat_1(C_204)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_440,plain,(
    k2_relset_1('#skF_6','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_436])).

tff(c_452,plain,(
    ! [A_212,B_213,C_214] :
      ( m1_subset_1(k2_relset_1(A_212,B_213,C_214),k1_zfmisc_1(B_213))
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_212,B_213))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_464,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_452])).

tff(c_469,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_464])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_475,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_8')
      | ~ r2_hidden(A_1,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_469,c_2])).

tff(c_528,plain,(
    ! [A_224,B_225] :
      ( m1_subset_1('#skF_5'(A_224,B_225,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_224,k10_relat_1('#skF_9',B_225))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_524,c_475])).

tff(c_532,plain,(
    ! [A_227,B_228] :
      ( m1_subset_1('#skF_5'(A_227,B_228,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_227,k10_relat_1('#skF_9',B_228)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_528])).

tff(c_548,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_514,c_532])).

tff(c_22,plain,(
    ! [A_28,B_29,C_30] :
      ( r2_hidden('#skF_5'(A_28,B_29,C_30),B_29)
      | ~ r2_hidden(A_28,k10_relat_1(C_30,B_29))
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_555,plain,(
    ! [A_233,B_234,C_235] :
      ( r2_hidden(k4_tarski(A_233,'#skF_5'(A_233,B_234,C_235)),C_235)
      | ~ r2_hidden(A_233,k10_relat_1(C_235,B_234))
      | ~ v1_relat_1(C_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_434,plain,(
    ~ r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [F_132] :
      ( ~ r2_hidden(F_132,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_132),'#skF_9')
      | ~ m1_subset_1(F_132,'#skF_8')
      | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_553,plain,(
    ! [F_132] :
      ( ~ r2_hidden(F_132,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_132),'#skF_9')
      | ~ m1_subset_1(F_132,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_434,c_52])).

tff(c_559,plain,(
    ! [B_234] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_234,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_234,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_234))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_555,c_553])).

tff(c_693,plain,(
    ! [B_248] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_248,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_248,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_248)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_559])).

tff(c_697,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_22,c_693])).

tff(c_701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_514,c_548,c_697])).

tff(c_703,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_704,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_708,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_704,c_8])).

tff(c_713,plain,(
    ! [A_252,B_253,C_254] :
      ( k2_relset_1(A_252,B_253,C_254) = k2_relat_1(C_254)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_717,plain,(
    k2_relset_1('#skF_6','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_713])).

tff(c_723,plain,(
    ! [A_256,B_257,C_258] :
      ( m1_subset_1(k2_relset_1(A_256,B_257,C_258),k1_zfmisc_1(B_257))
      | ~ m1_subset_1(C_258,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_735,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_723])).

tff(c_740,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_735])).

tff(c_757,plain,(
    ! [A_260] :
      ( m1_subset_1(A_260,'#skF_8')
      | ~ r2_hidden(A_260,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_740,c_2])).

tff(c_760,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_708,c_757])).

tff(c_764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_703,c_760])).

tff(c_765,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_877,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_876,c_765])).

tff(c_845,plain,(
    ! [A_283,B_284,C_285] :
      ( r2_hidden('#skF_5'(A_283,B_284,C_285),k2_relat_1(C_285))
      | ~ r2_hidden(A_283,k10_relat_1(C_285,B_284))
      | ~ v1_relat_1(C_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_775,plain,(
    ! [A_266,B_267,C_268] :
      ( k2_relset_1(A_266,B_267,C_268) = k2_relat_1(C_268)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_266,B_267))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_779,plain,(
    k2_relset_1('#skF_6','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_775])).

tff(c_785,plain,(
    ! [A_272,B_273,C_274] :
      ( m1_subset_1(k2_relset_1(A_272,B_273,C_274),k1_zfmisc_1(B_273))
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_797,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_779,c_785])).

tff(c_802,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_797])).

tff(c_809,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_8')
      | ~ r2_hidden(A_1,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_802,c_2])).

tff(c_849,plain,(
    ! [A_283,B_284] :
      ( m1_subset_1('#skF_5'(A_283,B_284,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_283,k10_relat_1('#skF_9',B_284))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_845,c_809])).

tff(c_852,plain,(
    ! [A_283,B_284] :
      ( m1_subset_1('#skF_5'(A_283,B_284,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_283,k10_relat_1('#skF_9',B_284)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_849])).

tff(c_890,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_877,c_852])).

tff(c_892,plain,(
    ! [A_293,B_294,C_295] :
      ( r2_hidden(k4_tarski(A_293,'#skF_5'(A_293,B_294,C_295)),C_295)
      | ~ r2_hidden(A_293,k10_relat_1(C_295,B_294))
      | ~ v1_relat_1(C_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_56,plain,(
    ! [F_132] :
      ( ~ r2_hidden(F_132,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_132),'#skF_9')
      | ~ m1_subset_1(F_132,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_772,plain,(
    ! [F_132] :
      ( ~ r2_hidden(F_132,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_132),'#skF_9')
      | ~ m1_subset_1(F_132,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_703,c_56])).

tff(c_904,plain,(
    ! [B_294] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_294,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_294,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_294))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_892,c_772])).

tff(c_1029,plain,(
    ! [B_311] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_311,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_311,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_311)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_904])).

tff(c_1033,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_22,c_1029])).

tff(c_1037,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_877,c_890,c_1033])).

tff(c_1038,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1127,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1124,c_1038])).

tff(c_1137,plain,(
    ! [A_339,B_340,C_341] :
      ( r2_hidden('#skF_5'(A_339,B_340,C_341),k2_relat_1(C_341))
      | ~ r2_hidden(A_339,k10_relat_1(C_341,B_340))
      | ~ v1_relat_1(C_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1046,plain,(
    ! [A_316,B_317,C_318] :
      ( k2_relset_1(A_316,B_317,C_318) = k2_relat_1(C_318)
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(A_316,B_317))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1050,plain,(
    k2_relset_1('#skF_6','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_1046])).

tff(c_1056,plain,(
    ! [A_319,B_320,C_321] :
      ( m1_subset_1(k2_relset_1(A_319,B_320,C_321),k1_zfmisc_1(B_320))
      | ~ m1_subset_1(C_321,k1_zfmisc_1(k2_zfmisc_1(A_319,B_320))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1068,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1050,c_1056])).

tff(c_1073,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1068])).

tff(c_1080,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_8')
      | ~ r2_hidden(A_1,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_1073,c_2])).

tff(c_1141,plain,(
    ! [A_339,B_340] :
      ( m1_subset_1('#skF_5'(A_339,B_340,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_339,k10_relat_1('#skF_9',B_340))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1137,c_1080])).

tff(c_1145,plain,(
    ! [A_342,B_343] :
      ( m1_subset_1('#skF_5'(A_342,B_343,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_342,k10_relat_1('#skF_9',B_343)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1141])).

tff(c_1161,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_1127,c_1145])).

tff(c_1166,plain,(
    ! [A_347,B_348,C_349] :
      ( r2_hidden(k4_tarski(A_347,'#skF_5'(A_347,B_348,C_349)),C_349)
      | ~ r2_hidden(A_347,k10_relat_1(C_349,B_348))
      | ~ v1_relat_1(C_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1039,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [F_132] :
      ( ~ r2_hidden(F_132,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_132),'#skF_9')
      | ~ m1_subset_1(F_132,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1125,plain,(
    ! [F_132] :
      ( ~ r2_hidden(F_132,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_132),'#skF_9')
      | ~ m1_subset_1(F_132,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1039,c_48])).

tff(c_1174,plain,(
    ! [B_348] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_348,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_348,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_348))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1166,c_1125])).

tff(c_1302,plain,(
    ! [B_362] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_362,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_362,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_362)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1174])).

tff(c_1306,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_22,c_1302])).

tff(c_1310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1127,c_1161,c_1306])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:06:46 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.58  
% 3.34/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.58  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 3.34/1.58  
% 3.34/1.58  %Foreground sorts:
% 3.34/1.58  
% 3.34/1.58  
% 3.34/1.58  %Background operators:
% 3.34/1.58  
% 3.34/1.58  
% 3.34/1.58  %Foreground operators:
% 3.34/1.58  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.34/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.34/1.58  tff('#skF_11', type, '#skF_11': $i).
% 3.34/1.58  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.34/1.58  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.34/1.58  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.34/1.58  tff('#skF_7', type, '#skF_7': $i).
% 3.34/1.58  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.34/1.58  tff('#skF_10', type, '#skF_10': $i).
% 3.34/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.34/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.34/1.58  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.34/1.58  tff('#skF_9', type, '#skF_9': $i).
% 3.34/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.34/1.58  tff('#skF_8', type, '#skF_8': $i).
% 3.34/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.58  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.34/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.34/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.34/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.34/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.34/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.34/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.34/1.58  
% 3.34/1.60  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.34/1.60  tff(f_98, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_relset_1)).
% 3.34/1.60  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.34/1.60  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.34/1.60  tff(f_46, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 3.34/1.60  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 3.34/1.60  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.34/1.60  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.34/1.60  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.34/1.60  tff(c_18, plain, (![A_26, B_27]: (v1_relat_1(k2_zfmisc_1(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.34/1.60  tff(c_36, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.34/1.60  tff(c_60, plain, (![B_135, A_136]: (v1_relat_1(B_135) | ~m1_subset_1(B_135, k1_zfmisc_1(A_136)) | ~v1_relat_1(A_136))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.34/1.60  tff(c_63, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_36, c_60])).
% 3.34/1.60  tff(c_66, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_63])).
% 3.34/1.60  tff(c_1117, plain, (![A_333, B_334, C_335, D_336]: (k8_relset_1(A_333, B_334, C_335, D_336)=k10_relat_1(C_335, D_336) | ~m1_subset_1(C_335, k1_zfmisc_1(k2_zfmisc_1(A_333, B_334))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.34/1.60  tff(c_1124, plain, (![D_336]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_336)=k10_relat_1('#skF_9', D_336))), inference(resolution, [status(thm)], [c_36, c_1117])).
% 3.34/1.60  tff(c_869, plain, (![A_288, B_289, C_290, D_291]: (k8_relset_1(A_288, B_289, C_290, D_291)=k10_relat_1(C_290, D_291) | ~m1_subset_1(C_290, k1_zfmisc_1(k2_zfmisc_1(A_288, B_289))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.34/1.60  tff(c_876, plain, (![D_291]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_291)=k10_relat_1('#skF_9', D_291))), inference(resolution, [status(thm)], [c_36, c_869])).
% 3.34/1.60  tff(c_506, plain, (![A_219, B_220, C_221, D_222]: (k8_relset_1(A_219, B_220, C_221, D_222)=k10_relat_1(C_221, D_222) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.34/1.60  tff(c_513, plain, (![D_222]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_222)=k10_relat_1('#skF_9', D_222))), inference(resolution, [status(thm)], [c_36, c_506])).
% 3.34/1.60  tff(c_58, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.34/1.60  tff(c_69, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_58])).
% 3.34/1.60  tff(c_50, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.34/1.60  tff(c_68, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_50])).
% 3.34/1.60  tff(c_54, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.34/1.60  tff(c_75, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitLeft, [status(thm)], [c_54])).
% 3.34/1.60  tff(c_156, plain, (![A_161, B_162, C_163, D_164]: (k8_relset_1(A_161, B_162, C_163, D_164)=k10_relat_1(C_163, D_164) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.34/1.60  tff(c_163, plain, (![D_164]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_164)=k10_relat_1('#skF_9', D_164))), inference(resolution, [status(thm)], [c_36, c_156])).
% 3.34/1.60  tff(c_44, plain, (![F_132]: (~r2_hidden(F_132, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_132), '#skF_9') | ~m1_subset_1(F_132, '#skF_8') | ~r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.34/1.60  tff(c_331, plain, (![F_132]: (~r2_hidden(F_132, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_132), '#skF_9') | ~m1_subset_1(F_132, '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_44])).
% 3.34/1.60  tff(c_332, plain, (~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(splitLeft, [status(thm)], [c_331])).
% 3.34/1.60  tff(c_8, plain, (![C_22, A_7, D_25]: (r2_hidden(C_22, k2_relat_1(A_7)) | ~r2_hidden(k4_tarski(D_25, C_22), A_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.34/1.60  tff(c_79, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_75, c_8])).
% 3.34/1.60  tff(c_353, plain, (![A_192, C_193, B_194, D_195]: (r2_hidden(A_192, k10_relat_1(C_193, B_194)) | ~r2_hidden(D_195, B_194) | ~r2_hidden(k4_tarski(A_192, D_195), C_193) | ~r2_hidden(D_195, k2_relat_1(C_193)) | ~v1_relat_1(C_193))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.34/1.60  tff(c_393, plain, (![A_196, C_197]: (r2_hidden(A_196, k10_relat_1(C_197, '#skF_7')) | ~r2_hidden(k4_tarski(A_196, '#skF_11'), C_197) | ~r2_hidden('#skF_11', k2_relat_1(C_197)) | ~v1_relat_1(C_197))), inference(resolution, [status(thm)], [c_68, c_353])).
% 3.34/1.60  tff(c_400, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~r2_hidden('#skF_11', k2_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_75, c_393])).
% 3.34/1.60  tff(c_404, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_79, c_400])).
% 3.34/1.60  tff(c_406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_332, c_404])).
% 3.34/1.60  tff(c_418, plain, (![F_201]: (~r2_hidden(F_201, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_201), '#skF_9') | ~m1_subset_1(F_201, '#skF_8'))), inference(splitRight, [status(thm)], [c_331])).
% 3.34/1.60  tff(c_425, plain, (~r2_hidden('#skF_11', '#skF_7') | ~m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_75, c_418])).
% 3.34/1.60  tff(c_432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_68, c_425])).
% 3.34/1.60  tff(c_433, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_54])).
% 3.34/1.60  tff(c_514, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_513, c_433])).
% 3.34/1.60  tff(c_524, plain, (![A_224, B_225, C_226]: (r2_hidden('#skF_5'(A_224, B_225, C_226), k2_relat_1(C_226)) | ~r2_hidden(A_224, k10_relat_1(C_226, B_225)) | ~v1_relat_1(C_226))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.34/1.60  tff(c_436, plain, (![A_202, B_203, C_204]: (k2_relset_1(A_202, B_203, C_204)=k2_relat_1(C_204) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.34/1.60  tff(c_440, plain, (k2_relset_1('#skF_6', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_36, c_436])).
% 3.34/1.60  tff(c_452, plain, (![A_212, B_213, C_214]: (m1_subset_1(k2_relset_1(A_212, B_213, C_214), k1_zfmisc_1(B_213)) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_212, B_213))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.34/1.60  tff(c_464, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_440, c_452])).
% 3.34/1.60  tff(c_469, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_464])).
% 3.34/1.60  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.34/1.60  tff(c_475, plain, (![A_1]: (m1_subset_1(A_1, '#skF_8') | ~r2_hidden(A_1, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_469, c_2])).
% 3.34/1.60  tff(c_528, plain, (![A_224, B_225]: (m1_subset_1('#skF_5'(A_224, B_225, '#skF_9'), '#skF_8') | ~r2_hidden(A_224, k10_relat_1('#skF_9', B_225)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_524, c_475])).
% 3.34/1.60  tff(c_532, plain, (![A_227, B_228]: (m1_subset_1('#skF_5'(A_227, B_228, '#skF_9'), '#skF_8') | ~r2_hidden(A_227, k10_relat_1('#skF_9', B_228)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_528])).
% 3.34/1.60  tff(c_548, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_514, c_532])).
% 3.34/1.60  tff(c_22, plain, (![A_28, B_29, C_30]: (r2_hidden('#skF_5'(A_28, B_29, C_30), B_29) | ~r2_hidden(A_28, k10_relat_1(C_30, B_29)) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.34/1.60  tff(c_555, plain, (![A_233, B_234, C_235]: (r2_hidden(k4_tarski(A_233, '#skF_5'(A_233, B_234, C_235)), C_235) | ~r2_hidden(A_233, k10_relat_1(C_235, B_234)) | ~v1_relat_1(C_235))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.34/1.60  tff(c_434, plain, (~r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitRight, [status(thm)], [c_54])).
% 3.34/1.60  tff(c_52, plain, (![F_132]: (~r2_hidden(F_132, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_132), '#skF_9') | ~m1_subset_1(F_132, '#skF_8') | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.34/1.60  tff(c_553, plain, (![F_132]: (~r2_hidden(F_132, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_132), '#skF_9') | ~m1_subset_1(F_132, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_434, c_52])).
% 3.34/1.60  tff(c_559, plain, (![B_234]: (~r2_hidden('#skF_5'('#skF_10', B_234, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_234, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_234)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_555, c_553])).
% 3.34/1.60  tff(c_693, plain, (![B_248]: (~r2_hidden('#skF_5'('#skF_10', B_248, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_248, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_248)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_559])).
% 3.34/1.60  tff(c_697, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_22, c_693])).
% 3.34/1.60  tff(c_701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_514, c_548, c_697])).
% 3.34/1.60  tff(c_703, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_58])).
% 3.34/1.60  tff(c_704, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitLeft, [status(thm)], [c_54])).
% 3.34/1.60  tff(c_708, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_704, c_8])).
% 3.34/1.60  tff(c_713, plain, (![A_252, B_253, C_254]: (k2_relset_1(A_252, B_253, C_254)=k2_relat_1(C_254) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_252, B_253))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.34/1.60  tff(c_717, plain, (k2_relset_1('#skF_6', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_36, c_713])).
% 3.34/1.60  tff(c_723, plain, (![A_256, B_257, C_258]: (m1_subset_1(k2_relset_1(A_256, B_257, C_258), k1_zfmisc_1(B_257)) | ~m1_subset_1(C_258, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.34/1.60  tff(c_735, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_717, c_723])).
% 3.34/1.60  tff(c_740, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_735])).
% 3.34/1.60  tff(c_757, plain, (![A_260]: (m1_subset_1(A_260, '#skF_8') | ~r2_hidden(A_260, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_740, c_2])).
% 3.34/1.60  tff(c_760, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_708, c_757])).
% 3.34/1.60  tff(c_764, plain, $false, inference(negUnitSimplification, [status(thm)], [c_703, c_760])).
% 3.34/1.60  tff(c_765, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_54])).
% 3.34/1.60  tff(c_877, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_876, c_765])).
% 3.34/1.60  tff(c_845, plain, (![A_283, B_284, C_285]: (r2_hidden('#skF_5'(A_283, B_284, C_285), k2_relat_1(C_285)) | ~r2_hidden(A_283, k10_relat_1(C_285, B_284)) | ~v1_relat_1(C_285))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.34/1.60  tff(c_775, plain, (![A_266, B_267, C_268]: (k2_relset_1(A_266, B_267, C_268)=k2_relat_1(C_268) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(A_266, B_267))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.34/1.60  tff(c_779, plain, (k2_relset_1('#skF_6', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_36, c_775])).
% 3.34/1.60  tff(c_785, plain, (![A_272, B_273, C_274]: (m1_subset_1(k2_relset_1(A_272, B_273, C_274), k1_zfmisc_1(B_273)) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.34/1.60  tff(c_797, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_779, c_785])).
% 3.34/1.60  tff(c_802, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_797])).
% 3.34/1.60  tff(c_809, plain, (![A_1]: (m1_subset_1(A_1, '#skF_8') | ~r2_hidden(A_1, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_802, c_2])).
% 3.34/1.60  tff(c_849, plain, (![A_283, B_284]: (m1_subset_1('#skF_5'(A_283, B_284, '#skF_9'), '#skF_8') | ~r2_hidden(A_283, k10_relat_1('#skF_9', B_284)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_845, c_809])).
% 3.34/1.60  tff(c_852, plain, (![A_283, B_284]: (m1_subset_1('#skF_5'(A_283, B_284, '#skF_9'), '#skF_8') | ~r2_hidden(A_283, k10_relat_1('#skF_9', B_284)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_849])).
% 3.34/1.60  tff(c_890, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_877, c_852])).
% 3.34/1.60  tff(c_892, plain, (![A_293, B_294, C_295]: (r2_hidden(k4_tarski(A_293, '#skF_5'(A_293, B_294, C_295)), C_295) | ~r2_hidden(A_293, k10_relat_1(C_295, B_294)) | ~v1_relat_1(C_295))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.34/1.60  tff(c_56, plain, (![F_132]: (~r2_hidden(F_132, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_132), '#skF_9') | ~m1_subset_1(F_132, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.34/1.60  tff(c_772, plain, (![F_132]: (~r2_hidden(F_132, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_132), '#skF_9') | ~m1_subset_1(F_132, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_703, c_56])).
% 3.34/1.60  tff(c_904, plain, (![B_294]: (~r2_hidden('#skF_5'('#skF_10', B_294, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_294, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_294)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_892, c_772])).
% 3.34/1.60  tff(c_1029, plain, (![B_311]: (~r2_hidden('#skF_5'('#skF_10', B_311, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_311, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_311)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_904])).
% 3.34/1.60  tff(c_1033, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_22, c_1029])).
% 3.34/1.60  tff(c_1037, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_877, c_890, c_1033])).
% 3.34/1.60  tff(c_1038, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_50])).
% 3.34/1.60  tff(c_1127, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1124, c_1038])).
% 3.34/1.60  tff(c_1137, plain, (![A_339, B_340, C_341]: (r2_hidden('#skF_5'(A_339, B_340, C_341), k2_relat_1(C_341)) | ~r2_hidden(A_339, k10_relat_1(C_341, B_340)) | ~v1_relat_1(C_341))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.34/1.60  tff(c_1046, plain, (![A_316, B_317, C_318]: (k2_relset_1(A_316, B_317, C_318)=k2_relat_1(C_318) | ~m1_subset_1(C_318, k1_zfmisc_1(k2_zfmisc_1(A_316, B_317))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.34/1.60  tff(c_1050, plain, (k2_relset_1('#skF_6', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_36, c_1046])).
% 3.34/1.60  tff(c_1056, plain, (![A_319, B_320, C_321]: (m1_subset_1(k2_relset_1(A_319, B_320, C_321), k1_zfmisc_1(B_320)) | ~m1_subset_1(C_321, k1_zfmisc_1(k2_zfmisc_1(A_319, B_320))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.34/1.60  tff(c_1068, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_1050, c_1056])).
% 3.34/1.60  tff(c_1073, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1068])).
% 3.34/1.60  tff(c_1080, plain, (![A_1]: (m1_subset_1(A_1, '#skF_8') | ~r2_hidden(A_1, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_1073, c_2])).
% 3.34/1.60  tff(c_1141, plain, (![A_339, B_340]: (m1_subset_1('#skF_5'(A_339, B_340, '#skF_9'), '#skF_8') | ~r2_hidden(A_339, k10_relat_1('#skF_9', B_340)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1137, c_1080])).
% 3.34/1.60  tff(c_1145, plain, (![A_342, B_343]: (m1_subset_1('#skF_5'(A_342, B_343, '#skF_9'), '#skF_8') | ~r2_hidden(A_342, k10_relat_1('#skF_9', B_343)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1141])).
% 3.34/1.60  tff(c_1161, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_1127, c_1145])).
% 3.34/1.60  tff(c_1166, plain, (![A_347, B_348, C_349]: (r2_hidden(k4_tarski(A_347, '#skF_5'(A_347, B_348, C_349)), C_349) | ~r2_hidden(A_347, k10_relat_1(C_349, B_348)) | ~v1_relat_1(C_349))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.34/1.60  tff(c_1039, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_50])).
% 3.34/1.60  tff(c_48, plain, (![F_132]: (~r2_hidden(F_132, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_132), '#skF_9') | ~m1_subset_1(F_132, '#skF_8') | r2_hidden('#skF_11', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.34/1.60  tff(c_1125, plain, (![F_132]: (~r2_hidden(F_132, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_132), '#skF_9') | ~m1_subset_1(F_132, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1039, c_48])).
% 3.34/1.60  tff(c_1174, plain, (![B_348]: (~r2_hidden('#skF_5'('#skF_10', B_348, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_348, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_348)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1166, c_1125])).
% 3.34/1.60  tff(c_1302, plain, (![B_362]: (~r2_hidden('#skF_5'('#skF_10', B_362, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_362, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_362)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1174])).
% 3.34/1.60  tff(c_1306, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_22, c_1302])).
% 3.34/1.60  tff(c_1310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_1127, c_1161, c_1306])).
% 3.34/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.60  
% 3.34/1.60  Inference rules
% 3.34/1.60  ----------------------
% 3.34/1.60  #Ref     : 0
% 3.34/1.60  #Sup     : 246
% 3.34/1.60  #Fact    : 0
% 3.34/1.60  #Define  : 0
% 3.34/1.60  #Split   : 12
% 3.34/1.60  #Chain   : 0
% 3.34/1.60  #Close   : 0
% 3.34/1.60  
% 3.34/1.60  Ordering : KBO
% 3.34/1.60  
% 3.34/1.60  Simplification rules
% 3.34/1.60  ----------------------
% 3.34/1.60  #Subsume      : 17
% 3.34/1.60  #Demod        : 52
% 3.34/1.60  #Tautology    : 39
% 3.34/1.60  #SimpNegUnit  : 7
% 3.34/1.60  #BackRed      : 3
% 3.34/1.60  
% 3.34/1.60  #Partial instantiations: 0
% 3.34/1.61  #Strategies tried      : 1
% 3.34/1.61  
% 3.34/1.61  Timing (in seconds)
% 3.34/1.61  ----------------------
% 3.34/1.61  Preprocessing        : 0.34
% 3.34/1.61  Parsing              : 0.18
% 3.34/1.61  CNF conversion       : 0.03
% 3.34/1.61  Main loop            : 0.46
% 3.34/1.61  Inferencing          : 0.18
% 3.34/1.61  Reduction            : 0.13
% 3.34/1.61  Demodulation         : 0.09
% 3.34/1.61  BG Simplification    : 0.03
% 3.34/1.61  Subsumption          : 0.08
% 3.34/1.61  Abstraction          : 0.03
% 3.34/1.61  MUC search           : 0.00
% 3.34/1.61  Cooper               : 0.00
% 3.34/1.61  Total                : 0.84
% 3.34/1.61  Index Insertion      : 0.00
% 3.34/1.61  Index Deletion       : 0.00
% 3.34/1.61  Index Matching       : 0.00
% 3.34/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
