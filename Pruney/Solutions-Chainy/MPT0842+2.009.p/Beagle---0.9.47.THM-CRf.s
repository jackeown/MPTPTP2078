%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:36 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 275 expanded)
%              Number of leaves         :   33 ( 107 expanded)
%              Depth                    :    9
%              Number of atoms          :  220 ( 813 expanded)
%              Number of equality atoms :   17 (  34 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_93,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_58,axiom,(
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

tff(c_34,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_57,plain,(
    ! [C_131,A_132,B_133] :
      ( v1_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_61,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_34,c_57])).

tff(c_1254,plain,(
    ! [A_353,B_354,C_355,D_356] :
      ( k8_relset_1(A_353,B_354,C_355,D_356) = k10_relat_1(C_355,D_356)
      | ~ m1_subset_1(C_355,k1_zfmisc_1(k2_zfmisc_1(A_353,B_354))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1261,plain,(
    ! [D_356] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_356) = k10_relat_1('#skF_9',D_356) ),
    inference(resolution,[status(thm)],[c_34,c_1254])).

tff(c_737,plain,(
    ! [A_258,B_259,C_260,D_261] :
      ( k8_relset_1(A_258,B_259,C_260,D_261) = k10_relat_1(C_260,D_261)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_744,plain,(
    ! [D_261] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_261) = k10_relat_1('#skF_9',D_261) ),
    inference(resolution,[status(thm)],[c_34,c_737])).

tff(c_469,plain,(
    ! [A_210,B_211,C_212,D_213] :
      ( k8_relset_1(A_210,B_211,C_212,D_213) = k10_relat_1(C_212,D_213)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_476,plain,(
    ! [D_213] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_213) = k10_relat_1('#skF_9',D_213) ),
    inference(resolution,[status(thm)],[c_34,c_469])).

tff(c_56,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_67,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_48,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_69,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_52,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_70,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_161,plain,(
    ! [A_160,B_161,C_162,D_163] :
      ( k8_relset_1(A_160,B_161,C_162,D_163) = k10_relat_1(C_162,D_163)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_168,plain,(
    ! [D_163] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_163) = k10_relat_1('#skF_9',D_163) ),
    inference(resolution,[status(thm)],[c_34,c_161])).

tff(c_42,plain,(
    ! [F_130] :
      ( ~ r2_hidden(F_130,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_130),'#skF_9')
      | ~ m1_subset_1(F_130,'#skF_8')
      | ~ r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_277,plain,(
    ! [F_130] :
      ( ~ r2_hidden(F_130,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_130),'#skF_9')
      | ~ m1_subset_1(F_130,'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_42])).

tff(c_278,plain,(
    ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_277])).

tff(c_6,plain,(
    ! [C_19,A_4,D_22] :
      ( r2_hidden(C_19,k2_relat_1(A_4))
      | ~ r2_hidden(k4_tarski(D_22,C_19),A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_74,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_70,c_6])).

tff(c_337,plain,(
    ! [A_189,C_190,B_191,D_192] :
      ( r2_hidden(A_189,k10_relat_1(C_190,B_191))
      | ~ r2_hidden(D_192,B_191)
      | ~ r2_hidden(k4_tarski(A_189,D_192),C_190)
      | ~ r2_hidden(D_192,k2_relat_1(C_190))
      | ~ v1_relat_1(C_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_377,plain,(
    ! [A_193,C_194] :
      ( r2_hidden(A_193,k10_relat_1(C_194,'#skF_7'))
      | ~ r2_hidden(k4_tarski(A_193,'#skF_11'),C_194)
      | ~ r2_hidden('#skF_11',k2_relat_1(C_194))
      | ~ v1_relat_1(C_194) ) ),
    inference(resolution,[status(thm)],[c_69,c_337])).

tff(c_384,plain,
    ( r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_377])).

tff(c_388,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_74,c_384])).

tff(c_390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_388])).

tff(c_397,plain,(
    ! [F_195] :
      ( ~ r2_hidden(F_195,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_195),'#skF_9')
      | ~ m1_subset_1(F_195,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_277])).

tff(c_404,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_397])).

tff(c_411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_69,c_404])).

tff(c_412,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_477,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_412])).

tff(c_488,plain,(
    ! [A_215,B_216,C_217] :
      ( r2_hidden('#skF_5'(A_215,B_216,C_217),k2_relat_1(C_217))
      | ~ r2_hidden(A_215,k10_relat_1(C_217,B_216))
      | ~ v1_relat_1(C_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_414,plain,(
    ! [A_196,B_197,C_198] :
      ( k2_relset_1(A_196,B_197,C_198) = k2_relat_1(C_198)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_418,plain,(
    k2_relset_1('#skF_6','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_34,c_414])).

tff(c_428,plain,(
    ! [A_201,B_202,C_203] :
      ( m1_subset_1(k2_relset_1(A_201,B_202,C_203),k1_zfmisc_1(B_202))
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_441,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_428])).

tff(c_446,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_441])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_449,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_8')
      | ~ r2_hidden(A_1,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_446,c_2])).

tff(c_492,plain,(
    ! [A_215,B_216] :
      ( m1_subset_1('#skF_5'(A_215,B_216,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_215,k10_relat_1('#skF_9',B_216))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_488,c_449])).

tff(c_496,plain,(
    ! [A_218,B_219] :
      ( m1_subset_1('#skF_5'(A_218,B_219,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_218,k10_relat_1('#skF_9',B_219)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_492])).

tff(c_512,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_477,c_496])).

tff(c_18,plain,(
    ! [A_23,B_24,C_25] :
      ( r2_hidden('#skF_5'(A_23,B_24,C_25),B_24)
      | ~ r2_hidden(A_23,k10_relat_1(C_25,B_24))
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_519,plain,(
    ! [A_224,B_225,C_226] :
      ( r2_hidden(k4_tarski(A_224,'#skF_5'(A_224,B_225,C_226)),C_226)
      | ~ r2_hidden(A_224,k10_relat_1(C_226,B_225))
      | ~ v1_relat_1(C_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_413,plain,(
    ~ r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,(
    ! [F_130] :
      ( ~ r2_hidden(F_130,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_130),'#skF_9')
      | ~ m1_subset_1(F_130,'#skF_8')
      | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_517,plain,(
    ! [F_130] :
      ( ~ r2_hidden(F_130,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_130),'#skF_9')
      | ~ m1_subset_1(F_130,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_50])).

tff(c_523,plain,(
    ! [B_225] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_225,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_225,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_225))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_519,c_517])).

tff(c_661,plain,(
    ! [B_243] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_243,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_243,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_243)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_523])).

tff(c_665,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_18,c_661])).

tff(c_669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_477,c_512,c_665])).

tff(c_670,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_745,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_744,c_670])).

tff(c_755,plain,(
    ! [A_263,B_264,C_265] :
      ( r2_hidden('#skF_5'(A_263,B_264,C_265),k2_relat_1(C_265))
      | ~ r2_hidden(A_263,k10_relat_1(C_265,B_264))
      | ~ v1_relat_1(C_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_677,plain,(
    ! [A_244,B_245,C_246] :
      ( k2_relset_1(A_244,B_245,C_246) = k2_relat_1(C_246)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_681,plain,(
    k2_relset_1('#skF_6','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_34,c_677])).

tff(c_692,plain,(
    ! [A_252,B_253,C_254] :
      ( m1_subset_1(k2_relset_1(A_252,B_253,C_254),k1_zfmisc_1(B_253))
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_705,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_692])).

tff(c_710,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_705])).

tff(c_714,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_8')
      | ~ r2_hidden(A_1,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_710,c_2])).

tff(c_759,plain,(
    ! [A_263,B_264] :
      ( m1_subset_1('#skF_5'(A_263,B_264,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_263,k10_relat_1('#skF_9',B_264))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_755,c_714])).

tff(c_763,plain,(
    ! [A_266,B_267] :
      ( m1_subset_1('#skF_5'(A_266,B_267,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_266,k10_relat_1('#skF_9',B_267)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_759])).

tff(c_779,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_745,c_763])).

tff(c_791,plain,(
    ! [A_269,B_270,C_271] :
      ( r2_hidden(k4_tarski(A_269,'#skF_5'(A_269,B_270,C_271)),C_271)
      | ~ r2_hidden(A_269,k10_relat_1(C_271,B_270))
      | ~ v1_relat_1(C_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_671,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [F_130] :
      ( ~ r2_hidden(F_130,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_130),'#skF_9')
      | ~ m1_subset_1(F_130,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_783,plain,(
    ! [F_130] :
      ( ~ r2_hidden(F_130,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_130),'#skF_9')
      | ~ m1_subset_1(F_130,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_671,c_46])).

tff(c_795,plain,(
    ! [B_270] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_270,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_270,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_270))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_791,c_783])).

tff(c_937,plain,(
    ! [B_291] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_291,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_291,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_291)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_795])).

tff(c_941,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_18,c_937])).

tff(c_945,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_745,c_779,c_941])).

tff(c_946,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1262,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1261,c_946])).

tff(c_1272,plain,(
    ! [A_358,B_359,C_360] :
      ( r2_hidden('#skF_5'(A_358,B_359,C_360),k2_relat_1(C_360))
      | ~ r2_hidden(A_358,k10_relat_1(C_360,B_359))
      | ~ v1_relat_1(C_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_950,plain,(
    ! [A_293,B_294,C_295] :
      ( k2_relset_1(A_293,B_294,C_295) = k2_relat_1(C_295)
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(A_293,B_294))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_954,plain,(
    k2_relset_1('#skF_6','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_34,c_950])).

tff(c_1207,plain,(
    ! [A_341,B_342,C_343] :
      ( m1_subset_1(k2_relset_1(A_341,B_342,C_343),k1_zfmisc_1(B_342))
      | ~ m1_subset_1(C_343,k1_zfmisc_1(k2_zfmisc_1(A_341,B_342))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1220,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_954,c_1207])).

tff(c_1225,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1220])).

tff(c_1228,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_8')
      | ~ r2_hidden(A_1,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_1225,c_2])).

tff(c_1276,plain,(
    ! [A_358,B_359] :
      ( m1_subset_1('#skF_5'(A_358,B_359,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_358,k10_relat_1('#skF_9',B_359))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1272,c_1228])).

tff(c_1280,plain,(
    ! [A_361,B_362] :
      ( m1_subset_1('#skF_5'(A_361,B_362,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_361,k10_relat_1('#skF_9',B_362)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_1276])).

tff(c_1296,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_1262,c_1280])).

tff(c_1300,plain,(
    ! [A_363,B_364,C_365] :
      ( r2_hidden(k4_tarski(A_363,'#skF_5'(A_363,B_364,C_365)),C_365)
      | ~ r2_hidden(A_363,k10_relat_1(C_365,B_364))
      | ~ v1_relat_1(C_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_947,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,(
    ! [F_130] :
      ( ~ r2_hidden(F_130,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_130),'#skF_9')
      | ~ m1_subset_1(F_130,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1230,plain,(
    ! [F_130] :
      ( ~ r2_hidden(F_130,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_130),'#skF_9')
      | ~ m1_subset_1(F_130,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_947,c_54])).

tff(c_1308,plain,(
    ! [B_364] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_364,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_364,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_364))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1300,c_1230])).

tff(c_1445,plain,(
    ! [B_385] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_385,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_385,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_385)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_1308])).

tff(c_1449,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_18,c_1445])).

tff(c_1453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_1262,c_1296,c_1449])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n010.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 12:12:59 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.57  
% 3.50/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.57  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 3.50/1.57  
% 3.50/1.57  %Foreground sorts:
% 3.50/1.57  
% 3.50/1.57  
% 3.50/1.57  %Background operators:
% 3.50/1.57  
% 3.50/1.57  
% 3.50/1.57  %Foreground operators:
% 3.50/1.57  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.50/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.50/1.57  tff('#skF_11', type, '#skF_11': $i).
% 3.50/1.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.50/1.57  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.50/1.57  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.50/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.50/1.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.50/1.57  tff('#skF_10', type, '#skF_10': $i).
% 3.50/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.50/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.50/1.57  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.50/1.57  tff('#skF_9', type, '#skF_9': $i).
% 3.50/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.50/1.57  tff('#skF_8', type, '#skF_8': $i).
% 3.50/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.57  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.50/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.50/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.50/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.50/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.50/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.50/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.50/1.57  
% 3.50/1.59  tff(f_93, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_relset_1)).
% 3.50/1.59  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.50/1.59  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.50/1.59  tff(f_39, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 3.50/1.59  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 3.50/1.59  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.50/1.59  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.50/1.59  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.50/1.59  tff(c_34, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.50/1.59  tff(c_57, plain, (![C_131, A_132, B_133]: (v1_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.50/1.59  tff(c_61, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_34, c_57])).
% 3.50/1.59  tff(c_1254, plain, (![A_353, B_354, C_355, D_356]: (k8_relset_1(A_353, B_354, C_355, D_356)=k10_relat_1(C_355, D_356) | ~m1_subset_1(C_355, k1_zfmisc_1(k2_zfmisc_1(A_353, B_354))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.50/1.59  tff(c_1261, plain, (![D_356]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_356)=k10_relat_1('#skF_9', D_356))), inference(resolution, [status(thm)], [c_34, c_1254])).
% 3.50/1.59  tff(c_737, plain, (![A_258, B_259, C_260, D_261]: (k8_relset_1(A_258, B_259, C_260, D_261)=k10_relat_1(C_260, D_261) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.50/1.59  tff(c_744, plain, (![D_261]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_261)=k10_relat_1('#skF_9', D_261))), inference(resolution, [status(thm)], [c_34, c_737])).
% 3.50/1.59  tff(c_469, plain, (![A_210, B_211, C_212, D_213]: (k8_relset_1(A_210, B_211, C_212, D_213)=k10_relat_1(C_212, D_213) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.50/1.59  tff(c_476, plain, (![D_213]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_213)=k10_relat_1('#skF_9', D_213))), inference(resolution, [status(thm)], [c_34, c_469])).
% 3.50/1.59  tff(c_56, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.50/1.59  tff(c_67, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_56])).
% 3.50/1.59  tff(c_48, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.50/1.59  tff(c_69, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_48])).
% 3.50/1.59  tff(c_52, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.50/1.59  tff(c_70, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitLeft, [status(thm)], [c_52])).
% 3.50/1.59  tff(c_161, plain, (![A_160, B_161, C_162, D_163]: (k8_relset_1(A_160, B_161, C_162, D_163)=k10_relat_1(C_162, D_163) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.50/1.59  tff(c_168, plain, (![D_163]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_163)=k10_relat_1('#skF_9', D_163))), inference(resolution, [status(thm)], [c_34, c_161])).
% 3.50/1.59  tff(c_42, plain, (![F_130]: (~r2_hidden(F_130, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_130), '#skF_9') | ~m1_subset_1(F_130, '#skF_8') | ~r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.50/1.59  tff(c_277, plain, (![F_130]: (~r2_hidden(F_130, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_130), '#skF_9') | ~m1_subset_1(F_130, '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_42])).
% 3.50/1.59  tff(c_278, plain, (~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(splitLeft, [status(thm)], [c_277])).
% 3.50/1.59  tff(c_6, plain, (![C_19, A_4, D_22]: (r2_hidden(C_19, k2_relat_1(A_4)) | ~r2_hidden(k4_tarski(D_22, C_19), A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.50/1.59  tff(c_74, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_70, c_6])).
% 3.50/1.59  tff(c_337, plain, (![A_189, C_190, B_191, D_192]: (r2_hidden(A_189, k10_relat_1(C_190, B_191)) | ~r2_hidden(D_192, B_191) | ~r2_hidden(k4_tarski(A_189, D_192), C_190) | ~r2_hidden(D_192, k2_relat_1(C_190)) | ~v1_relat_1(C_190))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.50/1.59  tff(c_377, plain, (![A_193, C_194]: (r2_hidden(A_193, k10_relat_1(C_194, '#skF_7')) | ~r2_hidden(k4_tarski(A_193, '#skF_11'), C_194) | ~r2_hidden('#skF_11', k2_relat_1(C_194)) | ~v1_relat_1(C_194))), inference(resolution, [status(thm)], [c_69, c_337])).
% 3.50/1.59  tff(c_384, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~r2_hidden('#skF_11', k2_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_70, c_377])).
% 3.50/1.59  tff(c_388, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_74, c_384])).
% 3.50/1.59  tff(c_390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_278, c_388])).
% 3.50/1.59  tff(c_397, plain, (![F_195]: (~r2_hidden(F_195, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_195), '#skF_9') | ~m1_subset_1(F_195, '#skF_8'))), inference(splitRight, [status(thm)], [c_277])).
% 3.50/1.59  tff(c_404, plain, (~r2_hidden('#skF_11', '#skF_7') | ~m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_70, c_397])).
% 3.50/1.59  tff(c_411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_69, c_404])).
% 3.50/1.59  tff(c_412, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_52])).
% 3.50/1.59  tff(c_477, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_476, c_412])).
% 3.50/1.59  tff(c_488, plain, (![A_215, B_216, C_217]: (r2_hidden('#skF_5'(A_215, B_216, C_217), k2_relat_1(C_217)) | ~r2_hidden(A_215, k10_relat_1(C_217, B_216)) | ~v1_relat_1(C_217))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.50/1.59  tff(c_414, plain, (![A_196, B_197, C_198]: (k2_relset_1(A_196, B_197, C_198)=k2_relat_1(C_198) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.50/1.59  tff(c_418, plain, (k2_relset_1('#skF_6', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_34, c_414])).
% 3.50/1.59  tff(c_428, plain, (![A_201, B_202, C_203]: (m1_subset_1(k2_relset_1(A_201, B_202, C_203), k1_zfmisc_1(B_202)) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.50/1.59  tff(c_441, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_418, c_428])).
% 3.50/1.59  tff(c_446, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_441])).
% 3.50/1.59  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.50/1.59  tff(c_449, plain, (![A_1]: (m1_subset_1(A_1, '#skF_8') | ~r2_hidden(A_1, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_446, c_2])).
% 3.50/1.59  tff(c_492, plain, (![A_215, B_216]: (m1_subset_1('#skF_5'(A_215, B_216, '#skF_9'), '#skF_8') | ~r2_hidden(A_215, k10_relat_1('#skF_9', B_216)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_488, c_449])).
% 3.50/1.59  tff(c_496, plain, (![A_218, B_219]: (m1_subset_1('#skF_5'(A_218, B_219, '#skF_9'), '#skF_8') | ~r2_hidden(A_218, k10_relat_1('#skF_9', B_219)))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_492])).
% 3.50/1.59  tff(c_512, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_477, c_496])).
% 3.50/1.59  tff(c_18, plain, (![A_23, B_24, C_25]: (r2_hidden('#skF_5'(A_23, B_24, C_25), B_24) | ~r2_hidden(A_23, k10_relat_1(C_25, B_24)) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.50/1.59  tff(c_519, plain, (![A_224, B_225, C_226]: (r2_hidden(k4_tarski(A_224, '#skF_5'(A_224, B_225, C_226)), C_226) | ~r2_hidden(A_224, k10_relat_1(C_226, B_225)) | ~v1_relat_1(C_226))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.50/1.59  tff(c_413, plain, (~r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitRight, [status(thm)], [c_52])).
% 3.50/1.59  tff(c_50, plain, (![F_130]: (~r2_hidden(F_130, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_130), '#skF_9') | ~m1_subset_1(F_130, '#skF_8') | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.50/1.59  tff(c_517, plain, (![F_130]: (~r2_hidden(F_130, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_130), '#skF_9') | ~m1_subset_1(F_130, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_413, c_50])).
% 3.50/1.59  tff(c_523, plain, (![B_225]: (~r2_hidden('#skF_5'('#skF_10', B_225, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_225, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_225)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_519, c_517])).
% 3.50/1.59  tff(c_661, plain, (![B_243]: (~r2_hidden('#skF_5'('#skF_10', B_243, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_243, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_243)))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_523])).
% 3.50/1.59  tff(c_665, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_18, c_661])).
% 3.50/1.59  tff(c_669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_477, c_512, c_665])).
% 3.50/1.59  tff(c_670, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_48])).
% 3.50/1.59  tff(c_745, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_744, c_670])).
% 3.50/1.59  tff(c_755, plain, (![A_263, B_264, C_265]: (r2_hidden('#skF_5'(A_263, B_264, C_265), k2_relat_1(C_265)) | ~r2_hidden(A_263, k10_relat_1(C_265, B_264)) | ~v1_relat_1(C_265))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.50/1.59  tff(c_677, plain, (![A_244, B_245, C_246]: (k2_relset_1(A_244, B_245, C_246)=k2_relat_1(C_246) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.50/1.59  tff(c_681, plain, (k2_relset_1('#skF_6', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_34, c_677])).
% 3.50/1.59  tff(c_692, plain, (![A_252, B_253, C_254]: (m1_subset_1(k2_relset_1(A_252, B_253, C_254), k1_zfmisc_1(B_253)) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_252, B_253))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.50/1.59  tff(c_705, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_681, c_692])).
% 3.50/1.59  tff(c_710, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_705])).
% 3.50/1.59  tff(c_714, plain, (![A_1]: (m1_subset_1(A_1, '#skF_8') | ~r2_hidden(A_1, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_710, c_2])).
% 3.50/1.59  tff(c_759, plain, (![A_263, B_264]: (m1_subset_1('#skF_5'(A_263, B_264, '#skF_9'), '#skF_8') | ~r2_hidden(A_263, k10_relat_1('#skF_9', B_264)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_755, c_714])).
% 3.50/1.59  tff(c_763, plain, (![A_266, B_267]: (m1_subset_1('#skF_5'(A_266, B_267, '#skF_9'), '#skF_8') | ~r2_hidden(A_266, k10_relat_1('#skF_9', B_267)))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_759])).
% 3.50/1.59  tff(c_779, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_745, c_763])).
% 3.50/1.59  tff(c_791, plain, (![A_269, B_270, C_271]: (r2_hidden(k4_tarski(A_269, '#skF_5'(A_269, B_270, C_271)), C_271) | ~r2_hidden(A_269, k10_relat_1(C_271, B_270)) | ~v1_relat_1(C_271))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.50/1.59  tff(c_671, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_48])).
% 3.50/1.59  tff(c_46, plain, (![F_130]: (~r2_hidden(F_130, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_130), '#skF_9') | ~m1_subset_1(F_130, '#skF_8') | r2_hidden('#skF_11', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.50/1.59  tff(c_783, plain, (![F_130]: (~r2_hidden(F_130, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_130), '#skF_9') | ~m1_subset_1(F_130, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_671, c_46])).
% 3.50/1.59  tff(c_795, plain, (![B_270]: (~r2_hidden('#skF_5'('#skF_10', B_270, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_270, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_270)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_791, c_783])).
% 3.50/1.59  tff(c_937, plain, (![B_291]: (~r2_hidden('#skF_5'('#skF_10', B_291, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_291, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_291)))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_795])).
% 3.50/1.59  tff(c_941, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_18, c_937])).
% 3.50/1.59  tff(c_945, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_745, c_779, c_941])).
% 3.50/1.59  tff(c_946, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_56])).
% 3.50/1.59  tff(c_1262, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1261, c_946])).
% 3.50/1.59  tff(c_1272, plain, (![A_358, B_359, C_360]: (r2_hidden('#skF_5'(A_358, B_359, C_360), k2_relat_1(C_360)) | ~r2_hidden(A_358, k10_relat_1(C_360, B_359)) | ~v1_relat_1(C_360))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.50/1.59  tff(c_950, plain, (![A_293, B_294, C_295]: (k2_relset_1(A_293, B_294, C_295)=k2_relat_1(C_295) | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1(A_293, B_294))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.50/1.59  tff(c_954, plain, (k2_relset_1('#skF_6', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_34, c_950])).
% 3.50/1.59  tff(c_1207, plain, (![A_341, B_342, C_343]: (m1_subset_1(k2_relset_1(A_341, B_342, C_343), k1_zfmisc_1(B_342)) | ~m1_subset_1(C_343, k1_zfmisc_1(k2_zfmisc_1(A_341, B_342))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.50/1.59  tff(c_1220, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_954, c_1207])).
% 3.50/1.59  tff(c_1225, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1220])).
% 3.50/1.59  tff(c_1228, plain, (![A_1]: (m1_subset_1(A_1, '#skF_8') | ~r2_hidden(A_1, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_1225, c_2])).
% 3.50/1.59  tff(c_1276, plain, (![A_358, B_359]: (m1_subset_1('#skF_5'(A_358, B_359, '#skF_9'), '#skF_8') | ~r2_hidden(A_358, k10_relat_1('#skF_9', B_359)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1272, c_1228])).
% 3.50/1.59  tff(c_1280, plain, (![A_361, B_362]: (m1_subset_1('#skF_5'(A_361, B_362, '#skF_9'), '#skF_8') | ~r2_hidden(A_361, k10_relat_1('#skF_9', B_362)))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_1276])).
% 3.50/1.59  tff(c_1296, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_1262, c_1280])).
% 3.50/1.59  tff(c_1300, plain, (![A_363, B_364, C_365]: (r2_hidden(k4_tarski(A_363, '#skF_5'(A_363, B_364, C_365)), C_365) | ~r2_hidden(A_363, k10_relat_1(C_365, B_364)) | ~v1_relat_1(C_365))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.50/1.59  tff(c_947, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_56])).
% 3.50/1.59  tff(c_54, plain, (![F_130]: (~r2_hidden(F_130, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_130), '#skF_9') | ~m1_subset_1(F_130, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.50/1.59  tff(c_1230, plain, (![F_130]: (~r2_hidden(F_130, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_130), '#skF_9') | ~m1_subset_1(F_130, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_947, c_54])).
% 3.50/1.59  tff(c_1308, plain, (![B_364]: (~r2_hidden('#skF_5'('#skF_10', B_364, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_364, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_364)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1300, c_1230])).
% 3.50/1.59  tff(c_1445, plain, (![B_385]: (~r2_hidden('#skF_5'('#skF_10', B_385, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_385, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_385)))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_1308])).
% 3.50/1.59  tff(c_1449, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_18, c_1445])).
% 3.50/1.59  tff(c_1453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_1262, c_1296, c_1449])).
% 3.50/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.59  
% 3.50/1.59  Inference rules
% 3.50/1.59  ----------------------
% 3.50/1.59  #Ref     : 0
% 3.50/1.59  #Sup     : 272
% 3.50/1.59  #Fact    : 0
% 3.50/1.59  #Define  : 0
% 3.50/1.59  #Split   : 6
% 3.50/1.59  #Chain   : 0
% 3.50/1.59  #Close   : 0
% 3.50/1.59  
% 3.50/1.59  Ordering : KBO
% 3.50/1.59  
% 3.50/1.59  Simplification rules
% 3.50/1.59  ----------------------
% 3.50/1.59  #Subsume      : 17
% 3.50/1.59  #Demod        : 57
% 3.50/1.59  #Tautology    : 42
% 3.50/1.59  #SimpNegUnit  : 5
% 3.50/1.59  #BackRed      : 4
% 3.50/1.59  
% 3.50/1.59  #Partial instantiations: 0
% 3.50/1.59  #Strategies tried      : 1
% 3.50/1.59  
% 3.50/1.59  Timing (in seconds)
% 3.50/1.59  ----------------------
% 3.50/1.60  Preprocessing        : 0.33
% 3.50/1.60  Parsing              : 0.16
% 3.50/1.60  CNF conversion       : 0.03
% 3.50/1.60  Main loop            : 0.50
% 3.50/1.60  Inferencing          : 0.20
% 3.50/1.60  Reduction            : 0.13
% 3.50/1.60  Demodulation         : 0.09
% 3.50/1.60  BG Simplification    : 0.03
% 3.50/1.60  Subsumption          : 0.09
% 3.50/1.60  Abstraction          : 0.03
% 3.50/1.60  MUC search           : 0.00
% 3.50/1.60  Cooper               : 0.00
% 3.50/1.60  Total                : 0.88
% 3.50/1.60  Index Insertion      : 0.00
% 3.50/1.60  Index Deletion       : 0.00
% 3.50/1.60  Index Matching       : 0.00
% 3.50/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
