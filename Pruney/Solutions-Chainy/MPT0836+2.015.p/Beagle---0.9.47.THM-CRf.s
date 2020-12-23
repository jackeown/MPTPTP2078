%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:04 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 162 expanded)
%              Number of leaves         :   36 (  71 expanded)
%              Depth                    :    9
%              Number of atoms          :  120 ( 353 expanded)
%              Number of equality atoms :   22 (  38 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_4 > #skF_3 > #skF_10 > #skF_13 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => ( r2_hidden(D,k1_relset_1(A,B,C))
                    <=> ? [E] :
                          ( m1_subset_1(E,B)
                          & r2_hidden(k4_tarski(D,E),C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_40,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_320,plain,(
    ! [A_178,B_179,C_180] :
      ( k1_relset_1(A_178,B_179,C_180) = k1_relat_1(C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_324,plain,(
    k1_relset_1('#skF_9','#skF_10','#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_40,c_320])).

tff(c_151,plain,(
    ! [A_131,B_132,C_133] :
      ( k1_relset_1(A_131,B_132,C_133) = k1_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_155,plain,(
    k1_relset_1('#skF_9','#skF_10','#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_40,c_151])).

tff(c_56,plain,
    ( r2_hidden('#skF_12',k1_relset_1('#skF_9','#skF_10','#skF_11'))
    | m1_subset_1('#skF_13','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_59,plain,(
    m1_subset_1('#skF_13','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_52,plain,
    ( r2_hidden('#skF_12',k1_relset_1('#skF_9','#skF_10','#skF_11'))
    | r2_hidden(k4_tarski('#skF_12','#skF_13'),'#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_64,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_13'),'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_6,plain,(
    ! [C_19,A_4,D_22] :
      ( r2_hidden(C_19,k1_relat_1(A_4))
      | ~ r2_hidden(k4_tarski(C_19,D_22),A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_71,plain,(
    r2_hidden('#skF_12',k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_64,c_6])).

tff(c_84,plain,(
    ! [A_110,B_111,C_112] :
      ( k1_relset_1(A_110,B_111,C_112) = k1_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_88,plain,(
    k1_relset_1('#skF_9','#skF_10','#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_40,c_84])).

tff(c_46,plain,(
    ! [E_96] :
      ( ~ r2_hidden(k4_tarski('#skF_12',E_96),'#skF_11')
      | ~ m1_subset_1(E_96,'#skF_10')
      | ~ r2_hidden('#skF_12',k1_relset_1('#skF_9','#skF_10','#skF_11')) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_132,plain,(
    ! [E_129] :
      ( ~ r2_hidden(k4_tarski('#skF_12',E_129),'#skF_11')
      | ~ m1_subset_1(E_129,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_88,c_46])).

tff(c_139,plain,(
    ~ m1_subset_1('#skF_13','#skF_10') ),
    inference(resolution,[status(thm)],[c_64,c_132])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_139])).

tff(c_147,plain,(
    r2_hidden('#skF_12',k1_relset_1('#skF_9','#skF_10','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_156,plain,(
    r2_hidden('#skF_12',k1_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_147])).

tff(c_175,plain,(
    ! [C_140,A_141] :
      ( r2_hidden(k4_tarski(C_140,'#skF_4'(A_141,k1_relat_1(A_141),C_140)),A_141)
      | ~ r2_hidden(C_140,k1_relat_1(A_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [C_38,A_23,D_41] :
      ( r2_hidden(C_38,k2_relat_1(A_23))
      | ~ r2_hidden(k4_tarski(D_41,C_38),A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_190,plain,(
    ! [A_141,C_140] :
      ( r2_hidden('#skF_4'(A_141,k1_relat_1(A_141),C_140),k2_relat_1(A_141))
      | ~ r2_hidden(C_140,k1_relat_1(A_141)) ) ),
    inference(resolution,[status(thm)],[c_175,c_18])).

tff(c_161,plain,(
    ! [A_134,B_135,C_136] :
      ( k2_relset_1(A_134,B_135,C_136) = k2_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_165,plain,(
    k2_relset_1('#skF_9','#skF_10','#skF_11') = k2_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_40,c_161])).

tff(c_232,plain,(
    ! [A_163,B_164,C_165] :
      ( k7_relset_1(A_163,B_164,C_165,A_163) = k2_relset_1(A_163,B_164,C_165)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_237,plain,(
    k7_relset_1('#skF_9','#skF_10','#skF_11','#skF_9') = k2_relset_1('#skF_9','#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_40,c_232])).

tff(c_240,plain,(
    k7_relset_1('#skF_9','#skF_10','#skF_11','#skF_9') = k2_relat_1('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_237])).

tff(c_28,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( m1_subset_1(k7_relset_1(A_42,B_43,C_44,D_45),k1_zfmisc_1(B_43))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_244,plain,
    ( m1_subset_1(k2_relat_1('#skF_11'),k1_zfmisc_1('#skF_10'))
    | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_10'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_28])).

tff(c_248,plain,(
    m1_subset_1(k2_relat_1('#skF_11'),k1_zfmisc_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_244])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_253,plain,(
    ! [A_166] :
      ( m1_subset_1(A_166,'#skF_10')
      | ~ r2_hidden(A_166,k2_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_248,c_2])).

tff(c_293,plain,(
    ! [C_169] :
      ( m1_subset_1('#skF_4'('#skF_11',k1_relat_1('#skF_11'),C_169),'#skF_10')
      | ~ r2_hidden(C_169,k1_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_190,c_253])).

tff(c_148,plain,(
    ~ r2_hidden(k4_tarski('#skF_12','#skF_13'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,(
    ! [E_96] :
      ( ~ r2_hidden(k4_tarski('#skF_12',E_96),'#skF_11')
      | ~ m1_subset_1(E_96,'#skF_10')
      | r2_hidden(k4_tarski('#skF_12','#skF_13'),'#skF_11') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_171,plain,(
    ! [E_96] :
      ( ~ r2_hidden(k4_tarski('#skF_12',E_96),'#skF_11')
      | ~ m1_subset_1(E_96,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_50])).

tff(c_179,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_11',k1_relat_1('#skF_11'),'#skF_12'),'#skF_10')
    | ~ r2_hidden('#skF_12',k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_175,c_171])).

tff(c_188,plain,(
    ~ m1_subset_1('#skF_4'('#skF_11',k1_relat_1('#skF_11'),'#skF_12'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_179])).

tff(c_296,plain,(
    ~ r2_hidden('#skF_12',k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_293,c_188])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_296])).

tff(c_301,plain,(
    r2_hidden('#skF_12',k1_relset_1('#skF_9','#skF_10','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_325,plain,(
    r2_hidden('#skF_12',k1_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_301])).

tff(c_334,plain,(
    ! [C_185,A_186] :
      ( r2_hidden(k4_tarski(C_185,'#skF_4'(A_186,k1_relat_1(A_186),C_185)),A_186)
      | ~ r2_hidden(C_185,k1_relat_1(A_186)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_349,plain,(
    ! [A_186,C_185] :
      ( r2_hidden('#skF_4'(A_186,k1_relat_1(A_186),C_185),k2_relat_1(A_186))
      | ~ r2_hidden(C_185,k1_relat_1(A_186)) ) ),
    inference(resolution,[status(thm)],[c_334,c_18])).

tff(c_311,plain,(
    ! [A_175,B_176,C_177] :
      ( k2_relset_1(A_175,B_176,C_177) = k2_relat_1(C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_315,plain,(
    k2_relset_1('#skF_9','#skF_10','#skF_11') = k2_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_40,c_311])).

tff(c_376,plain,(
    ! [A_200,B_201,C_202] :
      ( k7_relset_1(A_200,B_201,C_202,A_200) = k2_relset_1(A_200,B_201,C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_381,plain,(
    k7_relset_1('#skF_9','#skF_10','#skF_11','#skF_9') = k2_relset_1('#skF_9','#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_40,c_376])).

tff(c_384,plain,(
    k7_relset_1('#skF_9','#skF_10','#skF_11','#skF_9') = k2_relat_1('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_381])).

tff(c_388,plain,
    ( m1_subset_1(k2_relat_1('#skF_11'),k1_zfmisc_1('#skF_10'))
    | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_10'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_28])).

tff(c_392,plain,(
    m1_subset_1(k2_relat_1('#skF_11'),k1_zfmisc_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_388])).

tff(c_397,plain,(
    ! [A_203] :
      ( m1_subset_1(A_203,'#skF_10')
      | ~ r2_hidden(A_203,k2_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_392,c_2])).

tff(c_423,plain,(
    ! [C_204] :
      ( m1_subset_1('#skF_4'('#skF_11',k1_relat_1('#skF_11'),C_204),'#skF_10')
      | ~ r2_hidden(C_204,k1_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_349,c_397])).

tff(c_302,plain,(
    ~ m1_subset_1('#skF_13','#skF_10') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,(
    ! [E_96] :
      ( ~ r2_hidden(k4_tarski('#skF_12',E_96),'#skF_11')
      | ~ m1_subset_1(E_96,'#skF_10')
      | m1_subset_1('#skF_13','#skF_10') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_303,plain,(
    ! [E_96] :
      ( ~ r2_hidden(k4_tarski('#skF_12',E_96),'#skF_11')
      | ~ m1_subset_1(E_96,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_302,c_54])).

tff(c_338,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_11',k1_relat_1('#skF_11'),'#skF_12'),'#skF_10')
    | ~ r2_hidden('#skF_12',k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_334,c_303])).

tff(c_347,plain,(
    ~ m1_subset_1('#skF_4'('#skF_11',k1_relat_1('#skF_11'),'#skF_12'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_338])).

tff(c_426,plain,(
    ~ r2_hidden('#skF_12',k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_423,c_347])).

tff(c_430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_426])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:09:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.35  
% 2.65/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.35  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_4 > #skF_3 > #skF_10 > #skF_13 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_12
% 2.65/1.35  
% 2.65/1.35  %Foreground sorts:
% 2.65/1.35  
% 2.65/1.35  
% 2.65/1.35  %Background operators:
% 2.65/1.35  
% 2.65/1.35  
% 2.65/1.35  %Foreground operators:
% 2.65/1.35  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.65/1.35  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.35  tff('#skF_11', type, '#skF_11': $i).
% 2.65/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.65/1.35  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.65/1.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.65/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.65/1.35  tff('#skF_10', type, '#skF_10': $i).
% 2.65/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.65/1.35  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.65/1.35  tff('#skF_13', type, '#skF_13': $i).
% 2.65/1.35  tff('#skF_9', type, '#skF_9': $i).
% 2.65/1.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.65/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.65/1.35  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 2.65/1.35  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.65/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.65/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.65/1.35  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.65/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.65/1.35  tff('#skF_12', type, '#skF_12': $i).
% 2.65/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.35  
% 2.65/1.37  tff(f_86, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, A) => (r2_hidden(D, k1_relset_1(A, B, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(D, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relset_1)).
% 2.65/1.37  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.65/1.37  tff(f_39, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.65/1.37  tff(f_47, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.65/1.37  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.65/1.37  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.65/1.37  tff(f_51, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 2.65/1.37  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.65/1.37  tff(c_40, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.65/1.37  tff(c_320, plain, (![A_178, B_179, C_180]: (k1_relset_1(A_178, B_179, C_180)=k1_relat_1(C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.65/1.37  tff(c_324, plain, (k1_relset_1('#skF_9', '#skF_10', '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_40, c_320])).
% 2.65/1.37  tff(c_151, plain, (![A_131, B_132, C_133]: (k1_relset_1(A_131, B_132, C_133)=k1_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.65/1.37  tff(c_155, plain, (k1_relset_1('#skF_9', '#skF_10', '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_40, c_151])).
% 2.65/1.37  tff(c_56, plain, (r2_hidden('#skF_12', k1_relset_1('#skF_9', '#skF_10', '#skF_11')) | m1_subset_1('#skF_13', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.65/1.37  tff(c_59, plain, (m1_subset_1('#skF_13', '#skF_10')), inference(splitLeft, [status(thm)], [c_56])).
% 2.65/1.37  tff(c_52, plain, (r2_hidden('#skF_12', k1_relset_1('#skF_9', '#skF_10', '#skF_11')) | r2_hidden(k4_tarski('#skF_12', '#skF_13'), '#skF_11')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.65/1.37  tff(c_64, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_13'), '#skF_11')), inference(splitLeft, [status(thm)], [c_52])).
% 2.65/1.37  tff(c_6, plain, (![C_19, A_4, D_22]: (r2_hidden(C_19, k1_relat_1(A_4)) | ~r2_hidden(k4_tarski(C_19, D_22), A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.65/1.37  tff(c_71, plain, (r2_hidden('#skF_12', k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_64, c_6])).
% 2.65/1.37  tff(c_84, plain, (![A_110, B_111, C_112]: (k1_relset_1(A_110, B_111, C_112)=k1_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.65/1.37  tff(c_88, plain, (k1_relset_1('#skF_9', '#skF_10', '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_40, c_84])).
% 2.65/1.37  tff(c_46, plain, (![E_96]: (~r2_hidden(k4_tarski('#skF_12', E_96), '#skF_11') | ~m1_subset_1(E_96, '#skF_10') | ~r2_hidden('#skF_12', k1_relset_1('#skF_9', '#skF_10', '#skF_11')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.65/1.37  tff(c_132, plain, (![E_129]: (~r2_hidden(k4_tarski('#skF_12', E_129), '#skF_11') | ~m1_subset_1(E_129, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_88, c_46])).
% 2.65/1.37  tff(c_139, plain, (~m1_subset_1('#skF_13', '#skF_10')), inference(resolution, [status(thm)], [c_64, c_132])).
% 2.65/1.37  tff(c_146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_139])).
% 2.65/1.37  tff(c_147, plain, (r2_hidden('#skF_12', k1_relset_1('#skF_9', '#skF_10', '#skF_11'))), inference(splitRight, [status(thm)], [c_52])).
% 2.65/1.37  tff(c_156, plain, (r2_hidden('#skF_12', k1_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_147])).
% 2.65/1.37  tff(c_175, plain, (![C_140, A_141]: (r2_hidden(k4_tarski(C_140, '#skF_4'(A_141, k1_relat_1(A_141), C_140)), A_141) | ~r2_hidden(C_140, k1_relat_1(A_141)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.65/1.37  tff(c_18, plain, (![C_38, A_23, D_41]: (r2_hidden(C_38, k2_relat_1(A_23)) | ~r2_hidden(k4_tarski(D_41, C_38), A_23))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.65/1.37  tff(c_190, plain, (![A_141, C_140]: (r2_hidden('#skF_4'(A_141, k1_relat_1(A_141), C_140), k2_relat_1(A_141)) | ~r2_hidden(C_140, k1_relat_1(A_141)))), inference(resolution, [status(thm)], [c_175, c_18])).
% 2.65/1.37  tff(c_161, plain, (![A_134, B_135, C_136]: (k2_relset_1(A_134, B_135, C_136)=k2_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.65/1.37  tff(c_165, plain, (k2_relset_1('#skF_9', '#skF_10', '#skF_11')=k2_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_40, c_161])).
% 2.65/1.37  tff(c_232, plain, (![A_163, B_164, C_165]: (k7_relset_1(A_163, B_164, C_165, A_163)=k2_relset_1(A_163, B_164, C_165) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.65/1.37  tff(c_237, plain, (k7_relset_1('#skF_9', '#skF_10', '#skF_11', '#skF_9')=k2_relset_1('#skF_9', '#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_40, c_232])).
% 2.65/1.37  tff(c_240, plain, (k7_relset_1('#skF_9', '#skF_10', '#skF_11', '#skF_9')=k2_relat_1('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_165, c_237])).
% 2.65/1.37  tff(c_28, plain, (![A_42, B_43, C_44, D_45]: (m1_subset_1(k7_relset_1(A_42, B_43, C_44, D_45), k1_zfmisc_1(B_43)) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.65/1.37  tff(c_244, plain, (m1_subset_1(k2_relat_1('#skF_11'), k1_zfmisc_1('#skF_10')) | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_240, c_28])).
% 2.65/1.37  tff(c_248, plain, (m1_subset_1(k2_relat_1('#skF_11'), k1_zfmisc_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_244])).
% 2.65/1.37  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.37  tff(c_253, plain, (![A_166]: (m1_subset_1(A_166, '#skF_10') | ~r2_hidden(A_166, k2_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_248, c_2])).
% 2.65/1.37  tff(c_293, plain, (![C_169]: (m1_subset_1('#skF_4'('#skF_11', k1_relat_1('#skF_11'), C_169), '#skF_10') | ~r2_hidden(C_169, k1_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_190, c_253])).
% 2.65/1.37  tff(c_148, plain, (~r2_hidden(k4_tarski('#skF_12', '#skF_13'), '#skF_11')), inference(splitRight, [status(thm)], [c_52])).
% 2.65/1.37  tff(c_50, plain, (![E_96]: (~r2_hidden(k4_tarski('#skF_12', E_96), '#skF_11') | ~m1_subset_1(E_96, '#skF_10') | r2_hidden(k4_tarski('#skF_12', '#skF_13'), '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.65/1.37  tff(c_171, plain, (![E_96]: (~r2_hidden(k4_tarski('#skF_12', E_96), '#skF_11') | ~m1_subset_1(E_96, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_148, c_50])).
% 2.65/1.37  tff(c_179, plain, (~m1_subset_1('#skF_4'('#skF_11', k1_relat_1('#skF_11'), '#skF_12'), '#skF_10') | ~r2_hidden('#skF_12', k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_175, c_171])).
% 2.65/1.37  tff(c_188, plain, (~m1_subset_1('#skF_4'('#skF_11', k1_relat_1('#skF_11'), '#skF_12'), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_179])).
% 2.65/1.37  tff(c_296, plain, (~r2_hidden('#skF_12', k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_293, c_188])).
% 2.65/1.37  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156, c_296])).
% 2.65/1.37  tff(c_301, plain, (r2_hidden('#skF_12', k1_relset_1('#skF_9', '#skF_10', '#skF_11'))), inference(splitRight, [status(thm)], [c_56])).
% 2.65/1.37  tff(c_325, plain, (r2_hidden('#skF_12', k1_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_324, c_301])).
% 2.65/1.37  tff(c_334, plain, (![C_185, A_186]: (r2_hidden(k4_tarski(C_185, '#skF_4'(A_186, k1_relat_1(A_186), C_185)), A_186) | ~r2_hidden(C_185, k1_relat_1(A_186)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.65/1.37  tff(c_349, plain, (![A_186, C_185]: (r2_hidden('#skF_4'(A_186, k1_relat_1(A_186), C_185), k2_relat_1(A_186)) | ~r2_hidden(C_185, k1_relat_1(A_186)))), inference(resolution, [status(thm)], [c_334, c_18])).
% 2.65/1.37  tff(c_311, plain, (![A_175, B_176, C_177]: (k2_relset_1(A_175, B_176, C_177)=k2_relat_1(C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.65/1.37  tff(c_315, plain, (k2_relset_1('#skF_9', '#skF_10', '#skF_11')=k2_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_40, c_311])).
% 2.65/1.37  tff(c_376, plain, (![A_200, B_201, C_202]: (k7_relset_1(A_200, B_201, C_202, A_200)=k2_relset_1(A_200, B_201, C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.65/1.37  tff(c_381, plain, (k7_relset_1('#skF_9', '#skF_10', '#skF_11', '#skF_9')=k2_relset_1('#skF_9', '#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_40, c_376])).
% 2.65/1.37  tff(c_384, plain, (k7_relset_1('#skF_9', '#skF_10', '#skF_11', '#skF_9')=k2_relat_1('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_315, c_381])).
% 2.65/1.37  tff(c_388, plain, (m1_subset_1(k2_relat_1('#skF_11'), k1_zfmisc_1('#skF_10')) | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_384, c_28])).
% 2.65/1.37  tff(c_392, plain, (m1_subset_1(k2_relat_1('#skF_11'), k1_zfmisc_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_388])).
% 2.65/1.37  tff(c_397, plain, (![A_203]: (m1_subset_1(A_203, '#skF_10') | ~r2_hidden(A_203, k2_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_392, c_2])).
% 2.65/1.37  tff(c_423, plain, (![C_204]: (m1_subset_1('#skF_4'('#skF_11', k1_relat_1('#skF_11'), C_204), '#skF_10') | ~r2_hidden(C_204, k1_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_349, c_397])).
% 2.65/1.37  tff(c_302, plain, (~m1_subset_1('#skF_13', '#skF_10')), inference(splitRight, [status(thm)], [c_56])).
% 2.65/1.37  tff(c_54, plain, (![E_96]: (~r2_hidden(k4_tarski('#skF_12', E_96), '#skF_11') | ~m1_subset_1(E_96, '#skF_10') | m1_subset_1('#skF_13', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.65/1.37  tff(c_303, plain, (![E_96]: (~r2_hidden(k4_tarski('#skF_12', E_96), '#skF_11') | ~m1_subset_1(E_96, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_302, c_54])).
% 2.65/1.37  tff(c_338, plain, (~m1_subset_1('#skF_4'('#skF_11', k1_relat_1('#skF_11'), '#skF_12'), '#skF_10') | ~r2_hidden('#skF_12', k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_334, c_303])).
% 2.65/1.37  tff(c_347, plain, (~m1_subset_1('#skF_4'('#skF_11', k1_relat_1('#skF_11'), '#skF_12'), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_325, c_338])).
% 2.65/1.37  tff(c_426, plain, (~r2_hidden('#skF_12', k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_423, c_347])).
% 2.65/1.37  tff(c_430, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_325, c_426])).
% 2.65/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.37  
% 2.65/1.37  Inference rules
% 2.65/1.37  ----------------------
% 2.65/1.37  #Ref     : 0
% 2.65/1.37  #Sup     : 78
% 2.65/1.37  #Fact    : 0
% 2.65/1.37  #Define  : 0
% 2.65/1.37  #Split   : 2
% 2.65/1.37  #Chain   : 0
% 2.65/1.37  #Close   : 0
% 2.65/1.37  
% 2.65/1.37  Ordering : KBO
% 2.65/1.37  
% 2.65/1.37  Simplification rules
% 2.65/1.37  ----------------------
% 2.65/1.37  #Subsume      : 3
% 2.65/1.37  #Demod        : 23
% 2.65/1.37  #Tautology    : 29
% 2.65/1.37  #SimpNegUnit  : 2
% 2.65/1.37  #BackRed      : 2
% 2.65/1.37  
% 2.65/1.37  #Partial instantiations: 0
% 2.65/1.37  #Strategies tried      : 1
% 2.65/1.37  
% 2.65/1.37  Timing (in seconds)
% 2.65/1.37  ----------------------
% 2.65/1.38  Preprocessing        : 0.33
% 2.65/1.38  Parsing              : 0.17
% 2.65/1.38  CNF conversion       : 0.03
% 2.65/1.38  Main loop            : 0.26
% 2.65/1.38  Inferencing          : 0.11
% 2.65/1.38  Reduction            : 0.07
% 2.65/1.38  Demodulation         : 0.05
% 2.65/1.38  BG Simplification    : 0.02
% 2.65/1.38  Subsumption          : 0.04
% 2.65/1.38  Abstraction          : 0.02
% 2.65/1.38  MUC search           : 0.00
% 2.65/1.38  Cooper               : 0.00
% 2.65/1.38  Total                : 0.63
% 2.65/1.38  Index Insertion      : 0.00
% 2.65/1.38  Index Deletion       : 0.00
% 2.65/1.38  Index Matching       : 0.00
% 2.65/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
