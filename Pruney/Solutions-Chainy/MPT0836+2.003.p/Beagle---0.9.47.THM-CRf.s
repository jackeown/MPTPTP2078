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
% DateTime   : Thu Dec  3 10:08:03 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 178 expanded)
%              Number of leaves         :   35 (  77 expanded)
%              Depth                    :    9
%              Number of atoms          :  153 ( 433 expanded)
%              Number of equality atoms :   10 (  24 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => ( r2_hidden(D,k1_relset_1(A,B,C))
                    <=> ? [E] :
                          ( m1_subset_1(E,B)
                          & r2_hidden(k4_tarski(D,E),C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_38,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_56,plain,(
    ! [C_86,A_87,B_88] :
      ( v1_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_60,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_56])).

tff(c_765,plain,(
    ! [A_207,B_208,C_209] :
      ( k1_relset_1(A_207,B_208,C_209) = k1_relat_1(C_209)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_769,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_765])).

tff(c_182,plain,(
    ! [A_115,B_116,C_117] :
      ( k1_relset_1(A_115,B_116,C_117) = k1_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_186,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_182])).

tff(c_54,plain,
    ( r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8'))
    | m1_subset_1('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_71,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_50,plain,
    ( r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8'))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_83,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_6,plain,(
    ! [C_18,A_3,D_21] :
      ( r2_hidden(C_18,k1_relat_1(A_3))
      | ~ r2_hidden(k4_tarski(C_18,D_21),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_90,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_83,c_6])).

tff(c_98,plain,(
    ! [A_102,B_103,C_104] :
      ( k1_relset_1(A_102,B_103,C_104) = k1_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_102,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_98])).

tff(c_44,plain,(
    ! [E_83] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_83),'#skF_8')
      | ~ m1_subset_1(E_83,'#skF_7')
      | ~ r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_161,plain,(
    ! [E_114] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_114),'#skF_8')
      | ~ m1_subset_1(E_114,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_102,c_44])).

tff(c_168,plain,(
    ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_83,c_161])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_168])).

tff(c_176,plain,(
    r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_188,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_176])).

tff(c_72,plain,(
    ! [C_93,B_94,A_95] :
      ( v5_relat_1(C_93,B_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_76,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_72])).

tff(c_24,plain,(
    ! [A_28] :
      ( k10_relat_1(A_28,k2_relat_1(A_28)) = k1_relat_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_262,plain,(
    ! [A_131,B_132,C_133] :
      ( r2_hidden('#skF_5'(A_131,B_132,C_133),k2_relat_1(C_133))
      | ~ r2_hidden(A_131,k10_relat_1(C_133,B_132))
      | ~ v1_relat_1(C_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    ! [C_32,A_29,B_30] :
      ( r2_hidden(C_32,A_29)
      | ~ r2_hidden(C_32,k2_relat_1(B_30))
      | ~ v5_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_520,plain,(
    ! [A_169,B_170,C_171,A_172] :
      ( r2_hidden('#skF_5'(A_169,B_170,C_171),A_172)
      | ~ v5_relat_1(C_171,A_172)
      | ~ r2_hidden(A_169,k10_relat_1(C_171,B_170))
      | ~ v1_relat_1(C_171) ) ),
    inference(resolution,[status(thm)],[c_262,c_26])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_542,plain,(
    ! [A_175,B_176,C_177,A_178] :
      ( m1_subset_1('#skF_5'(A_175,B_176,C_177),A_178)
      | ~ v5_relat_1(C_177,A_178)
      | ~ r2_hidden(A_175,k10_relat_1(C_177,B_176))
      | ~ v1_relat_1(C_177) ) ),
    inference(resolution,[status(thm)],[c_520,c_2])).

tff(c_721,plain,(
    ! [A_194,A_195,A_196] :
      ( m1_subset_1('#skF_5'(A_194,k2_relat_1(A_195),A_195),A_196)
      | ~ v5_relat_1(A_195,A_196)
      | ~ r2_hidden(A_194,k1_relat_1(A_195))
      | ~ v1_relat_1(A_195)
      | ~ v1_relat_1(A_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_542])).

tff(c_288,plain,(
    ! [A_145,B_146,C_147] :
      ( r2_hidden(k4_tarski(A_145,'#skF_5'(A_145,B_146,C_147)),C_147)
      | ~ r2_hidden(A_145,k10_relat_1(C_147,B_146))
      | ~ v1_relat_1(C_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_177,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [E_83] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_83),'#skF_8')
      | ~ m1_subset_1(E_83,'#skF_7')
      | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_199,plain,(
    ! [E_83] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_83),'#skF_8')
      | ~ m1_subset_1(E_83,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_48])).

tff(c_295,plain,(
    ! [B_146] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_146,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_146))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_288,c_199])).

tff(c_336,plain,(
    ! [B_151] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_151,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_151)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_295])).

tff(c_340,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_9',k2_relat_1('#skF_8'),'#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_336])).

tff(c_342,plain,(
    ~ m1_subset_1('#skF_5'('#skF_9',k2_relat_1('#skF_8'),'#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_188,c_340])).

tff(c_724,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_721,c_342])).

tff(c_744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_188,c_76,c_724])).

tff(c_745,plain,(
    r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_771,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_745])).

tff(c_757,plain,(
    ! [C_200,B_201,A_202] :
      ( v5_relat_1(C_200,B_201)
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_zfmisc_1(A_202,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_761,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_757])).

tff(c_820,plain,(
    ! [A_219,B_220,C_221] :
      ( r2_hidden('#skF_5'(A_219,B_220,C_221),k2_relat_1(C_221))
      | ~ r2_hidden(A_219,k10_relat_1(C_221,B_220))
      | ~ v1_relat_1(C_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1100,plain,(
    ! [A_257,B_258,C_259,A_260] :
      ( r2_hidden('#skF_5'(A_257,B_258,C_259),A_260)
      | ~ v5_relat_1(C_259,A_260)
      | ~ r2_hidden(A_257,k10_relat_1(C_259,B_258))
      | ~ v1_relat_1(C_259) ) ),
    inference(resolution,[status(thm)],[c_820,c_26])).

tff(c_1131,plain,(
    ! [A_266,B_267,C_268,A_269] :
      ( m1_subset_1('#skF_5'(A_266,B_267,C_268),A_269)
      | ~ v5_relat_1(C_268,A_269)
      | ~ r2_hidden(A_266,k10_relat_1(C_268,B_267))
      | ~ v1_relat_1(C_268) ) ),
    inference(resolution,[status(thm)],[c_1100,c_2])).

tff(c_1326,plain,(
    ! [A_286,A_287,A_288] :
      ( m1_subset_1('#skF_5'(A_286,k2_relat_1(A_287),A_287),A_288)
      | ~ v5_relat_1(A_287,A_288)
      | ~ r2_hidden(A_286,k1_relat_1(A_287))
      | ~ v1_relat_1(A_287)
      | ~ v1_relat_1(A_287) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1131])).

tff(c_868,plain,(
    ! [A_233,B_234,C_235] :
      ( r2_hidden(k4_tarski(A_233,'#skF_5'(A_233,B_234,C_235)),C_235)
      | ~ r2_hidden(A_233,k10_relat_1(C_235,B_234))
      | ~ v1_relat_1(C_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_746,plain,(
    ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [E_83] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_83),'#skF_8')
      | ~ m1_subset_1(E_83,'#skF_7')
      | m1_subset_1('#skF_10','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_762,plain,(
    ! [E_83] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_83),'#skF_8')
      | ~ m1_subset_1(E_83,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_746,c_52])).

tff(c_878,plain,(
    ! [B_234] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_234,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_234))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_868,c_762])).

tff(c_892,plain,(
    ! [B_236] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_236,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_236)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_878])).

tff(c_896,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_9',k2_relat_1('#skF_8'),'#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_892])).

tff(c_898,plain,(
    ~ m1_subset_1('#skF_5'('#skF_9',k2_relat_1('#skF_8'),'#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_771,c_896])).

tff(c_1329,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1326,c_898])).

tff(c_1349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_771,c_761,c_1329])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:51:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.53  
% 3.39/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.54  %$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 3.39/1.54  
% 3.39/1.54  %Foreground sorts:
% 3.39/1.54  
% 3.39/1.54  
% 3.39/1.54  %Background operators:
% 3.39/1.54  
% 3.39/1.54  
% 3.39/1.54  %Foreground operators:
% 3.39/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.39/1.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.39/1.54  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.39/1.54  tff('#skF_7', type, '#skF_7': $i).
% 3.39/1.54  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.39/1.54  tff('#skF_10', type, '#skF_10': $i).
% 3.39/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.39/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.39/1.54  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.39/1.54  tff('#skF_9', type, '#skF_9': $i).
% 3.39/1.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.39/1.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.39/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.39/1.54  tff('#skF_8', type, '#skF_8': $i).
% 3.39/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.54  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.39/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.39/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.39/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.39/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.39/1.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.39/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.39/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.39/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.54  
% 3.54/1.55  tff(f_96, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, A) => (r2_hidden(D, k1_relset_1(A, B, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(D, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relset_1)).
% 3.54/1.55  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.54/1.55  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.54/1.55  tff(f_37, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.54/1.55  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.54/1.55  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.54/1.55  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 3.54/1.55  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t202_relat_1)).
% 3.54/1.55  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.54/1.55  tff(c_38, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.54/1.55  tff(c_56, plain, (![C_86, A_87, B_88]: (v1_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.54/1.55  tff(c_60, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_56])).
% 3.54/1.55  tff(c_765, plain, (![A_207, B_208, C_209]: (k1_relset_1(A_207, B_208, C_209)=k1_relat_1(C_209) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.54/1.55  tff(c_769, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_765])).
% 3.54/1.55  tff(c_182, plain, (![A_115, B_116, C_117]: (k1_relset_1(A_115, B_116, C_117)=k1_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.54/1.55  tff(c_186, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_182])).
% 3.54/1.55  tff(c_54, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8')) | m1_subset_1('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.54/1.55  tff(c_71, plain, (m1_subset_1('#skF_10', '#skF_7')), inference(splitLeft, [status(thm)], [c_54])).
% 3.54/1.55  tff(c_50, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8')) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.54/1.55  tff(c_83, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(splitLeft, [status(thm)], [c_50])).
% 3.54/1.55  tff(c_6, plain, (![C_18, A_3, D_21]: (r2_hidden(C_18, k1_relat_1(A_3)) | ~r2_hidden(k4_tarski(C_18, D_21), A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.54/1.55  tff(c_90, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_83, c_6])).
% 3.54/1.55  tff(c_98, plain, (![A_102, B_103, C_104]: (k1_relset_1(A_102, B_103, C_104)=k1_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.54/1.55  tff(c_102, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_98])).
% 3.54/1.55  tff(c_44, plain, (![E_83]: (~r2_hidden(k4_tarski('#skF_9', E_83), '#skF_8') | ~m1_subset_1(E_83, '#skF_7') | ~r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.54/1.55  tff(c_161, plain, (![E_114]: (~r2_hidden(k4_tarski('#skF_9', E_114), '#skF_8') | ~m1_subset_1(E_114, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_102, c_44])).
% 3.54/1.55  tff(c_168, plain, (~m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_83, c_161])).
% 3.54/1.55  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_168])).
% 3.54/1.55  tff(c_176, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_50])).
% 3.54/1.55  tff(c_188, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_176])).
% 3.54/1.55  tff(c_72, plain, (![C_93, B_94, A_95]: (v5_relat_1(C_93, B_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.54/1.55  tff(c_76, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_38, c_72])).
% 3.54/1.55  tff(c_24, plain, (![A_28]: (k10_relat_1(A_28, k2_relat_1(A_28))=k1_relat_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.54/1.55  tff(c_262, plain, (![A_131, B_132, C_133]: (r2_hidden('#skF_5'(A_131, B_132, C_133), k2_relat_1(C_133)) | ~r2_hidden(A_131, k10_relat_1(C_133, B_132)) | ~v1_relat_1(C_133))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.54/1.55  tff(c_26, plain, (![C_32, A_29, B_30]: (r2_hidden(C_32, A_29) | ~r2_hidden(C_32, k2_relat_1(B_30)) | ~v5_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.54/1.55  tff(c_520, plain, (![A_169, B_170, C_171, A_172]: (r2_hidden('#skF_5'(A_169, B_170, C_171), A_172) | ~v5_relat_1(C_171, A_172) | ~r2_hidden(A_169, k10_relat_1(C_171, B_170)) | ~v1_relat_1(C_171))), inference(resolution, [status(thm)], [c_262, c_26])).
% 3.54/1.55  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.54/1.55  tff(c_542, plain, (![A_175, B_176, C_177, A_178]: (m1_subset_1('#skF_5'(A_175, B_176, C_177), A_178) | ~v5_relat_1(C_177, A_178) | ~r2_hidden(A_175, k10_relat_1(C_177, B_176)) | ~v1_relat_1(C_177))), inference(resolution, [status(thm)], [c_520, c_2])).
% 3.54/1.55  tff(c_721, plain, (![A_194, A_195, A_196]: (m1_subset_1('#skF_5'(A_194, k2_relat_1(A_195), A_195), A_196) | ~v5_relat_1(A_195, A_196) | ~r2_hidden(A_194, k1_relat_1(A_195)) | ~v1_relat_1(A_195) | ~v1_relat_1(A_195))), inference(superposition, [status(thm), theory('equality')], [c_24, c_542])).
% 3.54/1.55  tff(c_288, plain, (![A_145, B_146, C_147]: (r2_hidden(k4_tarski(A_145, '#skF_5'(A_145, B_146, C_147)), C_147) | ~r2_hidden(A_145, k10_relat_1(C_147, B_146)) | ~v1_relat_1(C_147))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.54/1.55  tff(c_177, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(splitRight, [status(thm)], [c_50])).
% 3.54/1.55  tff(c_48, plain, (![E_83]: (~r2_hidden(k4_tarski('#skF_9', E_83), '#skF_8') | ~m1_subset_1(E_83, '#skF_7') | r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.54/1.55  tff(c_199, plain, (![E_83]: (~r2_hidden(k4_tarski('#skF_9', E_83), '#skF_8') | ~m1_subset_1(E_83, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_177, c_48])).
% 3.54/1.55  tff(c_295, plain, (![B_146]: (~m1_subset_1('#skF_5'('#skF_9', B_146, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_146)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_288, c_199])).
% 3.54/1.55  tff(c_336, plain, (![B_151]: (~m1_subset_1('#skF_5'('#skF_9', B_151, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_151)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_295])).
% 3.54/1.55  tff(c_340, plain, (~m1_subset_1('#skF_5'('#skF_9', k2_relat_1('#skF_8'), '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_24, c_336])).
% 3.54/1.55  tff(c_342, plain, (~m1_subset_1('#skF_5'('#skF_9', k2_relat_1('#skF_8'), '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_188, c_340])).
% 3.54/1.55  tff(c_724, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_721, c_342])).
% 3.54/1.55  tff(c_744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_188, c_76, c_724])).
% 3.54/1.55  tff(c_745, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_54])).
% 3.54/1.55  tff(c_771, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_769, c_745])).
% 3.54/1.55  tff(c_757, plain, (![C_200, B_201, A_202]: (v5_relat_1(C_200, B_201) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_zfmisc_1(A_202, B_201))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.54/1.55  tff(c_761, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_38, c_757])).
% 3.54/1.55  tff(c_820, plain, (![A_219, B_220, C_221]: (r2_hidden('#skF_5'(A_219, B_220, C_221), k2_relat_1(C_221)) | ~r2_hidden(A_219, k10_relat_1(C_221, B_220)) | ~v1_relat_1(C_221))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.54/1.55  tff(c_1100, plain, (![A_257, B_258, C_259, A_260]: (r2_hidden('#skF_5'(A_257, B_258, C_259), A_260) | ~v5_relat_1(C_259, A_260) | ~r2_hidden(A_257, k10_relat_1(C_259, B_258)) | ~v1_relat_1(C_259))), inference(resolution, [status(thm)], [c_820, c_26])).
% 3.54/1.55  tff(c_1131, plain, (![A_266, B_267, C_268, A_269]: (m1_subset_1('#skF_5'(A_266, B_267, C_268), A_269) | ~v5_relat_1(C_268, A_269) | ~r2_hidden(A_266, k10_relat_1(C_268, B_267)) | ~v1_relat_1(C_268))), inference(resolution, [status(thm)], [c_1100, c_2])).
% 3.54/1.55  tff(c_1326, plain, (![A_286, A_287, A_288]: (m1_subset_1('#skF_5'(A_286, k2_relat_1(A_287), A_287), A_288) | ~v5_relat_1(A_287, A_288) | ~r2_hidden(A_286, k1_relat_1(A_287)) | ~v1_relat_1(A_287) | ~v1_relat_1(A_287))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1131])).
% 3.54/1.55  tff(c_868, plain, (![A_233, B_234, C_235]: (r2_hidden(k4_tarski(A_233, '#skF_5'(A_233, B_234, C_235)), C_235) | ~r2_hidden(A_233, k10_relat_1(C_235, B_234)) | ~v1_relat_1(C_235))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.54/1.55  tff(c_746, plain, (~m1_subset_1('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_54])).
% 3.54/1.55  tff(c_52, plain, (![E_83]: (~r2_hidden(k4_tarski('#skF_9', E_83), '#skF_8') | ~m1_subset_1(E_83, '#skF_7') | m1_subset_1('#skF_10', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.54/1.55  tff(c_762, plain, (![E_83]: (~r2_hidden(k4_tarski('#skF_9', E_83), '#skF_8') | ~m1_subset_1(E_83, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_746, c_52])).
% 3.54/1.55  tff(c_878, plain, (![B_234]: (~m1_subset_1('#skF_5'('#skF_9', B_234, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_234)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_868, c_762])).
% 3.54/1.55  tff(c_892, plain, (![B_236]: (~m1_subset_1('#skF_5'('#skF_9', B_236, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_236)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_878])).
% 3.54/1.55  tff(c_896, plain, (~m1_subset_1('#skF_5'('#skF_9', k2_relat_1('#skF_8'), '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_24, c_892])).
% 3.54/1.55  tff(c_898, plain, (~m1_subset_1('#skF_5'('#skF_9', k2_relat_1('#skF_8'), '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_771, c_896])).
% 3.54/1.55  tff(c_1329, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_1326, c_898])).
% 3.54/1.55  tff(c_1349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_771, c_761, c_1329])).
% 3.54/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.55  
% 3.54/1.55  Inference rules
% 3.54/1.55  ----------------------
% 3.54/1.55  #Ref     : 0
% 3.54/1.55  #Sup     : 278
% 3.54/1.55  #Fact    : 0
% 3.54/1.55  #Define  : 0
% 3.54/1.55  #Split   : 4
% 3.54/1.55  #Chain   : 0
% 3.54/1.55  #Close   : 0
% 3.54/1.55  
% 3.54/1.55  Ordering : KBO
% 3.54/1.55  
% 3.54/1.55  Simplification rules
% 3.54/1.55  ----------------------
% 3.54/1.55  #Subsume      : 7
% 3.54/1.55  #Demod        : 33
% 3.54/1.55  #Tautology    : 29
% 3.54/1.55  #SimpNegUnit  : 2
% 3.54/1.55  #BackRed      : 4
% 3.54/1.55  
% 3.54/1.55  #Partial instantiations: 0
% 3.54/1.55  #Strategies tried      : 1
% 3.54/1.55  
% 3.54/1.55  Timing (in seconds)
% 3.54/1.55  ----------------------
% 3.54/1.56  Preprocessing        : 0.32
% 3.54/1.56  Parsing              : 0.16
% 3.54/1.56  CNF conversion       : 0.03
% 3.54/1.56  Main loop            : 0.48
% 3.54/1.56  Inferencing          : 0.18
% 3.54/1.56  Reduction            : 0.12
% 3.54/1.56  Demodulation         : 0.08
% 3.54/1.56  BG Simplification    : 0.03
% 3.54/1.56  Subsumption          : 0.10
% 3.54/1.56  Abstraction          : 0.03
% 3.54/1.56  MUC search           : 0.00
% 3.54/1.56  Cooper               : 0.00
% 3.54/1.56  Total                : 0.83
% 3.54/1.56  Index Insertion      : 0.00
% 3.54/1.56  Index Deletion       : 0.00
% 3.54/1.56  Index Matching       : 0.00
% 3.54/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
