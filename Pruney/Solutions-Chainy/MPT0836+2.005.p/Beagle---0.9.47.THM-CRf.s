%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:03 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 286 expanded)
%              Number of leaves         :   35 ( 113 expanded)
%              Depth                    :    8
%              Number of atoms          :  175 ( 695 expanded)
%              Number of equality atoms :   28 (  84 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
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

tff(f_56,axiom,(
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

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_36,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_617,plain,(
    ! [A_213,B_214,C_215] :
      ( k1_relset_1(A_213,B_214,C_215) = k1_relat_1(C_215)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_621,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_617])).

tff(c_48,plain,
    ( r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8'))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_383,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_392,plain,(
    ! [C_160,A_161,D_162] :
      ( r2_hidden(C_160,k1_relat_1(A_161))
      | ~ r2_hidden(k4_tarski(C_160,D_162),A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_396,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_383,c_392])).

tff(c_474,plain,(
    ! [A_181,B_182,C_183,D_184] :
      ( k8_relset_1(A_181,B_182,C_183,D_184) = k10_relat_1(C_183,D_184)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_481,plain,(
    ! [D_184] : k8_relset_1('#skF_6','#skF_7','#skF_8',D_184) = k10_relat_1('#skF_8',D_184) ),
    inference(resolution,[status(thm)],[c_36,c_474])).

tff(c_408,plain,(
    ! [A_164,B_165,C_166] :
      ( k1_relset_1(A_164,B_165,C_166) = k1_relat_1(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_412,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_408])).

tff(c_552,plain,(
    ! [A_205,B_206,C_207] :
      ( k8_relset_1(A_205,B_206,C_207,B_206) = k1_relset_1(A_205,B_206,C_207)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_557,plain,(
    k8_relset_1('#skF_6','#skF_7','#skF_8','#skF_7') = k1_relset_1('#skF_6','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_552])).

tff(c_560,plain,(
    k10_relat_1('#skF_8','#skF_7') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_412,c_557])).

tff(c_54,plain,(
    ! [C_85,A_86,B_87] :
      ( v1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_58,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_54])).

tff(c_497,plain,(
    ! [A_192,B_193,C_194] :
      ( r2_hidden(k4_tarski(A_192,'#skF_5'(A_192,B_193,C_194)),C_194)
      | ~ r2_hidden(A_192,k10_relat_1(C_194,B_193))
      | ~ v1_relat_1(C_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_154,plain,(
    ! [A_112,B_113,C_114] :
      ( k1_relset_1(A_112,B_113,C_114) = k1_relat_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_158,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_154])).

tff(c_52,plain,
    ( r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8'))
    | m1_subset_1('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_59,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_60,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_65,plain,(
    ! [C_88,A_89,D_90] :
      ( r2_hidden(C_88,k1_relat_1(A_89))
      | ~ r2_hidden(k4_tarski(C_88,D_90),A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_69,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_60,c_65])).

tff(c_75,plain,(
    ! [A_91,B_92,C_93] :
      ( k1_relset_1(A_91,B_92,C_93) = k1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_79,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_75])).

tff(c_42,plain,(
    ! [E_82] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_82),'#skF_8')
      | ~ m1_subset_1(E_82,'#skF_7')
      | ~ r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_131,plain,(
    ! [E_108] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_108),'#skF_8')
      | ~ m1_subset_1(E_108,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_79,c_42])).

tff(c_138,plain,(
    ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_131])).

tff(c_145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_138])).

tff(c_146,plain,(
    r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_160,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_146])).

tff(c_230,plain,(
    ! [A_133,B_134,C_135,D_136] :
      ( k8_relset_1(A_133,B_134,C_135,D_136) = k10_relat_1(C_135,D_136)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_237,plain,(
    ! [D_136] : k8_relset_1('#skF_6','#skF_7','#skF_8',D_136) = k10_relat_1('#skF_8',D_136) ),
    inference(resolution,[status(thm)],[c_36,c_230])).

tff(c_303,plain,(
    ! [A_154,B_155,C_156] :
      ( k8_relset_1(A_154,B_155,C_156,B_155) = k1_relset_1(A_154,B_155,C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_308,plain,(
    k8_relset_1('#skF_6','#skF_7','#skF_8','#skF_7') = k1_relset_1('#skF_6','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_303])).

tff(c_311,plain,(
    k10_relat_1('#skF_8','#skF_7') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_158,c_308])).

tff(c_261,plain,(
    ! [A_147,B_148,C_149] :
      ( r2_hidden(k4_tarski(A_147,'#skF_5'(A_147,B_148,C_149)),C_149)
      | ~ r2_hidden(A_147,k10_relat_1(C_149,B_148))
      | ~ v1_relat_1(C_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_147,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [E_82] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_82),'#skF_8')
      | ~ m1_subset_1(E_82,'#skF_7')
      | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_175,plain,(
    ! [E_82] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_82),'#skF_8')
      | ~ m1_subset_1(E_82,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_46])).

tff(c_268,plain,(
    ! [B_148] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_148,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_148))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_261,c_175])).

tff(c_278,plain,(
    ! [B_148] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_148,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_148)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_268])).

tff(c_333,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_278])).

tff(c_342,plain,(
    ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_333])).

tff(c_170,plain,(
    ! [A_115,B_116,C_117] :
      ( r2_hidden('#skF_5'(A_115,B_116,C_117),B_116)
      | ~ r2_hidden(A_115,k10_relat_1(C_117,B_116))
      | ~ v1_relat_1(C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_174,plain,(
    ! [A_115,B_116,C_117] :
      ( m1_subset_1('#skF_5'(A_115,B_116,C_117),B_116)
      | ~ r2_hidden(A_115,k10_relat_1(C_117,B_116))
      | ~ v1_relat_1(C_117) ) ),
    inference(resolution,[status(thm)],[c_170,c_2])).

tff(c_338,plain,(
    ! [A_115] :
      ( m1_subset_1('#skF_5'(A_115,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_115,k1_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_174])).

tff(c_348,plain,(
    ! [A_159] :
      ( m1_subset_1('#skF_5'(A_159,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_159,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_338])).

tff(c_371,plain,(
    m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_160,c_348])).

tff(c_380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_371])).

tff(c_382,plain,(
    ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,(
    ! [E_82] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_82),'#skF_8')
      | ~ m1_subset_1(E_82,'#skF_7')
      | m1_subset_1('#skF_10','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_401,plain,(
    ! [E_82] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_82),'#skF_8')
      | ~ m1_subset_1(E_82,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_382,c_50])).

tff(c_504,plain,(
    ! [B_193] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_193,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_193))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_497,c_401])).

tff(c_514,plain,(
    ! [B_193] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_193,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_193)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_504])).

tff(c_567,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_514])).

tff(c_575,plain,(
    ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_567])).

tff(c_442,plain,(
    ! [A_171,B_172,C_173] :
      ( r2_hidden('#skF_5'(A_171,B_172,C_173),B_172)
      | ~ r2_hidden(A_171,k10_relat_1(C_173,B_172))
      | ~ v1_relat_1(C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_446,plain,(
    ! [A_171,B_172,C_173] :
      ( m1_subset_1('#skF_5'(A_171,B_172,C_173),B_172)
      | ~ r2_hidden(A_171,k10_relat_1(C_173,B_172))
      | ~ v1_relat_1(C_173) ) ),
    inference(resolution,[status(thm)],[c_442,c_2])).

tff(c_569,plain,(
    ! [A_171] :
      ( m1_subset_1('#skF_5'(A_171,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_171,k1_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_446])).

tff(c_579,plain,(
    ! [A_208] :
      ( m1_subset_1('#skF_5'(A_208,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_208,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_569])).

tff(c_598,plain,(
    m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_396,c_579])).

tff(c_606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_575,c_598])).

tff(c_607,plain,(
    r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_623,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_607])).

tff(c_692,plain,(
    ! [A_233,B_234,C_235,D_236] :
      ( k8_relset_1(A_233,B_234,C_235,D_236) = k10_relat_1(C_235,D_236)
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_699,plain,(
    ! [D_236] : k8_relset_1('#skF_6','#skF_7','#skF_8',D_236) = k10_relat_1('#skF_8',D_236) ),
    inference(resolution,[status(thm)],[c_36,c_692])).

tff(c_765,plain,(
    ! [A_254,B_255,C_256] :
      ( k8_relset_1(A_254,B_255,C_256,B_255) = k1_relset_1(A_254,B_255,C_256)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_254,B_255))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_770,plain,(
    k8_relset_1('#skF_6','#skF_7','#skF_8','#skF_7') = k1_relset_1('#skF_6','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_765])).

tff(c_773,plain,(
    k10_relat_1('#skF_8','#skF_7') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_621,c_770])).

tff(c_722,plain,(
    ! [A_244,B_245,C_246] :
      ( r2_hidden(k4_tarski(A_244,'#skF_5'(A_244,B_245,C_246)),C_246)
      | ~ r2_hidden(A_244,k10_relat_1(C_246,B_245))
      | ~ v1_relat_1(C_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_614,plain,(
    ! [E_82] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_82),'#skF_8')
      | ~ m1_subset_1(E_82,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_382,c_50])).

tff(c_732,plain,(
    ! [B_245] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_245,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_245))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_722,c_614])).

tff(c_740,plain,(
    ! [B_245] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_245,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_245)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_732])).

tff(c_795,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_773,c_740])).

tff(c_804,plain,(
    ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_795])).

tff(c_657,plain,(
    ! [A_220,B_221,C_222] :
      ( r2_hidden('#skF_5'(A_220,B_221,C_222),B_221)
      | ~ r2_hidden(A_220,k10_relat_1(C_222,B_221))
      | ~ v1_relat_1(C_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_661,plain,(
    ! [A_220,B_221,C_222] :
      ( m1_subset_1('#skF_5'(A_220,B_221,C_222),B_221)
      | ~ r2_hidden(A_220,k10_relat_1(C_222,B_221))
      | ~ v1_relat_1(C_222) ) ),
    inference(resolution,[status(thm)],[c_657,c_2])).

tff(c_800,plain,(
    ! [A_220] :
      ( m1_subset_1('#skF_5'(A_220,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_220,k1_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_773,c_661])).

tff(c_810,plain,(
    ! [A_259] :
      ( m1_subset_1('#skF_5'(A_259,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_259,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_800])).

tff(c_833,plain,(
    m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_623,c_810])).

tff(c_842,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_804,c_833])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:09:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.49  
% 3.00/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.49  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 3.00/1.49  
% 3.00/1.49  %Foreground sorts:
% 3.00/1.49  
% 3.00/1.49  
% 3.00/1.49  %Background operators:
% 3.00/1.49  
% 3.00/1.49  
% 3.00/1.49  %Foreground operators:
% 3.00/1.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.00/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.49  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.00/1.49  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.00/1.49  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.00/1.49  tff('#skF_7', type, '#skF_7': $i).
% 3.00/1.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.00/1.49  tff('#skF_10', type, '#skF_10': $i).
% 3.00/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.00/1.49  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.00/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.00/1.49  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.00/1.49  tff('#skF_9', type, '#skF_9': $i).
% 3.00/1.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.00/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.00/1.49  tff('#skF_8', type, '#skF_8': $i).
% 3.00/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.49  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.00/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.00/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.00/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.00/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.00/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.00/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.00/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.00/1.49  
% 3.00/1.51  tff(f_87, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, A) => (r2_hidden(D, k1_relset_1(A, B, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(D, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relset_1)).
% 3.00/1.51  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.00/1.51  tff(f_37, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.00/1.51  tff(f_60, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.00/1.51  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.00/1.51  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.00/1.51  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 3.00/1.51  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.00/1.51  tff(c_36, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.00/1.51  tff(c_617, plain, (![A_213, B_214, C_215]: (k1_relset_1(A_213, B_214, C_215)=k1_relat_1(C_215) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.00/1.51  tff(c_621, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_617])).
% 3.00/1.51  tff(c_48, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8')) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.00/1.51  tff(c_383, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(splitLeft, [status(thm)], [c_48])).
% 3.00/1.51  tff(c_392, plain, (![C_160, A_161, D_162]: (r2_hidden(C_160, k1_relat_1(A_161)) | ~r2_hidden(k4_tarski(C_160, D_162), A_161))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.00/1.51  tff(c_396, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_383, c_392])).
% 3.00/1.51  tff(c_474, plain, (![A_181, B_182, C_183, D_184]: (k8_relset_1(A_181, B_182, C_183, D_184)=k10_relat_1(C_183, D_184) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.00/1.51  tff(c_481, plain, (![D_184]: (k8_relset_1('#skF_6', '#skF_7', '#skF_8', D_184)=k10_relat_1('#skF_8', D_184))), inference(resolution, [status(thm)], [c_36, c_474])).
% 3.00/1.51  tff(c_408, plain, (![A_164, B_165, C_166]: (k1_relset_1(A_164, B_165, C_166)=k1_relat_1(C_166) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.00/1.51  tff(c_412, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_408])).
% 3.00/1.51  tff(c_552, plain, (![A_205, B_206, C_207]: (k8_relset_1(A_205, B_206, C_207, B_206)=k1_relset_1(A_205, B_206, C_207) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.00/1.51  tff(c_557, plain, (k8_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_7')=k1_relset_1('#skF_6', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_36, c_552])).
% 3.00/1.51  tff(c_560, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_481, c_412, c_557])).
% 3.00/1.51  tff(c_54, plain, (![C_85, A_86, B_87]: (v1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.00/1.51  tff(c_58, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_54])).
% 3.00/1.51  tff(c_497, plain, (![A_192, B_193, C_194]: (r2_hidden(k4_tarski(A_192, '#skF_5'(A_192, B_193, C_194)), C_194) | ~r2_hidden(A_192, k10_relat_1(C_194, B_193)) | ~v1_relat_1(C_194))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.00/1.51  tff(c_154, plain, (![A_112, B_113, C_114]: (k1_relset_1(A_112, B_113, C_114)=k1_relat_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.00/1.51  tff(c_158, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_154])).
% 3.00/1.51  tff(c_52, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8')) | m1_subset_1('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.00/1.51  tff(c_59, plain, (m1_subset_1('#skF_10', '#skF_7')), inference(splitLeft, [status(thm)], [c_52])).
% 3.00/1.51  tff(c_60, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(splitLeft, [status(thm)], [c_48])).
% 3.00/1.51  tff(c_65, plain, (![C_88, A_89, D_90]: (r2_hidden(C_88, k1_relat_1(A_89)) | ~r2_hidden(k4_tarski(C_88, D_90), A_89))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.00/1.51  tff(c_69, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_60, c_65])).
% 3.00/1.51  tff(c_75, plain, (![A_91, B_92, C_93]: (k1_relset_1(A_91, B_92, C_93)=k1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.00/1.51  tff(c_79, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_75])).
% 3.00/1.51  tff(c_42, plain, (![E_82]: (~r2_hidden(k4_tarski('#skF_9', E_82), '#skF_8') | ~m1_subset_1(E_82, '#skF_7') | ~r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.00/1.51  tff(c_131, plain, (![E_108]: (~r2_hidden(k4_tarski('#skF_9', E_108), '#skF_8') | ~m1_subset_1(E_108, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_79, c_42])).
% 3.00/1.51  tff(c_138, plain, (~m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_60, c_131])).
% 3.00/1.51  tff(c_145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_138])).
% 3.00/1.51  tff(c_146, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_48])).
% 3.00/1.51  tff(c_160, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_146])).
% 3.00/1.51  tff(c_230, plain, (![A_133, B_134, C_135, D_136]: (k8_relset_1(A_133, B_134, C_135, D_136)=k10_relat_1(C_135, D_136) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.00/1.51  tff(c_237, plain, (![D_136]: (k8_relset_1('#skF_6', '#skF_7', '#skF_8', D_136)=k10_relat_1('#skF_8', D_136))), inference(resolution, [status(thm)], [c_36, c_230])).
% 3.00/1.51  tff(c_303, plain, (![A_154, B_155, C_156]: (k8_relset_1(A_154, B_155, C_156, B_155)=k1_relset_1(A_154, B_155, C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.00/1.51  tff(c_308, plain, (k8_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_7')=k1_relset_1('#skF_6', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_36, c_303])).
% 3.00/1.51  tff(c_311, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_237, c_158, c_308])).
% 3.00/1.51  tff(c_261, plain, (![A_147, B_148, C_149]: (r2_hidden(k4_tarski(A_147, '#skF_5'(A_147, B_148, C_149)), C_149) | ~r2_hidden(A_147, k10_relat_1(C_149, B_148)) | ~v1_relat_1(C_149))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.00/1.51  tff(c_147, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(splitRight, [status(thm)], [c_48])).
% 3.00/1.51  tff(c_46, plain, (![E_82]: (~r2_hidden(k4_tarski('#skF_9', E_82), '#skF_8') | ~m1_subset_1(E_82, '#skF_7') | r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.00/1.51  tff(c_175, plain, (![E_82]: (~r2_hidden(k4_tarski('#skF_9', E_82), '#skF_8') | ~m1_subset_1(E_82, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_147, c_46])).
% 3.00/1.51  tff(c_268, plain, (![B_148]: (~m1_subset_1('#skF_5'('#skF_9', B_148, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_148)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_261, c_175])).
% 3.00/1.51  tff(c_278, plain, (![B_148]: (~m1_subset_1('#skF_5'('#skF_9', B_148, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_148)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_268])).
% 3.00/1.51  tff(c_333, plain, (~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_311, c_278])).
% 3.00/1.51  tff(c_342, plain, (~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_333])).
% 3.00/1.51  tff(c_170, plain, (![A_115, B_116, C_117]: (r2_hidden('#skF_5'(A_115, B_116, C_117), B_116) | ~r2_hidden(A_115, k10_relat_1(C_117, B_116)) | ~v1_relat_1(C_117))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.00/1.51  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.00/1.51  tff(c_174, plain, (![A_115, B_116, C_117]: (m1_subset_1('#skF_5'(A_115, B_116, C_117), B_116) | ~r2_hidden(A_115, k10_relat_1(C_117, B_116)) | ~v1_relat_1(C_117))), inference(resolution, [status(thm)], [c_170, c_2])).
% 3.00/1.51  tff(c_338, plain, (![A_115]: (m1_subset_1('#skF_5'(A_115, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_115, k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_311, c_174])).
% 3.00/1.51  tff(c_348, plain, (![A_159]: (m1_subset_1('#skF_5'(A_159, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_159, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_338])).
% 3.00/1.51  tff(c_371, plain, (m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_160, c_348])).
% 3.00/1.51  tff(c_380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_342, c_371])).
% 3.00/1.51  tff(c_382, plain, (~m1_subset_1('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_52])).
% 3.00/1.51  tff(c_50, plain, (![E_82]: (~r2_hidden(k4_tarski('#skF_9', E_82), '#skF_8') | ~m1_subset_1(E_82, '#skF_7') | m1_subset_1('#skF_10', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.00/1.51  tff(c_401, plain, (![E_82]: (~r2_hidden(k4_tarski('#skF_9', E_82), '#skF_8') | ~m1_subset_1(E_82, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_382, c_50])).
% 3.00/1.51  tff(c_504, plain, (![B_193]: (~m1_subset_1('#skF_5'('#skF_9', B_193, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_193)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_497, c_401])).
% 3.00/1.51  tff(c_514, plain, (![B_193]: (~m1_subset_1('#skF_5'('#skF_9', B_193, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_193)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_504])).
% 3.00/1.51  tff(c_567, plain, (~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_560, c_514])).
% 3.00/1.51  tff(c_575, plain, (~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_396, c_567])).
% 3.00/1.51  tff(c_442, plain, (![A_171, B_172, C_173]: (r2_hidden('#skF_5'(A_171, B_172, C_173), B_172) | ~r2_hidden(A_171, k10_relat_1(C_173, B_172)) | ~v1_relat_1(C_173))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.00/1.51  tff(c_446, plain, (![A_171, B_172, C_173]: (m1_subset_1('#skF_5'(A_171, B_172, C_173), B_172) | ~r2_hidden(A_171, k10_relat_1(C_173, B_172)) | ~v1_relat_1(C_173))), inference(resolution, [status(thm)], [c_442, c_2])).
% 3.00/1.51  tff(c_569, plain, (![A_171]: (m1_subset_1('#skF_5'(A_171, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_171, k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_560, c_446])).
% 3.00/1.51  tff(c_579, plain, (![A_208]: (m1_subset_1('#skF_5'(A_208, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_208, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_569])).
% 3.00/1.51  tff(c_598, plain, (m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_396, c_579])).
% 3.00/1.51  tff(c_606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_575, c_598])).
% 3.00/1.51  tff(c_607, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_48])).
% 3.00/1.51  tff(c_623, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_621, c_607])).
% 3.00/1.51  tff(c_692, plain, (![A_233, B_234, C_235, D_236]: (k8_relset_1(A_233, B_234, C_235, D_236)=k10_relat_1(C_235, D_236) | ~m1_subset_1(C_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.00/1.51  tff(c_699, plain, (![D_236]: (k8_relset_1('#skF_6', '#skF_7', '#skF_8', D_236)=k10_relat_1('#skF_8', D_236))), inference(resolution, [status(thm)], [c_36, c_692])).
% 3.00/1.51  tff(c_765, plain, (![A_254, B_255, C_256]: (k8_relset_1(A_254, B_255, C_256, B_255)=k1_relset_1(A_254, B_255, C_256) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_254, B_255))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.00/1.51  tff(c_770, plain, (k8_relset_1('#skF_6', '#skF_7', '#skF_8', '#skF_7')=k1_relset_1('#skF_6', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_36, c_765])).
% 3.00/1.51  tff(c_773, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_699, c_621, c_770])).
% 3.00/1.51  tff(c_722, plain, (![A_244, B_245, C_246]: (r2_hidden(k4_tarski(A_244, '#skF_5'(A_244, B_245, C_246)), C_246) | ~r2_hidden(A_244, k10_relat_1(C_246, B_245)) | ~v1_relat_1(C_246))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.00/1.51  tff(c_614, plain, (![E_82]: (~r2_hidden(k4_tarski('#skF_9', E_82), '#skF_8') | ~m1_subset_1(E_82, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_382, c_50])).
% 3.00/1.51  tff(c_732, plain, (![B_245]: (~m1_subset_1('#skF_5'('#skF_9', B_245, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_245)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_722, c_614])).
% 3.00/1.51  tff(c_740, plain, (![B_245]: (~m1_subset_1('#skF_5'('#skF_9', B_245, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_245)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_732])).
% 3.00/1.51  tff(c_795, plain, (~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_773, c_740])).
% 3.00/1.51  tff(c_804, plain, (~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_623, c_795])).
% 3.00/1.51  tff(c_657, plain, (![A_220, B_221, C_222]: (r2_hidden('#skF_5'(A_220, B_221, C_222), B_221) | ~r2_hidden(A_220, k10_relat_1(C_222, B_221)) | ~v1_relat_1(C_222))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.00/1.51  tff(c_661, plain, (![A_220, B_221, C_222]: (m1_subset_1('#skF_5'(A_220, B_221, C_222), B_221) | ~r2_hidden(A_220, k10_relat_1(C_222, B_221)) | ~v1_relat_1(C_222))), inference(resolution, [status(thm)], [c_657, c_2])).
% 3.00/1.51  tff(c_800, plain, (![A_220]: (m1_subset_1('#skF_5'(A_220, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_220, k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_773, c_661])).
% 3.00/1.51  tff(c_810, plain, (![A_259]: (m1_subset_1('#skF_5'(A_259, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_259, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_800])).
% 3.00/1.51  tff(c_833, plain, (m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_623, c_810])).
% 3.00/1.51  tff(c_842, plain, $false, inference(negUnitSimplification, [status(thm)], [c_804, c_833])).
% 3.00/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.51  
% 3.00/1.51  Inference rules
% 3.00/1.51  ----------------------
% 3.00/1.51  #Ref     : 0
% 3.00/1.51  #Sup     : 163
% 3.00/1.51  #Fact    : 0
% 3.00/1.51  #Define  : 0
% 3.00/1.51  #Split   : 3
% 3.00/1.51  #Chain   : 0
% 3.00/1.51  #Close   : 0
% 3.00/1.51  
% 3.00/1.51  Ordering : KBO
% 3.00/1.51  
% 3.00/1.51  Simplification rules
% 3.00/1.51  ----------------------
% 3.00/1.51  #Subsume      : 6
% 3.00/1.51  #Demod        : 46
% 3.00/1.51  #Tautology    : 42
% 3.00/1.51  #SimpNegUnit  : 7
% 3.00/1.51  #BackRed      : 6
% 3.00/1.51  
% 3.00/1.51  #Partial instantiations: 0
% 3.00/1.51  #Strategies tried      : 1
% 3.00/1.51  
% 3.00/1.51  Timing (in seconds)
% 3.00/1.51  ----------------------
% 3.00/1.52  Preprocessing        : 0.34
% 3.00/1.52  Parsing              : 0.18
% 3.00/1.52  CNF conversion       : 0.03
% 3.00/1.52  Main loop            : 0.35
% 3.00/1.52  Inferencing          : 0.14
% 3.00/1.52  Reduction            : 0.10
% 3.00/1.52  Demodulation         : 0.07
% 3.00/1.52  BG Simplification    : 0.02
% 3.00/1.52  Subsumption          : 0.06
% 3.00/1.52  Abstraction          : 0.02
% 3.00/1.52  MUC search           : 0.00
% 3.00/1.52  Cooper               : 0.00
% 3.00/1.52  Total                : 0.73
% 3.00/1.52  Index Insertion      : 0.00
% 3.00/1.52  Index Deletion       : 0.00
% 3.00/1.52  Index Matching       : 0.00
% 3.00/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
