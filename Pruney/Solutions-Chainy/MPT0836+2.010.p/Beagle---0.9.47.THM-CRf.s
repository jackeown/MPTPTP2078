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
% DateTime   : Thu Dec  3 10:08:04 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 200 expanded)
%              Number of leaves         :   36 (  84 expanded)
%              Depth                    :    9
%              Number of atoms          :  161 ( 481 expanded)
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

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_101,negated_conjecture,(
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

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_70,axiom,(
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

tff(c_18,plain,(
    ! [A_25,B_26] : v1_relat_1(k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_40,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_68,plain,(
    ! [B_91,A_92] :
      ( v1_relat_1(B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_92))
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_71,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_40,c_68])).

tff(c_74,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_71])).

tff(c_168,plain,(
    ! [A_119,B_120,C_121] :
      ( k1_relset_1(A_119,B_120,C_121) = k1_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_172,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_168])).

tff(c_56,plain,
    ( r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8'))
    | m1_subset_1('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_75,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_52,plain,
    ( r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8'))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_87,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_8,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k1_relat_1(A_6))
      | ~ r2_hidden(k4_tarski(C_21,D_24),A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_94,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_87,c_8])).

tff(c_102,plain,(
    ! [A_105,B_106,C_107] :
      ( k1_relset_1(A_105,B_106,C_107) = k1_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_106,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_102])).

tff(c_46,plain,(
    ! [E_85] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_85),'#skF_8')
      | ~ m1_subset_1(E_85,'#skF_7')
      | ~ r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_145,plain,(
    ! [E_115] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_115),'#skF_8')
      | ~ m1_subset_1(E_115,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_106,c_46])).

tff(c_152,plain,(
    ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_87,c_145])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_152])).

tff(c_160,plain,(
    r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_174,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_160])).

tff(c_76,plain,(
    ! [C_93,B_94,A_95] :
      ( v5_relat_1(C_93,B_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_80,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_76])).

tff(c_28,plain,(
    ! [A_33] :
      ( k10_relat_1(A_33,k2_relat_1(A_33)) = k1_relat_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_245,plain,(
    ! [A_132,B_133,C_134] :
      ( r2_hidden('#skF_5'(A_132,B_133,C_134),k2_relat_1(C_134))
      | ~ r2_hidden(A_132,k10_relat_1(C_134,B_133))
      | ~ v1_relat_1(C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [C_37,A_34,B_35] :
      ( r2_hidden(C_37,A_34)
      | ~ r2_hidden(C_37,k2_relat_1(B_35))
      | ~ v5_relat_1(B_35,A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_480,plain,(
    ! [A_169,B_170,C_171,A_172] :
      ( r2_hidden('#skF_5'(A_169,B_170,C_171),A_172)
      | ~ v5_relat_1(C_171,A_172)
      | ~ r2_hidden(A_169,k10_relat_1(C_171,B_170))
      | ~ v1_relat_1(C_171) ) ),
    inference(resolution,[status(thm)],[c_245,c_30])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_536,plain,(
    ! [A_179,B_180,C_181,A_182] :
      ( m1_subset_1('#skF_5'(A_179,B_180,C_181),A_182)
      | ~ v5_relat_1(C_181,A_182)
      | ~ r2_hidden(A_179,k10_relat_1(C_181,B_180))
      | ~ v1_relat_1(C_181) ) ),
    inference(resolution,[status(thm)],[c_480,c_2])).

tff(c_740,plain,(
    ! [A_203,A_204,A_205] :
      ( m1_subset_1('#skF_5'(A_203,k2_relat_1(A_204),A_204),A_205)
      | ~ v5_relat_1(A_204,A_205)
      | ~ r2_hidden(A_203,k1_relat_1(A_204))
      | ~ v1_relat_1(A_204)
      | ~ v1_relat_1(A_204) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_536])).

tff(c_273,plain,(
    ! [A_146,B_147,C_148] :
      ( r2_hidden(k4_tarski(A_146,'#skF_5'(A_146,B_147,C_148)),C_148)
      | ~ r2_hidden(A_146,k10_relat_1(C_148,B_147))
      | ~ v1_relat_1(C_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_161,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,(
    ! [E_85] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_85),'#skF_8')
      | ~ m1_subset_1(E_85,'#skF_7')
      | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_184,plain,(
    ! [E_85] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_85),'#skF_8')
      | ~ m1_subset_1(E_85,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_50])).

tff(c_280,plain,(
    ! [B_147] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_147,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_147))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_273,c_184])).

tff(c_321,plain,(
    ! [B_152] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_152,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_152)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_280])).

tff(c_325,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_9',k2_relat_1('#skF_8'),'#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_321])).

tff(c_327,plain,(
    ~ m1_subset_1('#skF_5'('#skF_9',k2_relat_1('#skF_8'),'#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_174,c_325])).

tff(c_743,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_740,c_327])).

tff(c_763,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_174,c_80,c_743])).

tff(c_765,plain,(
    ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_785,plain,(
    ! [A_219,B_220,C_221] :
      ( k1_relset_1(A_219,B_220,C_221) = k1_relat_1(C_221)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_789,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_785])).

tff(c_764,plain,(
    r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_791,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_789,c_764])).

tff(c_778,plain,(
    ! [C_213,B_214,A_215] :
      ( v5_relat_1(C_213,B_214)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_215,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_782,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_778])).

tff(c_878,plain,(
    ! [A_236,B_237,C_238] :
      ( r2_hidden('#skF_5'(A_236,B_237,C_238),k2_relat_1(C_238))
      | ~ r2_hidden(A_236,k10_relat_1(C_238,B_237))
      | ~ v1_relat_1(C_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_964,plain,(
    ! [A_255,B_256,C_257,A_258] :
      ( r2_hidden('#skF_5'(A_255,B_256,C_257),A_258)
      | ~ v5_relat_1(C_257,A_258)
      | ~ r2_hidden(A_255,k10_relat_1(C_257,B_256))
      | ~ v1_relat_1(C_257) ) ),
    inference(resolution,[status(thm)],[c_878,c_30])).

tff(c_983,plain,(
    ! [A_261,B_262,C_263,A_264] :
      ( m1_subset_1('#skF_5'(A_261,B_262,C_263),A_264)
      | ~ v5_relat_1(C_263,A_264)
      | ~ r2_hidden(A_261,k10_relat_1(C_263,B_262))
      | ~ v1_relat_1(C_263) ) ),
    inference(resolution,[status(thm)],[c_964,c_2])).

tff(c_1322,plain,(
    ! [A_296,A_297,A_298] :
      ( m1_subset_1('#skF_5'(A_296,k2_relat_1(A_297),A_297),A_298)
      | ~ v5_relat_1(A_297,A_298)
      | ~ r2_hidden(A_296,k1_relat_1(A_297))
      | ~ v1_relat_1(A_297)
      | ~ v1_relat_1(A_297) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_983])).

tff(c_888,plain,(
    ! [A_245,B_246,C_247] :
      ( r2_hidden(k4_tarski(A_245,'#skF_5'(A_245,B_246,C_247)),C_247)
      | ~ r2_hidden(A_245,k10_relat_1(C_247,B_246))
      | ~ v1_relat_1(C_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_54,plain,(
    ! [E_85] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_85),'#skF_8')
      | ~ m1_subset_1(E_85,'#skF_7')
      | m1_subset_1('#skF_10','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_766,plain,(
    ! [E_85] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_85),'#skF_8')
      | ~ m1_subset_1(E_85,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_901,plain,(
    ! [B_246] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_246,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_246))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_888,c_766])).

tff(c_936,plain,(
    ! [B_251] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_251,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_251)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_901])).

tff(c_940,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_9',k2_relat_1('#skF_8'),'#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_936])).

tff(c_942,plain,(
    ~ m1_subset_1('#skF_5'('#skF_9',k2_relat_1('#skF_8'),'#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_791,c_940])).

tff(c_1325,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1322,c_942])).

tff(c_1345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_791,c_782,c_1325])).

tff(c_1346,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_765,c_1346])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.43/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.58  
% 3.43/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.58  %$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 3.43/1.58  
% 3.43/1.58  %Foreground sorts:
% 3.43/1.58  
% 3.43/1.58  
% 3.43/1.58  %Background operators:
% 3.43/1.58  
% 3.43/1.58  
% 3.43/1.58  %Foreground operators:
% 3.43/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.43/1.58  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.43/1.58  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.43/1.58  tff('#skF_7', type, '#skF_7': $i).
% 3.43/1.58  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.43/1.58  tff('#skF_10', type, '#skF_10': $i).
% 3.43/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.43/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.43/1.58  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.43/1.58  tff('#skF_9', type, '#skF_9': $i).
% 3.43/1.58  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.43/1.58  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.43/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.43/1.58  tff('#skF_8', type, '#skF_8': $i).
% 3.43/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.58  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.43/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.43/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.43/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.43/1.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.43/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.43/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.43/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.43/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.43/1.58  
% 3.43/1.60  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.43/1.60  tff(f_101, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, A) => (r2_hidden(D, k1_relset_1(A, B, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(D, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relset_1)).
% 3.43/1.60  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.43/1.60  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.43/1.60  tff(f_44, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.43/1.60  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.43/1.60  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.43/1.60  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 3.43/1.60  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t202_relat_1)).
% 3.43/1.60  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.43/1.60  tff(c_18, plain, (![A_25, B_26]: (v1_relat_1(k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.43/1.60  tff(c_40, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.43/1.60  tff(c_68, plain, (![B_91, A_92]: (v1_relat_1(B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(A_92)) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.43/1.60  tff(c_71, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_40, c_68])).
% 3.43/1.60  tff(c_74, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_71])).
% 3.43/1.60  tff(c_168, plain, (![A_119, B_120, C_121]: (k1_relset_1(A_119, B_120, C_121)=k1_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.43/1.60  tff(c_172, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_40, c_168])).
% 3.43/1.60  tff(c_56, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8')) | m1_subset_1('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.43/1.60  tff(c_75, plain, (m1_subset_1('#skF_10', '#skF_7')), inference(splitLeft, [status(thm)], [c_56])).
% 3.43/1.60  tff(c_52, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8')) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.43/1.60  tff(c_87, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(splitLeft, [status(thm)], [c_52])).
% 3.43/1.60  tff(c_8, plain, (![C_21, A_6, D_24]: (r2_hidden(C_21, k1_relat_1(A_6)) | ~r2_hidden(k4_tarski(C_21, D_24), A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.43/1.60  tff(c_94, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_87, c_8])).
% 3.43/1.60  tff(c_102, plain, (![A_105, B_106, C_107]: (k1_relset_1(A_105, B_106, C_107)=k1_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.43/1.60  tff(c_106, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_40, c_102])).
% 3.43/1.60  tff(c_46, plain, (![E_85]: (~r2_hidden(k4_tarski('#skF_9', E_85), '#skF_8') | ~m1_subset_1(E_85, '#skF_7') | ~r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.43/1.60  tff(c_145, plain, (![E_115]: (~r2_hidden(k4_tarski('#skF_9', E_115), '#skF_8') | ~m1_subset_1(E_115, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_106, c_46])).
% 3.43/1.60  tff(c_152, plain, (~m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_87, c_145])).
% 3.43/1.60  tff(c_159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_75, c_152])).
% 3.43/1.60  tff(c_160, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_52])).
% 3.43/1.60  tff(c_174, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_160])).
% 3.43/1.60  tff(c_76, plain, (![C_93, B_94, A_95]: (v5_relat_1(C_93, B_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.43/1.60  tff(c_80, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_40, c_76])).
% 3.43/1.60  tff(c_28, plain, (![A_33]: (k10_relat_1(A_33, k2_relat_1(A_33))=k1_relat_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.43/1.60  tff(c_245, plain, (![A_132, B_133, C_134]: (r2_hidden('#skF_5'(A_132, B_133, C_134), k2_relat_1(C_134)) | ~r2_hidden(A_132, k10_relat_1(C_134, B_133)) | ~v1_relat_1(C_134))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.43/1.60  tff(c_30, plain, (![C_37, A_34, B_35]: (r2_hidden(C_37, A_34) | ~r2_hidden(C_37, k2_relat_1(B_35)) | ~v5_relat_1(B_35, A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.43/1.60  tff(c_480, plain, (![A_169, B_170, C_171, A_172]: (r2_hidden('#skF_5'(A_169, B_170, C_171), A_172) | ~v5_relat_1(C_171, A_172) | ~r2_hidden(A_169, k10_relat_1(C_171, B_170)) | ~v1_relat_1(C_171))), inference(resolution, [status(thm)], [c_245, c_30])).
% 3.43/1.60  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.43/1.60  tff(c_536, plain, (![A_179, B_180, C_181, A_182]: (m1_subset_1('#skF_5'(A_179, B_180, C_181), A_182) | ~v5_relat_1(C_181, A_182) | ~r2_hidden(A_179, k10_relat_1(C_181, B_180)) | ~v1_relat_1(C_181))), inference(resolution, [status(thm)], [c_480, c_2])).
% 3.43/1.60  tff(c_740, plain, (![A_203, A_204, A_205]: (m1_subset_1('#skF_5'(A_203, k2_relat_1(A_204), A_204), A_205) | ~v5_relat_1(A_204, A_205) | ~r2_hidden(A_203, k1_relat_1(A_204)) | ~v1_relat_1(A_204) | ~v1_relat_1(A_204))), inference(superposition, [status(thm), theory('equality')], [c_28, c_536])).
% 3.43/1.60  tff(c_273, plain, (![A_146, B_147, C_148]: (r2_hidden(k4_tarski(A_146, '#skF_5'(A_146, B_147, C_148)), C_148) | ~r2_hidden(A_146, k10_relat_1(C_148, B_147)) | ~v1_relat_1(C_148))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.43/1.60  tff(c_161, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(splitRight, [status(thm)], [c_52])).
% 3.43/1.60  tff(c_50, plain, (![E_85]: (~r2_hidden(k4_tarski('#skF_9', E_85), '#skF_8') | ~m1_subset_1(E_85, '#skF_7') | r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.43/1.60  tff(c_184, plain, (![E_85]: (~r2_hidden(k4_tarski('#skF_9', E_85), '#skF_8') | ~m1_subset_1(E_85, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_161, c_50])).
% 3.43/1.60  tff(c_280, plain, (![B_147]: (~m1_subset_1('#skF_5'('#skF_9', B_147, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_147)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_273, c_184])).
% 3.43/1.60  tff(c_321, plain, (![B_152]: (~m1_subset_1('#skF_5'('#skF_9', B_152, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_152)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_280])).
% 3.43/1.60  tff(c_325, plain, (~m1_subset_1('#skF_5'('#skF_9', k2_relat_1('#skF_8'), '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_28, c_321])).
% 3.43/1.60  tff(c_327, plain, (~m1_subset_1('#skF_5'('#skF_9', k2_relat_1('#skF_8'), '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_174, c_325])).
% 3.43/1.60  tff(c_743, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_740, c_327])).
% 3.43/1.60  tff(c_763, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_174, c_80, c_743])).
% 3.43/1.60  tff(c_765, plain, (~m1_subset_1('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_56])).
% 3.43/1.60  tff(c_785, plain, (![A_219, B_220, C_221]: (k1_relset_1(A_219, B_220, C_221)=k1_relat_1(C_221) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.43/1.60  tff(c_789, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_40, c_785])).
% 3.43/1.60  tff(c_764, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_56])).
% 3.43/1.60  tff(c_791, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_789, c_764])).
% 3.43/1.60  tff(c_778, plain, (![C_213, B_214, A_215]: (v5_relat_1(C_213, B_214) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_215, B_214))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.43/1.60  tff(c_782, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_40, c_778])).
% 3.43/1.60  tff(c_878, plain, (![A_236, B_237, C_238]: (r2_hidden('#skF_5'(A_236, B_237, C_238), k2_relat_1(C_238)) | ~r2_hidden(A_236, k10_relat_1(C_238, B_237)) | ~v1_relat_1(C_238))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.43/1.60  tff(c_964, plain, (![A_255, B_256, C_257, A_258]: (r2_hidden('#skF_5'(A_255, B_256, C_257), A_258) | ~v5_relat_1(C_257, A_258) | ~r2_hidden(A_255, k10_relat_1(C_257, B_256)) | ~v1_relat_1(C_257))), inference(resolution, [status(thm)], [c_878, c_30])).
% 3.43/1.60  tff(c_983, plain, (![A_261, B_262, C_263, A_264]: (m1_subset_1('#skF_5'(A_261, B_262, C_263), A_264) | ~v5_relat_1(C_263, A_264) | ~r2_hidden(A_261, k10_relat_1(C_263, B_262)) | ~v1_relat_1(C_263))), inference(resolution, [status(thm)], [c_964, c_2])).
% 3.43/1.60  tff(c_1322, plain, (![A_296, A_297, A_298]: (m1_subset_1('#skF_5'(A_296, k2_relat_1(A_297), A_297), A_298) | ~v5_relat_1(A_297, A_298) | ~r2_hidden(A_296, k1_relat_1(A_297)) | ~v1_relat_1(A_297) | ~v1_relat_1(A_297))), inference(superposition, [status(thm), theory('equality')], [c_28, c_983])).
% 3.43/1.60  tff(c_888, plain, (![A_245, B_246, C_247]: (r2_hidden(k4_tarski(A_245, '#skF_5'(A_245, B_246, C_247)), C_247) | ~r2_hidden(A_245, k10_relat_1(C_247, B_246)) | ~v1_relat_1(C_247))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.43/1.60  tff(c_54, plain, (![E_85]: (~r2_hidden(k4_tarski('#skF_9', E_85), '#skF_8') | ~m1_subset_1(E_85, '#skF_7') | m1_subset_1('#skF_10', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.43/1.60  tff(c_766, plain, (![E_85]: (~r2_hidden(k4_tarski('#skF_9', E_85), '#skF_8') | ~m1_subset_1(E_85, '#skF_7'))), inference(splitLeft, [status(thm)], [c_54])).
% 3.43/1.60  tff(c_901, plain, (![B_246]: (~m1_subset_1('#skF_5'('#skF_9', B_246, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_246)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_888, c_766])).
% 3.43/1.60  tff(c_936, plain, (![B_251]: (~m1_subset_1('#skF_5'('#skF_9', B_251, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_251)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_901])).
% 3.43/1.60  tff(c_940, plain, (~m1_subset_1('#skF_5'('#skF_9', k2_relat_1('#skF_8'), '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_28, c_936])).
% 3.43/1.60  tff(c_942, plain, (~m1_subset_1('#skF_5'('#skF_9', k2_relat_1('#skF_8'), '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_791, c_940])).
% 3.43/1.60  tff(c_1325, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_1322, c_942])).
% 3.43/1.60  tff(c_1345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_791, c_782, c_1325])).
% 3.43/1.60  tff(c_1346, plain, (m1_subset_1('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_54])).
% 3.43/1.60  tff(c_1347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_765, c_1346])).
% 3.43/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.60  
% 3.43/1.60  Inference rules
% 3.43/1.60  ----------------------
% 3.43/1.60  #Ref     : 0
% 3.43/1.60  #Sup     : 276
% 3.43/1.60  #Fact    : 0
% 3.43/1.60  #Define  : 0
% 3.43/1.60  #Split   : 5
% 3.43/1.60  #Chain   : 0
% 3.43/1.60  #Close   : 0
% 3.43/1.60  
% 3.43/1.60  Ordering : KBO
% 3.43/1.60  
% 3.43/1.60  Simplification rules
% 3.43/1.60  ----------------------
% 3.43/1.60  #Subsume      : 7
% 3.43/1.60  #Demod        : 35
% 3.43/1.60  #Tautology    : 30
% 3.43/1.60  #SimpNegUnit  : 2
% 3.43/1.60  #BackRed      : 4
% 3.43/1.60  
% 3.43/1.60  #Partial instantiations: 0
% 3.43/1.60  #Strategies tried      : 1
% 3.43/1.60  
% 3.43/1.60  Timing (in seconds)
% 3.43/1.60  ----------------------
% 3.43/1.60  Preprocessing        : 0.33
% 3.43/1.61  Parsing              : 0.17
% 3.43/1.61  CNF conversion       : 0.03
% 3.43/1.61  Main loop            : 0.50
% 3.43/1.61  Inferencing          : 0.19
% 3.43/1.61  Reduction            : 0.13
% 3.43/1.61  Demodulation         : 0.09
% 3.43/1.61  BG Simplification    : 0.03
% 3.43/1.61  Subsumption          : 0.10
% 3.43/1.61  Abstraction          : 0.03
% 3.43/1.61  MUC search           : 0.00
% 3.43/1.61  Cooper               : 0.00
% 3.43/1.61  Total                : 0.87
% 3.43/1.61  Index Insertion      : 0.00
% 3.43/1.61  Index Deletion       : 0.00
% 3.43/1.61  Index Matching       : 0.00
% 3.43/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
