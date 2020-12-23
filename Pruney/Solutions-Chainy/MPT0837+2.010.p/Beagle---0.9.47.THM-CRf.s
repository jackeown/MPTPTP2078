%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:06 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 277 expanded)
%              Number of leaves         :   35 ( 107 expanded)
%              Depth                    :    8
%              Number of atoms          :  204 ( 649 expanded)
%              Number of equality atoms :   29 (  66 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ! [D] :
                    ( r2_hidden(D,k2_relset_1(B,A,C))
                  <=> ? [E] :
                        ( m1_subset_1(E,B)
                        & r2_hidden(k4_tarski(E,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_58,plain,(
    ! [C_107,A_108,B_109] :
      ( v1_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_62,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_58])).

tff(c_516,plain,(
    ! [A_225,B_226,C_227,D_228] :
      ( k7_relset_1(A_225,B_226,C_227,D_228) = k9_relat_1(C_227,D_228)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_225,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_519,plain,(
    ! [D_228] : k7_relset_1('#skF_7','#skF_6','#skF_8',D_228) = k9_relat_1('#skF_8',D_228) ),
    inference(resolution,[status(thm)],[c_40,c_516])).

tff(c_535,plain,(
    ! [A_236,B_237,C_238] :
      ( k7_relset_1(A_236,B_237,C_238,A_236) = k2_relset_1(A_236,B_237,C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_236,B_237))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_537,plain,(
    k7_relset_1('#skF_7','#skF_6','#skF_8','#skF_7') = k2_relset_1('#skF_7','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_535])).

tff(c_539,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k9_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_537])).

tff(c_56,plain,
    ( m1_subset_1('#skF_10','#skF_7')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_68,plain,(
    r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_543,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_68])).

tff(c_279,plain,(
    ! [A_168,B_169,C_170] :
      ( r2_hidden('#skF_5'(A_168,B_169,C_170),B_169)
      | ~ r2_hidden(A_168,k9_relat_1(C_170,B_169))
      | ~ v1_relat_1(C_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_283,plain,(
    ! [A_168,B_169,C_170] :
      ( m1_subset_1('#skF_5'(A_168,B_169,C_170),B_169)
      | ~ r2_hidden(A_168,k9_relat_1(C_170,B_169))
      | ~ v1_relat_1(C_170) ) ),
    inference(resolution,[status(thm)],[c_279,c_2])).

tff(c_549,plain,
    ( m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_543,c_283])).

tff(c_555,plain,(
    m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_549])).

tff(c_576,plain,(
    ! [A_242,B_243,C_244] :
      ( r2_hidden(k4_tarski('#skF_5'(A_242,B_243,C_244),A_242),C_244)
      | ~ r2_hidden(A_242,k9_relat_1(C_244,B_243))
      | ~ v1_relat_1(C_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_102,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( k7_relset_1(A_123,B_124,C_125,D_126) = k9_relat_1(C_125,D_126)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_105,plain,(
    ! [D_126] : k7_relset_1('#skF_7','#skF_6','#skF_8',D_126) = k9_relat_1('#skF_8',D_126) ),
    inference(resolution,[status(thm)],[c_40,c_102])).

tff(c_153,plain,(
    ! [A_139,B_140,C_141] :
      ( k7_relset_1(A_139,B_140,C_141,A_139) = k2_relset_1(A_139,B_140,C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_155,plain,(
    k7_relset_1('#skF_7','#skF_6','#skF_8','#skF_7') = k2_relset_1('#skF_7','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_153])).

tff(c_157,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k9_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_155])).

tff(c_159,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_68])).

tff(c_83,plain,(
    ! [A_114,B_115,C_116] :
      ( r2_hidden('#skF_5'(A_114,B_115,C_116),B_115)
      | ~ r2_hidden(A_114,k9_relat_1(C_116,B_115))
      | ~ v1_relat_1(C_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_87,plain,(
    ! [A_114,B_115,C_116] :
      ( m1_subset_1('#skF_5'(A_114,B_115,C_116),B_115)
      | ~ r2_hidden(A_114,k9_relat_1(C_116,B_115))
      | ~ v1_relat_1(C_116) ) ),
    inference(resolution,[status(thm)],[c_83,c_2])).

tff(c_170,plain,
    ( m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_159,c_87])).

tff(c_178,plain,(
    m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_170])).

tff(c_129,plain,(
    ! [A_135,B_136,C_137] :
      ( r2_hidden(k4_tarski('#skF_5'(A_135,B_136,C_137),A_135),C_137)
      | ~ r2_hidden(A_135,k9_relat_1(C_137,B_136))
      | ~ v1_relat_1(C_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_50,plain,(
    ! [E_104] :
      ( m1_subset_1('#skF_10','#skF_7')
      | ~ r2_hidden(k4_tarski(E_104,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_104,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_74,plain,(
    ! [E_104] :
      ( ~ r2_hidden(k4_tarski(E_104,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_104,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_138,plain,(
    ! [B_136] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_136,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_136))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_129,c_74])).

tff(c_146,plain,(
    ! [B_136] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_136,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_136)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_138])).

tff(c_174,plain,(
    ~ m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_159,c_146])).

tff(c_182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_174])).

tff(c_183,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_207,plain,(
    ! [A_150,B_151,C_152,D_153] :
      ( k7_relset_1(A_150,B_151,C_152,D_153) = k9_relat_1(C_152,D_153)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_210,plain,(
    ! [D_153] : k7_relset_1('#skF_7','#skF_6','#skF_8',D_153) = k9_relat_1('#skF_8',D_153) ),
    inference(resolution,[status(thm)],[c_40,c_207])).

tff(c_226,plain,(
    ! [A_161,B_162,C_163] :
      ( k7_relset_1(A_161,B_162,C_163,A_161) = k2_relset_1(A_161,B_162,C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_228,plain,(
    k7_relset_1('#skF_7','#skF_6','#skF_8','#skF_7') = k2_relset_1('#skF_7','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_226])).

tff(c_230,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k9_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_228])).

tff(c_232,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_68])).

tff(c_193,plain,(
    ! [A_144,B_145,C_146] :
      ( r2_hidden('#skF_5'(A_144,B_145,C_146),B_145)
      | ~ r2_hidden(A_144,k9_relat_1(C_146,B_145))
      | ~ v1_relat_1(C_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_197,plain,(
    ! [A_144,B_145,C_146] :
      ( m1_subset_1('#skF_5'(A_144,B_145,C_146),B_145)
      | ~ r2_hidden(A_144,k9_relat_1(C_146,B_145))
      | ~ v1_relat_1(C_146) ) ),
    inference(resolution,[status(thm)],[c_193,c_2])).

tff(c_238,plain,
    ( m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_232,c_197])).

tff(c_244,plain,(
    m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_238])).

tff(c_247,plain,(
    ! [A_164,B_165,C_166] :
      ( r2_hidden(k4_tarski('#skF_5'(A_164,B_165,C_166),A_164),C_166)
      | ~ r2_hidden(A_164,k9_relat_1(C_166,B_165))
      | ~ v1_relat_1(C_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_48,plain,(
    ! [E_104] :
      ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
      | ~ r2_hidden(k4_tarski(E_104,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_104,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_185,plain,(
    ! [E_104] :
      ( ~ r2_hidden(k4_tarski(E_104,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_104,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_254,plain,(
    ! [B_165] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_165,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_165))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_247,c_185])).

tff(c_263,plain,(
    ! [B_167] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_167,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_167)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_254])).

tff(c_266,plain,(
    ~ m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_232,c_263])).

tff(c_273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_266])).

tff(c_274,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_362,plain,(
    ! [D_194,A_195,B_196,E_197] :
      ( r2_hidden(D_194,k9_relat_1(A_195,B_196))
      | ~ r2_hidden(E_197,B_196)
      | ~ r2_hidden(k4_tarski(E_197,D_194),A_195)
      | ~ v1_relat_1(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_469,plain,(
    ! [D_218,A_219,B_220,A_221] :
      ( r2_hidden(D_218,k9_relat_1(A_219,B_220))
      | ~ r2_hidden(k4_tarski(A_221,D_218),A_219)
      | ~ v1_relat_1(A_219)
      | v1_xboole_0(B_220)
      | ~ m1_subset_1(A_221,B_220) ) ),
    inference(resolution,[status(thm)],[c_4,c_362])).

tff(c_476,plain,(
    ! [B_220] :
      ( r2_hidden('#skF_9',k9_relat_1('#skF_8',B_220))
      | ~ v1_relat_1('#skF_8')
      | v1_xboole_0(B_220)
      | ~ m1_subset_1('#skF_10',B_220) ) ),
    inference(resolution,[status(thm)],[c_274,c_469])).

tff(c_486,plain,(
    ! [B_222] :
      ( r2_hidden('#skF_9',k9_relat_1('#skF_8',B_222))
      | v1_xboole_0(B_222)
      | ~ m1_subset_1('#skF_10',B_222) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_476])).

tff(c_304,plain,(
    ! [A_177,B_178,C_179,D_180] :
      ( k7_relset_1(A_177,B_178,C_179,D_180) = k9_relat_1(C_179,D_180)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_307,plain,(
    ! [D_180] : k7_relset_1('#skF_7','#skF_6','#skF_8',D_180) = k9_relat_1('#skF_8',D_180) ),
    inference(resolution,[status(thm)],[c_40,c_304])).

tff(c_308,plain,(
    ! [A_181,B_182,C_183] :
      ( k7_relset_1(A_181,B_182,C_183,A_181) = k2_relset_1(A_181,B_182,C_183)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_311,plain,(
    k7_relset_1('#skF_7','#skF_6','#skF_8','#skF_7') = k2_relset_1('#skF_7','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_308])).

tff(c_321,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k9_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_311])).

tff(c_46,plain,(
    ! [E_104] :
      ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(E_104,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_104,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_293,plain,(
    ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_323,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_293])).

tff(c_491,plain,
    ( v1_xboole_0('#skF_7')
    | ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_486,c_323])).

tff(c_500,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_491])).

tff(c_502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_500])).

tff(c_503,plain,(
    ! [E_104] :
      ( ~ r2_hidden(k4_tarski(E_104,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_104,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_580,plain,(
    ! [B_243] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_243,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_243))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_576,c_503])).

tff(c_592,plain,(
    ! [B_245] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_245,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_245)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_580])).

tff(c_595,plain,(
    ~ m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_543,c_592])).

tff(c_602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_555,c_595])).

tff(c_603,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_604,plain,(
    ~ r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,
    ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_609,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_604,c_54])).

tff(c_656,plain,(
    ! [D_263,A_264,B_265,E_266] :
      ( r2_hidden(D_263,k9_relat_1(A_264,B_265))
      | ~ r2_hidden(E_266,B_265)
      | ~ r2_hidden(k4_tarski(E_266,D_263),A_264)
      | ~ v1_relat_1(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_771,plain,(
    ! [D_292,A_293,B_294,A_295] :
      ( r2_hidden(D_292,k9_relat_1(A_293,B_294))
      | ~ r2_hidden(k4_tarski(A_295,D_292),A_293)
      | ~ v1_relat_1(A_293)
      | v1_xboole_0(B_294)
      | ~ m1_subset_1(A_295,B_294) ) ),
    inference(resolution,[status(thm)],[c_4,c_656])).

tff(c_775,plain,(
    ! [B_294] :
      ( r2_hidden('#skF_9',k9_relat_1('#skF_8',B_294))
      | ~ v1_relat_1('#skF_8')
      | v1_xboole_0(B_294)
      | ~ m1_subset_1('#skF_10',B_294) ) ),
    inference(resolution,[status(thm)],[c_609,c_771])).

tff(c_784,plain,(
    ! [B_296] :
      ( r2_hidden('#skF_9',k9_relat_1('#skF_8',B_296))
      | v1_xboole_0(B_296)
      | ~ m1_subset_1('#skF_10',B_296) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_775])).

tff(c_642,plain,(
    ! [A_255,B_256,C_257,D_258] :
      ( k7_relset_1(A_255,B_256,C_257,D_258) = k9_relat_1(C_257,D_258)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_645,plain,(
    ! [D_258] : k7_relset_1('#skF_7','#skF_6','#skF_8',D_258) = k9_relat_1('#skF_8',D_258) ),
    inference(resolution,[status(thm)],[c_40,c_642])).

tff(c_675,plain,(
    ! [A_269,B_270,C_271] :
      ( k7_relset_1(A_269,B_270,C_271,A_269) = k2_relset_1(A_269,B_270,C_271)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_269,B_270))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_677,plain,(
    k7_relset_1('#skF_7','#skF_6','#skF_8','#skF_7') = k2_relset_1('#skF_7','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_675])).

tff(c_679,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k9_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_677])).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_615,plain,(
    ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_604,c_52])).

tff(c_682,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_615])).

tff(c_787,plain,
    ( v1_xboole_0('#skF_7')
    | ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_784,c_682])).

tff(c_797,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_603,c_787])).

tff(c_799,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_797])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:16:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.51  
% 3.13/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.51  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 3.13/1.51  
% 3.13/1.51  %Foreground sorts:
% 3.13/1.51  
% 3.13/1.51  
% 3.13/1.51  %Background operators:
% 3.13/1.51  
% 3.13/1.51  
% 3.13/1.51  %Foreground operators:
% 3.13/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.13/1.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.13/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.51  tff('#skF_11', type, '#skF_11': $i).
% 3.13/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.13/1.51  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.13/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.13/1.51  tff('#skF_10', type, '#skF_10': $i).
% 3.13/1.51  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.13/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.13/1.51  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.13/1.51  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.13/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.13/1.51  tff('#skF_9', type, '#skF_9': $i).
% 3.13/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.13/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.51  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.13/1.51  tff('#skF_8', type, '#skF_8': $i).
% 3.13/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.13/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.13/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.13/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.13/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.13/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.51  
% 3.22/1.54  tff(f_92, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relset_1)).
% 3.22/1.54  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.22/1.54  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.22/1.54  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.22/1.54  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 3.22/1.54  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.22/1.54  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.22/1.54  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 3.22/1.54  tff(c_42, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.22/1.54  tff(c_40, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.22/1.54  tff(c_58, plain, (![C_107, A_108, B_109]: (v1_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.22/1.54  tff(c_62, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_40, c_58])).
% 3.22/1.54  tff(c_516, plain, (![A_225, B_226, C_227, D_228]: (k7_relset_1(A_225, B_226, C_227, D_228)=k9_relat_1(C_227, D_228) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_225, B_226))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.22/1.54  tff(c_519, plain, (![D_228]: (k7_relset_1('#skF_7', '#skF_6', '#skF_8', D_228)=k9_relat_1('#skF_8', D_228))), inference(resolution, [status(thm)], [c_40, c_516])).
% 3.22/1.54  tff(c_535, plain, (![A_236, B_237, C_238]: (k7_relset_1(A_236, B_237, C_238, A_236)=k2_relset_1(A_236, B_237, C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_236, B_237))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.22/1.54  tff(c_537, plain, (k7_relset_1('#skF_7', '#skF_6', '#skF_8', '#skF_7')=k2_relset_1('#skF_7', '#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_40, c_535])).
% 3.22/1.54  tff(c_539, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k9_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_519, c_537])).
% 3.22/1.54  tff(c_56, plain, (m1_subset_1('#skF_10', '#skF_7') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.22/1.54  tff(c_68, plain, (r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_56])).
% 3.22/1.54  tff(c_543, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_539, c_68])).
% 3.22/1.54  tff(c_279, plain, (![A_168, B_169, C_170]: (r2_hidden('#skF_5'(A_168, B_169, C_170), B_169) | ~r2_hidden(A_168, k9_relat_1(C_170, B_169)) | ~v1_relat_1(C_170))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.54  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.22/1.54  tff(c_283, plain, (![A_168, B_169, C_170]: (m1_subset_1('#skF_5'(A_168, B_169, C_170), B_169) | ~r2_hidden(A_168, k9_relat_1(C_170, B_169)) | ~v1_relat_1(C_170))), inference(resolution, [status(thm)], [c_279, c_2])).
% 3.22/1.54  tff(c_549, plain, (m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_543, c_283])).
% 3.22/1.54  tff(c_555, plain, (m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_549])).
% 3.22/1.54  tff(c_576, plain, (![A_242, B_243, C_244]: (r2_hidden(k4_tarski('#skF_5'(A_242, B_243, C_244), A_242), C_244) | ~r2_hidden(A_242, k9_relat_1(C_244, B_243)) | ~v1_relat_1(C_244))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.54  tff(c_102, plain, (![A_123, B_124, C_125, D_126]: (k7_relset_1(A_123, B_124, C_125, D_126)=k9_relat_1(C_125, D_126) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.22/1.54  tff(c_105, plain, (![D_126]: (k7_relset_1('#skF_7', '#skF_6', '#skF_8', D_126)=k9_relat_1('#skF_8', D_126))), inference(resolution, [status(thm)], [c_40, c_102])).
% 3.22/1.54  tff(c_153, plain, (![A_139, B_140, C_141]: (k7_relset_1(A_139, B_140, C_141, A_139)=k2_relset_1(A_139, B_140, C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.22/1.54  tff(c_155, plain, (k7_relset_1('#skF_7', '#skF_6', '#skF_8', '#skF_7')=k2_relset_1('#skF_7', '#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_40, c_153])).
% 3.22/1.54  tff(c_157, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k9_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_155])).
% 3.22/1.54  tff(c_159, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_68])).
% 3.22/1.54  tff(c_83, plain, (![A_114, B_115, C_116]: (r2_hidden('#skF_5'(A_114, B_115, C_116), B_115) | ~r2_hidden(A_114, k9_relat_1(C_116, B_115)) | ~v1_relat_1(C_116))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.54  tff(c_87, plain, (![A_114, B_115, C_116]: (m1_subset_1('#skF_5'(A_114, B_115, C_116), B_115) | ~r2_hidden(A_114, k9_relat_1(C_116, B_115)) | ~v1_relat_1(C_116))), inference(resolution, [status(thm)], [c_83, c_2])).
% 3.22/1.54  tff(c_170, plain, (m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_159, c_87])).
% 3.22/1.54  tff(c_178, plain, (m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_170])).
% 3.22/1.54  tff(c_129, plain, (![A_135, B_136, C_137]: (r2_hidden(k4_tarski('#skF_5'(A_135, B_136, C_137), A_135), C_137) | ~r2_hidden(A_135, k9_relat_1(C_137, B_136)) | ~v1_relat_1(C_137))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.54  tff(c_50, plain, (![E_104]: (m1_subset_1('#skF_10', '#skF_7') | ~r2_hidden(k4_tarski(E_104, '#skF_11'), '#skF_8') | ~m1_subset_1(E_104, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.22/1.54  tff(c_74, plain, (![E_104]: (~r2_hidden(k4_tarski(E_104, '#skF_11'), '#skF_8') | ~m1_subset_1(E_104, '#skF_7'))), inference(splitLeft, [status(thm)], [c_50])).
% 3.22/1.54  tff(c_138, plain, (![B_136]: (~m1_subset_1('#skF_5'('#skF_11', B_136, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_136)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_129, c_74])).
% 3.22/1.54  tff(c_146, plain, (![B_136]: (~m1_subset_1('#skF_5'('#skF_11', B_136, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_136)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_138])).
% 3.22/1.54  tff(c_174, plain, (~m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_159, c_146])).
% 3.22/1.54  tff(c_182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_178, c_174])).
% 3.22/1.54  tff(c_183, plain, (m1_subset_1('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_50])).
% 3.22/1.54  tff(c_207, plain, (![A_150, B_151, C_152, D_153]: (k7_relset_1(A_150, B_151, C_152, D_153)=k9_relat_1(C_152, D_153) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.22/1.54  tff(c_210, plain, (![D_153]: (k7_relset_1('#skF_7', '#skF_6', '#skF_8', D_153)=k9_relat_1('#skF_8', D_153))), inference(resolution, [status(thm)], [c_40, c_207])).
% 3.22/1.54  tff(c_226, plain, (![A_161, B_162, C_163]: (k7_relset_1(A_161, B_162, C_163, A_161)=k2_relset_1(A_161, B_162, C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.22/1.54  tff(c_228, plain, (k7_relset_1('#skF_7', '#skF_6', '#skF_8', '#skF_7')=k2_relset_1('#skF_7', '#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_40, c_226])).
% 3.22/1.54  tff(c_230, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k9_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_228])).
% 3.22/1.54  tff(c_232, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_68])).
% 3.22/1.54  tff(c_193, plain, (![A_144, B_145, C_146]: (r2_hidden('#skF_5'(A_144, B_145, C_146), B_145) | ~r2_hidden(A_144, k9_relat_1(C_146, B_145)) | ~v1_relat_1(C_146))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.54  tff(c_197, plain, (![A_144, B_145, C_146]: (m1_subset_1('#skF_5'(A_144, B_145, C_146), B_145) | ~r2_hidden(A_144, k9_relat_1(C_146, B_145)) | ~v1_relat_1(C_146))), inference(resolution, [status(thm)], [c_193, c_2])).
% 3.22/1.54  tff(c_238, plain, (m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_232, c_197])).
% 3.22/1.54  tff(c_244, plain, (m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_238])).
% 3.22/1.54  tff(c_247, plain, (![A_164, B_165, C_166]: (r2_hidden(k4_tarski('#skF_5'(A_164, B_165, C_166), A_164), C_166) | ~r2_hidden(A_164, k9_relat_1(C_166, B_165)) | ~v1_relat_1(C_166))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.54  tff(c_48, plain, (![E_104]: (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | ~r2_hidden(k4_tarski(E_104, '#skF_11'), '#skF_8') | ~m1_subset_1(E_104, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.22/1.54  tff(c_185, plain, (![E_104]: (~r2_hidden(k4_tarski(E_104, '#skF_11'), '#skF_8') | ~m1_subset_1(E_104, '#skF_7'))), inference(splitLeft, [status(thm)], [c_48])).
% 3.22/1.54  tff(c_254, plain, (![B_165]: (~m1_subset_1('#skF_5'('#skF_11', B_165, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_165)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_247, c_185])).
% 3.22/1.54  tff(c_263, plain, (![B_167]: (~m1_subset_1('#skF_5'('#skF_11', B_167, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_167)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_254])).
% 3.22/1.54  tff(c_266, plain, (~m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_232, c_263])).
% 3.22/1.54  tff(c_273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_244, c_266])).
% 3.22/1.54  tff(c_274, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_48])).
% 3.22/1.54  tff(c_4, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.54  tff(c_362, plain, (![D_194, A_195, B_196, E_197]: (r2_hidden(D_194, k9_relat_1(A_195, B_196)) | ~r2_hidden(E_197, B_196) | ~r2_hidden(k4_tarski(E_197, D_194), A_195) | ~v1_relat_1(A_195))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.22/1.54  tff(c_469, plain, (![D_218, A_219, B_220, A_221]: (r2_hidden(D_218, k9_relat_1(A_219, B_220)) | ~r2_hidden(k4_tarski(A_221, D_218), A_219) | ~v1_relat_1(A_219) | v1_xboole_0(B_220) | ~m1_subset_1(A_221, B_220))), inference(resolution, [status(thm)], [c_4, c_362])).
% 3.22/1.54  tff(c_476, plain, (![B_220]: (r2_hidden('#skF_9', k9_relat_1('#skF_8', B_220)) | ~v1_relat_1('#skF_8') | v1_xboole_0(B_220) | ~m1_subset_1('#skF_10', B_220))), inference(resolution, [status(thm)], [c_274, c_469])).
% 3.22/1.54  tff(c_486, plain, (![B_222]: (r2_hidden('#skF_9', k9_relat_1('#skF_8', B_222)) | v1_xboole_0(B_222) | ~m1_subset_1('#skF_10', B_222))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_476])).
% 3.22/1.54  tff(c_304, plain, (![A_177, B_178, C_179, D_180]: (k7_relset_1(A_177, B_178, C_179, D_180)=k9_relat_1(C_179, D_180) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.22/1.54  tff(c_307, plain, (![D_180]: (k7_relset_1('#skF_7', '#skF_6', '#skF_8', D_180)=k9_relat_1('#skF_8', D_180))), inference(resolution, [status(thm)], [c_40, c_304])).
% 3.22/1.54  tff(c_308, plain, (![A_181, B_182, C_183]: (k7_relset_1(A_181, B_182, C_183, A_181)=k2_relset_1(A_181, B_182, C_183) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.22/1.54  tff(c_311, plain, (k7_relset_1('#skF_7', '#skF_6', '#skF_8', '#skF_7')=k2_relset_1('#skF_7', '#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_40, c_308])).
% 3.22/1.54  tff(c_321, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k9_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_307, c_311])).
% 3.22/1.54  tff(c_46, plain, (![E_104]: (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | ~r2_hidden(k4_tarski(E_104, '#skF_11'), '#skF_8') | ~m1_subset_1(E_104, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.22/1.54  tff(c_293, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_46])).
% 3.22/1.54  tff(c_323, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_321, c_293])).
% 3.22/1.54  tff(c_491, plain, (v1_xboole_0('#skF_7') | ~m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_486, c_323])).
% 3.22/1.54  tff(c_500, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_491])).
% 3.22/1.54  tff(c_502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_500])).
% 3.22/1.54  tff(c_503, plain, (![E_104]: (~r2_hidden(k4_tarski(E_104, '#skF_11'), '#skF_8') | ~m1_subset_1(E_104, '#skF_7'))), inference(splitRight, [status(thm)], [c_46])).
% 3.22/1.54  tff(c_580, plain, (![B_243]: (~m1_subset_1('#skF_5'('#skF_11', B_243, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_243)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_576, c_503])).
% 3.22/1.54  tff(c_592, plain, (![B_245]: (~m1_subset_1('#skF_5'('#skF_11', B_245, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_245)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_580])).
% 3.22/1.54  tff(c_595, plain, (~m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_543, c_592])).
% 3.22/1.54  tff(c_602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_555, c_595])).
% 3.22/1.54  tff(c_603, plain, (m1_subset_1('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_56])).
% 3.22/1.54  tff(c_604, plain, (~r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_56])).
% 3.22/1.54  tff(c_54, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.22/1.54  tff(c_609, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_604, c_54])).
% 3.22/1.54  tff(c_656, plain, (![D_263, A_264, B_265, E_266]: (r2_hidden(D_263, k9_relat_1(A_264, B_265)) | ~r2_hidden(E_266, B_265) | ~r2_hidden(k4_tarski(E_266, D_263), A_264) | ~v1_relat_1(A_264))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.22/1.54  tff(c_771, plain, (![D_292, A_293, B_294, A_295]: (r2_hidden(D_292, k9_relat_1(A_293, B_294)) | ~r2_hidden(k4_tarski(A_295, D_292), A_293) | ~v1_relat_1(A_293) | v1_xboole_0(B_294) | ~m1_subset_1(A_295, B_294))), inference(resolution, [status(thm)], [c_4, c_656])).
% 3.22/1.54  tff(c_775, plain, (![B_294]: (r2_hidden('#skF_9', k9_relat_1('#skF_8', B_294)) | ~v1_relat_1('#skF_8') | v1_xboole_0(B_294) | ~m1_subset_1('#skF_10', B_294))), inference(resolution, [status(thm)], [c_609, c_771])).
% 3.22/1.54  tff(c_784, plain, (![B_296]: (r2_hidden('#skF_9', k9_relat_1('#skF_8', B_296)) | v1_xboole_0(B_296) | ~m1_subset_1('#skF_10', B_296))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_775])).
% 3.22/1.54  tff(c_642, plain, (![A_255, B_256, C_257, D_258]: (k7_relset_1(A_255, B_256, C_257, D_258)=k9_relat_1(C_257, D_258) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.22/1.54  tff(c_645, plain, (![D_258]: (k7_relset_1('#skF_7', '#skF_6', '#skF_8', D_258)=k9_relat_1('#skF_8', D_258))), inference(resolution, [status(thm)], [c_40, c_642])).
% 3.22/1.54  tff(c_675, plain, (![A_269, B_270, C_271]: (k7_relset_1(A_269, B_270, C_271, A_269)=k2_relset_1(A_269, B_270, C_271) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_269, B_270))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.22/1.54  tff(c_677, plain, (k7_relset_1('#skF_7', '#skF_6', '#skF_8', '#skF_7')=k2_relset_1('#skF_7', '#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_40, c_675])).
% 3.22/1.54  tff(c_679, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k9_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_645, c_677])).
% 3.22/1.54  tff(c_52, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.22/1.54  tff(c_615, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_604, c_52])).
% 3.22/1.54  tff(c_682, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_679, c_615])).
% 3.22/1.54  tff(c_787, plain, (v1_xboole_0('#skF_7') | ~m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_784, c_682])).
% 3.22/1.54  tff(c_797, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_603, c_787])).
% 3.22/1.54  tff(c_799, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_797])).
% 3.22/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.54  
% 3.22/1.54  Inference rules
% 3.22/1.54  ----------------------
% 3.22/1.54  #Ref     : 0
% 3.22/1.54  #Sup     : 164
% 3.22/1.54  #Fact    : 0
% 3.22/1.54  #Define  : 0
% 3.22/1.54  #Split   : 10
% 3.22/1.54  #Chain   : 0
% 3.22/1.54  #Close   : 0
% 3.22/1.54  
% 3.22/1.54  Ordering : KBO
% 3.22/1.54  
% 3.22/1.54  Simplification rules
% 3.22/1.54  ----------------------
% 3.22/1.54  #Subsume      : 8
% 3.22/1.54  #Demod        : 46
% 3.22/1.54  #Tautology    : 37
% 3.22/1.54  #SimpNegUnit  : 4
% 3.22/1.54  #BackRed      : 16
% 3.22/1.54  
% 3.22/1.54  #Partial instantiations: 0
% 3.22/1.54  #Strategies tried      : 1
% 3.22/1.54  
% 3.22/1.54  Timing (in seconds)
% 3.22/1.54  ----------------------
% 3.22/1.54  Preprocessing        : 0.35
% 3.22/1.54  Parsing              : 0.18
% 3.22/1.54  CNF conversion       : 0.03
% 3.22/1.54  Main loop            : 0.38
% 3.22/1.54  Inferencing          : 0.15
% 3.22/1.54  Reduction            : 0.10
% 3.22/1.54  Demodulation         : 0.07
% 3.22/1.54  BG Simplification    : 0.02
% 3.22/1.54  Subsumption          : 0.07
% 3.22/1.54  Abstraction          : 0.02
% 3.22/1.54  MUC search           : 0.00
% 3.22/1.54  Cooper               : 0.00
% 3.22/1.54  Total                : 0.78
% 3.22/1.54  Index Insertion      : 0.00
% 3.22/1.54  Index Deletion       : 0.00
% 3.22/1.54  Index Matching       : 0.00
% 3.22/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
