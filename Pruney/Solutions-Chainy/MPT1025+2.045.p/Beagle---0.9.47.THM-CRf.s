%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:36 EST 2020

% Result     : Theorem 10.55s
% Output     : CNFRefutation 10.73s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 727 expanded)
%              Number of leaves         :   40 ( 262 expanded)
%              Depth                    :   12
%              Number of atoms          :  355 (1969 expanded)
%              Number of equality atoms :   37 ( 276 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_149,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_130,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ~ v1_xboole_0(C)
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
                 => ! [E] :
                      ( m1_subset_1(E,A)
                     => ( r2_hidden(E,k7_relset_1(C,A,D,B))
                      <=> ? [F] :
                            ( m1_subset_1(F,C)
                            & r2_hidden(k4_tarski(F,E),D)
                            & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_12,plain,(
    ! [A_13,B_14] : v1_relat_1(k2_zfmisc_1(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_54,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_86,plain,(
    ! [B_159,A_160] :
      ( v1_relat_1(B_159)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(A_160))
      | ~ v1_relat_1(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_89,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_54,c_86])).

tff(c_92,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_89])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,(
    ! [A_175,B_176,C_177] :
      ( r2_hidden('#skF_2'(A_175,B_176,C_177),B_176)
      | ~ r2_hidden(A_175,k9_relat_1(C_177,B_176))
      | ~ v1_relat_1(C_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_138,plain,(
    ! [B_181,A_182,C_183] :
      ( ~ v1_xboole_0(B_181)
      | ~ r2_hidden(A_182,k9_relat_1(C_183,B_181))
      | ~ v1_relat_1(C_183) ) ),
    inference(resolution,[status(thm)],[c_122,c_2])).

tff(c_153,plain,(
    ! [B_181,C_183] :
      ( ~ v1_xboole_0(B_181)
      | ~ v1_relat_1(C_183)
      | v1_xboole_0(k9_relat_1(C_183,B_181)) ) ),
    inference(resolution,[status(thm)],[c_4,c_138])).

tff(c_210,plain,(
    ! [A_203,B_204,C_205,D_206] :
      ( k7_relset_1(A_203,B_204,C_205,D_206) = k9_relat_1(C_205,D_206)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_213,plain,(
    ! [D_206] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_206) = k9_relat_1('#skF_9',D_206) ),
    inference(resolution,[status(thm)],[c_54,c_210])).

tff(c_52,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_69,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_52,c_2])).

tff(c_214,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_69])).

tff(c_230,plain,
    ( ~ v1_xboole_0('#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_153,c_214])).

tff(c_236,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_230])).

tff(c_215,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_52])).

tff(c_260,plain,(
    ! [A_208,B_209,C_210,D_211] :
      ( m1_subset_1(k7_relset_1(A_208,B_209,C_210,D_211),k1_zfmisc_1(B_209))
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_279,plain,(
    ! [D_206] :
      ( m1_subset_1(k9_relat_1('#skF_9',D_206),k1_zfmisc_1('#skF_7'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_260])).

tff(c_326,plain,(
    ! [D_214] : m1_subset_1(k9_relat_1('#skF_9',D_214),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_279])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] :
      ( m1_subset_1(A_7,C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_336,plain,(
    ! [A_215,D_216] :
      ( m1_subset_1(A_215,'#skF_7')
      | ~ r2_hidden(A_215,k9_relat_1('#skF_9',D_216)) ) ),
    inference(resolution,[status(thm)],[c_326,c_8])).

tff(c_357,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_215,c_336])).

tff(c_93,plain,(
    ! [C_161,B_162,A_163] :
      ( v1_xboole_0(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(B_162,A_163)))
      | ~ v1_xboole_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_97,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_93])).

tff(c_98,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_107,plain,(
    ! [A_169,B_170,C_171] :
      ( k1_relset_1(A_169,B_170,C_171) = k1_relat_1(C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_111,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_107])).

tff(c_510,plain,(
    ! [A_240,B_241,C_242] :
      ( r2_hidden('#skF_3'(A_240,B_241,C_242),B_241)
      | k1_relset_1(B_241,A_240,C_242) = B_241
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(B_241,A_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_515,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6')
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_54,c_510])).

tff(c_518,plain,
    ( r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6')
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_515])).

tff(c_519,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_518])).

tff(c_188,plain,(
    ! [A_195,B_196,C_197] :
      ( r2_hidden('#skF_2'(A_195,B_196,C_197),k1_relat_1(C_197))
      | ~ r2_hidden(A_195,k9_relat_1(C_197,B_196))
      | ~ v1_relat_1(C_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_192,plain,(
    ! [C_197,A_195,B_196] :
      ( ~ v1_xboole_0(k1_relat_1(C_197))
      | ~ r2_hidden(A_195,k9_relat_1(C_197,B_196))
      | ~ v1_relat_1(C_197) ) ),
    inference(resolution,[status(thm)],[c_188,c_2])).

tff(c_239,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_215,c_192])).

tff(c_251,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_239])).

tff(c_520,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_251])).

tff(c_1076,plain,(
    ! [A_315,B_316,E_317,C_319,D_318] :
      ( m1_subset_1('#skF_5'(A_315,B_316,E_317,D_318,C_319),C_319)
      | ~ r2_hidden(E_317,k7_relset_1(C_319,A_315,D_318,B_316))
      | ~ m1_subset_1(E_317,A_315)
      | ~ m1_subset_1(D_318,k1_zfmisc_1(k2_zfmisc_1(C_319,A_315)))
      | v1_xboole_0(C_319)
      | v1_xboole_0(B_316)
      | v1_xboole_0(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1087,plain,(
    ! [D_206,E_317] :
      ( m1_subset_1('#skF_5'('#skF_7',D_206,E_317,'#skF_9','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_317,k9_relat_1('#skF_9',D_206))
      | ~ m1_subset_1(E_317,'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_206)
      | v1_xboole_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_1076])).

tff(c_1101,plain,(
    ! [D_206,E_317] :
      ( m1_subset_1('#skF_5'('#skF_7',D_206,E_317,'#skF_9','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_317,k9_relat_1('#skF_9',D_206))
      | ~ m1_subset_1(E_317,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_206)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1087])).

tff(c_1741,plain,(
    ! [D_397,E_398] :
      ( m1_subset_1('#skF_5'('#skF_7',D_397,E_398,'#skF_9','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_398,k9_relat_1('#skF_9',D_397))
      | ~ m1_subset_1(E_398,'#skF_7')
      | v1_xboole_0(D_397) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_520,c_1101])).

tff(c_1768,plain,
    ( m1_subset_1('#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_215,c_1741])).

tff(c_1792,plain,
    ( m1_subset_1('#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_1768])).

tff(c_1793,plain,(
    m1_subset_1('#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_1792])).

tff(c_1316,plain,(
    ! [D_350,A_347,C_351,E_349,B_348] :
      ( r2_hidden('#skF_5'(A_347,B_348,E_349,D_350,C_351),B_348)
      | ~ r2_hidden(E_349,k7_relset_1(C_351,A_347,D_350,B_348))
      | ~ m1_subset_1(E_349,A_347)
      | ~ m1_subset_1(D_350,k1_zfmisc_1(k2_zfmisc_1(C_351,A_347)))
      | v1_xboole_0(C_351)
      | v1_xboole_0(B_348)
      | v1_xboole_0(A_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1321,plain,(
    ! [B_348,E_349] :
      ( r2_hidden('#skF_5'('#skF_7',B_348,E_349,'#skF_9','#skF_6'),B_348)
      | ~ r2_hidden(E_349,k7_relset_1('#skF_6','#skF_7','#skF_9',B_348))
      | ~ m1_subset_1(E_349,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_348)
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_54,c_1316])).

tff(c_1324,plain,(
    ! [B_348,E_349] :
      ( r2_hidden('#skF_5'('#skF_7',B_348,E_349,'#skF_9','#skF_6'),B_348)
      | ~ r2_hidden(E_349,k9_relat_1('#skF_9',B_348))
      | ~ m1_subset_1(E_349,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_348)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_1321])).

tff(c_1400,plain,(
    ! [B_376,E_377] :
      ( r2_hidden('#skF_5'('#skF_7',B_376,E_377,'#skF_9','#skF_6'),B_376)
      | ~ r2_hidden(E_377,k9_relat_1('#skF_9',B_376))
      | ~ m1_subset_1(E_377,'#skF_7')
      | v1_xboole_0(B_376) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_520,c_1324])).

tff(c_50,plain,(
    ! [F_150] :
      ( k1_funct_1('#skF_9',F_150) != '#skF_10'
      | ~ r2_hidden(F_150,'#skF_8')
      | ~ m1_subset_1(F_150,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1489,plain,(
    ! [E_377] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_8',E_377,'#skF_9','#skF_6')) != '#skF_10'
      | ~ m1_subset_1('#skF_5'('#skF_7','#skF_8',E_377,'#skF_9','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_377,k9_relat_1('#skF_9','#skF_8'))
      | ~ m1_subset_1(E_377,'#skF_7')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1400,c_50])).

tff(c_1947,plain,(
    ! [E_421] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_8',E_421,'#skF_9','#skF_6')) != '#skF_10'
      | ~ m1_subset_1('#skF_5'('#skF_7','#skF_8',E_421,'#skF_9','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_421,k9_relat_1('#skF_9','#skF_8'))
      | ~ m1_subset_1(E_421,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_1489])).

tff(c_1970,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6')) != '#skF_10'
    | ~ m1_subset_1('#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_215,c_1947])).

tff(c_1992,plain,(
    k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6')) != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_1793,c_1970])).

tff(c_58,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1561,plain,(
    ! [A_381,D_384,E_383,B_382,C_385] :
      ( r2_hidden(k4_tarski('#skF_5'(A_381,B_382,E_383,D_384,C_385),E_383),D_384)
      | ~ r2_hidden(E_383,k7_relset_1(C_385,A_381,D_384,B_382))
      | ~ m1_subset_1(E_383,A_381)
      | ~ m1_subset_1(D_384,k1_zfmisc_1(k2_zfmisc_1(C_385,A_381)))
      | v1_xboole_0(C_385)
      | v1_xboole_0(B_382)
      | v1_xboole_0(A_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_24,plain,(
    ! [C_23,A_21,B_22] :
      ( k1_funct_1(C_23,A_21) = B_22
      | ~ r2_hidden(k4_tarski(A_21,B_22),C_23)
      | ~ v1_funct_1(C_23)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_7552,plain,(
    ! [E_814,B_818,A_816,D_817,C_815] :
      ( k1_funct_1(D_817,'#skF_5'(A_816,B_818,E_814,D_817,C_815)) = E_814
      | ~ v1_funct_1(D_817)
      | ~ v1_relat_1(D_817)
      | ~ r2_hidden(E_814,k7_relset_1(C_815,A_816,D_817,B_818))
      | ~ m1_subset_1(E_814,A_816)
      | ~ m1_subset_1(D_817,k1_zfmisc_1(k2_zfmisc_1(C_815,A_816)))
      | v1_xboole_0(C_815)
      | v1_xboole_0(B_818)
      | v1_xboole_0(A_816) ) ),
    inference(resolution,[status(thm)],[c_1561,c_24])).

tff(c_7572,plain,(
    ! [D_206,E_814] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7',D_206,E_814,'#skF_9','#skF_6')) = E_814
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(E_814,k9_relat_1('#skF_9',D_206))
      | ~ m1_subset_1(E_814,'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_206)
      | v1_xboole_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_7552])).

tff(c_7589,plain,(
    ! [D_206,E_814] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7',D_206,E_814,'#skF_9','#skF_6')) = E_814
      | ~ r2_hidden(E_814,k9_relat_1('#skF_9',D_206))
      | ~ m1_subset_1(E_814,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_206)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_92,c_58,c_7572])).

tff(c_7660,plain,(
    ! [D_820,E_821] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7',D_820,E_821,'#skF_9','#skF_6')) = E_821
      | ~ r2_hidden(E_821,k9_relat_1('#skF_9',D_820))
      | ~ m1_subset_1(E_821,'#skF_7')
      | v1_xboole_0(D_820) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_520,c_7589])).

tff(c_7757,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6')) = '#skF_10'
    | ~ m1_subset_1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_215,c_7660])).

tff(c_7850,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6')) = '#skF_10'
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_7757])).

tff(c_7852,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_1992,c_7850])).

tff(c_7853,plain,(
    r2_hidden('#skF_3'('#skF_7','#skF_6','#skF_9'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_518])).

tff(c_7859,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_7853,c_2])).

tff(c_8503,plain,(
    ! [C_927,B_924,A_923,D_926,E_925] :
      ( m1_subset_1('#skF_5'(A_923,B_924,E_925,D_926,C_927),C_927)
      | ~ r2_hidden(E_925,k7_relset_1(C_927,A_923,D_926,B_924))
      | ~ m1_subset_1(E_925,A_923)
      | ~ m1_subset_1(D_926,k1_zfmisc_1(k2_zfmisc_1(C_927,A_923)))
      | v1_xboole_0(C_927)
      | v1_xboole_0(B_924)
      | v1_xboole_0(A_923) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_8514,plain,(
    ! [D_206,E_925] :
      ( m1_subset_1('#skF_5'('#skF_7',D_206,E_925,'#skF_9','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_925,k9_relat_1('#skF_9',D_206))
      | ~ m1_subset_1(E_925,'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_206)
      | v1_xboole_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_8503])).

tff(c_8528,plain,(
    ! [D_206,E_925] :
      ( m1_subset_1('#skF_5'('#skF_7',D_206,E_925,'#skF_9','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_925,k9_relat_1('#skF_9',D_206))
      | ~ m1_subset_1(E_925,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_206)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_8514])).

tff(c_9031,plain,(
    ! [D_979,E_980] :
      ( m1_subset_1('#skF_5'('#skF_7',D_979,E_980,'#skF_9','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_980,k9_relat_1('#skF_9',D_979))
      | ~ m1_subset_1(E_980,'#skF_7')
      | v1_xboole_0(D_979) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_7859,c_8528])).

tff(c_9058,plain,
    ( m1_subset_1('#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_215,c_9031])).

tff(c_9082,plain,
    ( m1_subset_1('#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_9058])).

tff(c_9083,plain,(
    m1_subset_1('#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_9082])).

tff(c_8383,plain,(
    ! [E_898,C_900,A_896,B_897,D_899] :
      ( r2_hidden('#skF_5'(A_896,B_897,E_898,D_899,C_900),B_897)
      | ~ r2_hidden(E_898,k7_relset_1(C_900,A_896,D_899,B_897))
      | ~ m1_subset_1(E_898,A_896)
      | ~ m1_subset_1(D_899,k1_zfmisc_1(k2_zfmisc_1(C_900,A_896)))
      | v1_xboole_0(C_900)
      | v1_xboole_0(B_897)
      | v1_xboole_0(A_896) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_8388,plain,(
    ! [B_897,E_898] :
      ( r2_hidden('#skF_5'('#skF_7',B_897,E_898,'#skF_9','#skF_6'),B_897)
      | ~ r2_hidden(E_898,k7_relset_1('#skF_6','#skF_7','#skF_9',B_897))
      | ~ m1_subset_1(E_898,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_897)
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_54,c_8383])).

tff(c_8391,plain,(
    ! [B_897,E_898] :
      ( r2_hidden('#skF_5'('#skF_7',B_897,E_898,'#skF_9','#skF_6'),B_897)
      | ~ r2_hidden(E_898,k9_relat_1('#skF_9',B_897))
      | ~ m1_subset_1(E_898,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(B_897)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_8388])).

tff(c_8690,plain,(
    ! [B_958,E_959] :
      ( r2_hidden('#skF_5'('#skF_7',B_958,E_959,'#skF_9','#skF_6'),B_958)
      | ~ r2_hidden(E_959,k9_relat_1('#skF_9',B_958))
      | ~ m1_subset_1(E_959,'#skF_7')
      | v1_xboole_0(B_958) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_7859,c_8391])).

tff(c_8779,plain,(
    ! [E_959] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_8',E_959,'#skF_9','#skF_6')) != '#skF_10'
      | ~ m1_subset_1('#skF_5'('#skF_7','#skF_8',E_959,'#skF_9','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_959,k9_relat_1('#skF_9','#skF_8'))
      | ~ m1_subset_1(E_959,'#skF_7')
      | v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_8690,c_50])).

tff(c_9185,plain,(
    ! [E_994] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_8',E_994,'#skF_9','#skF_6')) != '#skF_10'
      | ~ m1_subset_1('#skF_5'('#skF_7','#skF_8',E_994,'#skF_9','#skF_6'),'#skF_6')
      | ~ r2_hidden(E_994,k9_relat_1('#skF_9','#skF_8'))
      | ~ m1_subset_1(E_994,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_8779])).

tff(c_9208,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6')) != '#skF_10'
    | ~ m1_subset_1('#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_215,c_9185])).

tff(c_9230,plain,(
    k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6')) != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_9083,c_9208])).

tff(c_8810,plain,(
    ! [C_964,B_961,A_960,D_963,E_962] :
      ( r2_hidden(k4_tarski('#skF_5'(A_960,B_961,E_962,D_963,C_964),E_962),D_963)
      | ~ r2_hidden(E_962,k7_relset_1(C_964,A_960,D_963,B_961))
      | ~ m1_subset_1(E_962,A_960)
      | ~ m1_subset_1(D_963,k1_zfmisc_1(k2_zfmisc_1(C_964,A_960)))
      | v1_xboole_0(C_964)
      | v1_xboole_0(B_961)
      | v1_xboole_0(A_960) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_14057,plain,(
    ! [A_1423,C_1421,E_1425,B_1422,D_1424] :
      ( k1_funct_1(D_1424,'#skF_5'(A_1423,B_1422,E_1425,D_1424,C_1421)) = E_1425
      | ~ v1_funct_1(D_1424)
      | ~ v1_relat_1(D_1424)
      | ~ r2_hidden(E_1425,k7_relset_1(C_1421,A_1423,D_1424,B_1422))
      | ~ m1_subset_1(E_1425,A_1423)
      | ~ m1_subset_1(D_1424,k1_zfmisc_1(k2_zfmisc_1(C_1421,A_1423)))
      | v1_xboole_0(C_1421)
      | v1_xboole_0(B_1422)
      | v1_xboole_0(A_1423) ) ),
    inference(resolution,[status(thm)],[c_8810,c_24])).

tff(c_14077,plain,(
    ! [D_206,E_1425] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7',D_206,E_1425,'#skF_9','#skF_6')) = E_1425
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(E_1425,k9_relat_1('#skF_9',D_206))
      | ~ m1_subset_1(E_1425,'#skF_7')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7')))
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_206)
      | v1_xboole_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_14057])).

tff(c_14094,plain,(
    ! [D_206,E_1425] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7',D_206,E_1425,'#skF_9','#skF_6')) = E_1425
      | ~ r2_hidden(E_1425,k9_relat_1('#skF_9',D_206))
      | ~ m1_subset_1(E_1425,'#skF_7')
      | v1_xboole_0('#skF_6')
      | v1_xboole_0(D_206)
      | v1_xboole_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_92,c_58,c_14077])).

tff(c_14099,plain,(
    ! [D_1426,E_1427] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_7',D_1426,E_1427,'#skF_9','#skF_6')) = E_1427
      | ~ r2_hidden(E_1427,k9_relat_1('#skF_9',D_1426))
      | ~ m1_subset_1(E_1427,'#skF_7')
      | v1_xboole_0(D_1426) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_7859,c_14094])).

tff(c_14172,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6')) = '#skF_10'
    | ~ m1_subset_1('#skF_10','#skF_7')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_215,c_14099])).

tff(c_14238,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_7','#skF_8','#skF_10','#skF_9','#skF_6')) = '#skF_10'
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_14172])).

tff(c_14240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_9230,c_14238])).

tff(c_14241,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_14332,plain,(
    ! [A_1459,B_1460,C_1461,D_1462] :
      ( k7_relset_1(A_1459,B_1460,C_1461,D_1462) = k9_relat_1(C_1461,D_1462)
      | ~ m1_subset_1(C_1461,k1_zfmisc_1(k2_zfmisc_1(A_1459,B_1460))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14335,plain,(
    ! [D_1462] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_1462) = k9_relat_1('#skF_9',D_1462) ),
    inference(resolution,[status(thm)],[c_54,c_14332])).

tff(c_14337,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14335,c_52])).

tff(c_14462,plain,(
    ! [A_1482,B_1483,C_1484] :
      ( r2_hidden(k4_tarski('#skF_2'(A_1482,B_1483,C_1484),A_1482),C_1484)
      | ~ r2_hidden(A_1482,k9_relat_1(C_1484,B_1483))
      | ~ v1_relat_1(C_1484) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14505,plain,(
    ! [C_1485,A_1486,B_1487] :
      ( ~ v1_xboole_0(C_1485)
      | ~ r2_hidden(A_1486,k9_relat_1(C_1485,B_1487))
      | ~ v1_relat_1(C_1485) ) ),
    inference(resolution,[status(thm)],[c_14462,c_2])).

tff(c_14512,plain,
    ( ~ v1_xboole_0('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_14337,c_14505])).

tff(c_14529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_14241,c_14512])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:03:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.55/4.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.59/4.33  
% 10.59/4.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.59/4.33  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 10.59/4.33  
% 10.59/4.33  %Foreground sorts:
% 10.59/4.33  
% 10.59/4.33  
% 10.59/4.33  %Background operators:
% 10.59/4.33  
% 10.59/4.33  
% 10.59/4.33  %Foreground operators:
% 10.59/4.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.59/4.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.59/4.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.59/4.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 10.59/4.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.59/4.33  tff('#skF_7', type, '#skF_7': $i).
% 10.59/4.33  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 10.59/4.33  tff('#skF_10', type, '#skF_10': $i).
% 10.59/4.33  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 10.59/4.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.59/4.33  tff('#skF_6', type, '#skF_6': $i).
% 10.59/4.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.59/4.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.59/4.33  tff('#skF_9', type, '#skF_9': $i).
% 10.59/4.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.59/4.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.59/4.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.59/4.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 10.59/4.33  tff('#skF_8', type, '#skF_8': $i).
% 10.59/4.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.59/4.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.59/4.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.59/4.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.59/4.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.59/4.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.59/4.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.59/4.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.59/4.33  
% 10.73/4.35  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.73/4.35  tff(f_149, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 10.73/4.35  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.73/4.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.73/4.35  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 10.73/4.35  tff(f_92, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 10.73/4.35  tff(f_84, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 10.73/4.35  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 10.73/4.35  tff(f_80, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 10.73/4.35  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.73/4.35  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 10.73/4.35  tff(f_130, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 10.73/4.35  tff(f_73, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 10.73/4.35  tff(c_12, plain, (![A_13, B_14]: (v1_relat_1(k2_zfmisc_1(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.73/4.35  tff(c_54, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.73/4.35  tff(c_86, plain, (![B_159, A_160]: (v1_relat_1(B_159) | ~m1_subset_1(B_159, k1_zfmisc_1(A_160)) | ~v1_relat_1(A_160))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.73/4.35  tff(c_89, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_54, c_86])).
% 10.73/4.35  tff(c_92, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_89])).
% 10.73/4.35  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.73/4.35  tff(c_122, plain, (![A_175, B_176, C_177]: (r2_hidden('#skF_2'(A_175, B_176, C_177), B_176) | ~r2_hidden(A_175, k9_relat_1(C_177, B_176)) | ~v1_relat_1(C_177))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.73/4.35  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.73/4.35  tff(c_138, plain, (![B_181, A_182, C_183]: (~v1_xboole_0(B_181) | ~r2_hidden(A_182, k9_relat_1(C_183, B_181)) | ~v1_relat_1(C_183))), inference(resolution, [status(thm)], [c_122, c_2])).
% 10.73/4.35  tff(c_153, plain, (![B_181, C_183]: (~v1_xboole_0(B_181) | ~v1_relat_1(C_183) | v1_xboole_0(k9_relat_1(C_183, B_181)))), inference(resolution, [status(thm)], [c_4, c_138])).
% 10.73/4.35  tff(c_210, plain, (![A_203, B_204, C_205, D_206]: (k7_relset_1(A_203, B_204, C_205, D_206)=k9_relat_1(C_205, D_206) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.73/4.35  tff(c_213, plain, (![D_206]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_206)=k9_relat_1('#skF_9', D_206))), inference(resolution, [status(thm)], [c_54, c_210])).
% 10.73/4.35  tff(c_52, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.73/4.35  tff(c_69, plain, (~v1_xboole_0(k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_52, c_2])).
% 10.73/4.35  tff(c_214, plain, (~v1_xboole_0(k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_69])).
% 10.73/4.35  tff(c_230, plain, (~v1_xboole_0('#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_153, c_214])).
% 10.73/4.35  tff(c_236, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_230])).
% 10.73/4.35  tff(c_215, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_52])).
% 10.73/4.35  tff(c_260, plain, (![A_208, B_209, C_210, D_211]: (m1_subset_1(k7_relset_1(A_208, B_209, C_210, D_211), k1_zfmisc_1(B_209)) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.73/4.35  tff(c_279, plain, (![D_206]: (m1_subset_1(k9_relat_1('#skF_9', D_206), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_213, c_260])).
% 10.73/4.35  tff(c_326, plain, (![D_214]: (m1_subset_1(k9_relat_1('#skF_9', D_214), k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_279])).
% 10.73/4.35  tff(c_8, plain, (![A_7, C_9, B_8]: (m1_subset_1(A_7, C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.73/4.35  tff(c_336, plain, (![A_215, D_216]: (m1_subset_1(A_215, '#skF_7') | ~r2_hidden(A_215, k9_relat_1('#skF_9', D_216)))), inference(resolution, [status(thm)], [c_326, c_8])).
% 10.73/4.35  tff(c_357, plain, (m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_215, c_336])).
% 10.73/4.35  tff(c_93, plain, (![C_161, B_162, A_163]: (v1_xboole_0(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(B_162, A_163))) | ~v1_xboole_0(A_163))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.73/4.35  tff(c_97, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_54, c_93])).
% 10.73/4.35  tff(c_98, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_97])).
% 10.73/4.35  tff(c_107, plain, (![A_169, B_170, C_171]: (k1_relset_1(A_169, B_170, C_171)=k1_relat_1(C_171) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.73/4.35  tff(c_111, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_54, c_107])).
% 10.73/4.35  tff(c_510, plain, (![A_240, B_241, C_242]: (r2_hidden('#skF_3'(A_240, B_241, C_242), B_241) | k1_relset_1(B_241, A_240, C_242)=B_241 | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(B_241, A_240))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.73/4.35  tff(c_515, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6') | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6'), inference(resolution, [status(thm)], [c_54, c_510])).
% 10.73/4.35  tff(c_518, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6') | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_515])).
% 10.73/4.35  tff(c_519, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_518])).
% 10.73/4.35  tff(c_188, plain, (![A_195, B_196, C_197]: (r2_hidden('#skF_2'(A_195, B_196, C_197), k1_relat_1(C_197)) | ~r2_hidden(A_195, k9_relat_1(C_197, B_196)) | ~v1_relat_1(C_197))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.73/4.35  tff(c_192, plain, (![C_197, A_195, B_196]: (~v1_xboole_0(k1_relat_1(C_197)) | ~r2_hidden(A_195, k9_relat_1(C_197, B_196)) | ~v1_relat_1(C_197))), inference(resolution, [status(thm)], [c_188, c_2])).
% 10.73/4.35  tff(c_239, plain, (~v1_xboole_0(k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_215, c_192])).
% 10.73/4.35  tff(c_251, plain, (~v1_xboole_0(k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_239])).
% 10.73/4.35  tff(c_520, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_519, c_251])).
% 10.73/4.35  tff(c_1076, plain, (![A_315, B_316, E_317, C_319, D_318]: (m1_subset_1('#skF_5'(A_315, B_316, E_317, D_318, C_319), C_319) | ~r2_hidden(E_317, k7_relset_1(C_319, A_315, D_318, B_316)) | ~m1_subset_1(E_317, A_315) | ~m1_subset_1(D_318, k1_zfmisc_1(k2_zfmisc_1(C_319, A_315))) | v1_xboole_0(C_319) | v1_xboole_0(B_316) | v1_xboole_0(A_315))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.73/4.35  tff(c_1087, plain, (![D_206, E_317]: (m1_subset_1('#skF_5'('#skF_7', D_206, E_317, '#skF_9', '#skF_6'), '#skF_6') | ~r2_hidden(E_317, k9_relat_1('#skF_9', D_206)) | ~m1_subset_1(E_317, '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0('#skF_6') | v1_xboole_0(D_206) | v1_xboole_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_213, c_1076])).
% 10.73/4.35  tff(c_1101, plain, (![D_206, E_317]: (m1_subset_1('#skF_5'('#skF_7', D_206, E_317, '#skF_9', '#skF_6'), '#skF_6') | ~r2_hidden(E_317, k9_relat_1('#skF_9', D_206)) | ~m1_subset_1(E_317, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(D_206) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1087])).
% 10.73/4.35  tff(c_1741, plain, (![D_397, E_398]: (m1_subset_1('#skF_5'('#skF_7', D_397, E_398, '#skF_9', '#skF_6'), '#skF_6') | ~r2_hidden(E_398, k9_relat_1('#skF_9', D_397)) | ~m1_subset_1(E_398, '#skF_7') | v1_xboole_0(D_397))), inference(negUnitSimplification, [status(thm)], [c_98, c_520, c_1101])).
% 10.73/4.35  tff(c_1768, plain, (m1_subset_1('#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'), '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_215, c_1741])).
% 10.73/4.35  tff(c_1792, plain, (m1_subset_1('#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'), '#skF_6') | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_357, c_1768])).
% 10.73/4.35  tff(c_1793, plain, (m1_subset_1('#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_236, c_1792])).
% 10.73/4.35  tff(c_1316, plain, (![D_350, A_347, C_351, E_349, B_348]: (r2_hidden('#skF_5'(A_347, B_348, E_349, D_350, C_351), B_348) | ~r2_hidden(E_349, k7_relset_1(C_351, A_347, D_350, B_348)) | ~m1_subset_1(E_349, A_347) | ~m1_subset_1(D_350, k1_zfmisc_1(k2_zfmisc_1(C_351, A_347))) | v1_xboole_0(C_351) | v1_xboole_0(B_348) | v1_xboole_0(A_347))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.73/4.35  tff(c_1321, plain, (![B_348, E_349]: (r2_hidden('#skF_5'('#skF_7', B_348, E_349, '#skF_9', '#skF_6'), B_348) | ~r2_hidden(E_349, k7_relset_1('#skF_6', '#skF_7', '#skF_9', B_348)) | ~m1_subset_1(E_349, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(B_348) | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_54, c_1316])).
% 10.73/4.35  tff(c_1324, plain, (![B_348, E_349]: (r2_hidden('#skF_5'('#skF_7', B_348, E_349, '#skF_9', '#skF_6'), B_348) | ~r2_hidden(E_349, k9_relat_1('#skF_9', B_348)) | ~m1_subset_1(E_349, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(B_348) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_1321])).
% 10.73/4.35  tff(c_1400, plain, (![B_376, E_377]: (r2_hidden('#skF_5'('#skF_7', B_376, E_377, '#skF_9', '#skF_6'), B_376) | ~r2_hidden(E_377, k9_relat_1('#skF_9', B_376)) | ~m1_subset_1(E_377, '#skF_7') | v1_xboole_0(B_376))), inference(negUnitSimplification, [status(thm)], [c_98, c_520, c_1324])).
% 10.73/4.35  tff(c_50, plain, (![F_150]: (k1_funct_1('#skF_9', F_150)!='#skF_10' | ~r2_hidden(F_150, '#skF_8') | ~m1_subset_1(F_150, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.73/4.35  tff(c_1489, plain, (![E_377]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_8', E_377, '#skF_9', '#skF_6'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_7', '#skF_8', E_377, '#skF_9', '#skF_6'), '#skF_6') | ~r2_hidden(E_377, k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1(E_377, '#skF_7') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_1400, c_50])).
% 10.73/4.35  tff(c_1947, plain, (![E_421]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_8', E_421, '#skF_9', '#skF_6'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_7', '#skF_8', E_421, '#skF_9', '#skF_6'), '#skF_6') | ~r2_hidden(E_421, k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1(E_421, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_236, c_1489])).
% 10.73/4.35  tff(c_1970, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'), '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_215, c_1947])).
% 10.73/4.35  tff(c_1992, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'))!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_357, c_1793, c_1970])).
% 10.73/4.35  tff(c_58, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.73/4.35  tff(c_1561, plain, (![A_381, D_384, E_383, B_382, C_385]: (r2_hidden(k4_tarski('#skF_5'(A_381, B_382, E_383, D_384, C_385), E_383), D_384) | ~r2_hidden(E_383, k7_relset_1(C_385, A_381, D_384, B_382)) | ~m1_subset_1(E_383, A_381) | ~m1_subset_1(D_384, k1_zfmisc_1(k2_zfmisc_1(C_385, A_381))) | v1_xboole_0(C_385) | v1_xboole_0(B_382) | v1_xboole_0(A_381))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.73/4.35  tff(c_24, plain, (![C_23, A_21, B_22]: (k1_funct_1(C_23, A_21)=B_22 | ~r2_hidden(k4_tarski(A_21, B_22), C_23) | ~v1_funct_1(C_23) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.73/4.35  tff(c_7552, plain, (![E_814, B_818, A_816, D_817, C_815]: (k1_funct_1(D_817, '#skF_5'(A_816, B_818, E_814, D_817, C_815))=E_814 | ~v1_funct_1(D_817) | ~v1_relat_1(D_817) | ~r2_hidden(E_814, k7_relset_1(C_815, A_816, D_817, B_818)) | ~m1_subset_1(E_814, A_816) | ~m1_subset_1(D_817, k1_zfmisc_1(k2_zfmisc_1(C_815, A_816))) | v1_xboole_0(C_815) | v1_xboole_0(B_818) | v1_xboole_0(A_816))), inference(resolution, [status(thm)], [c_1561, c_24])).
% 10.73/4.35  tff(c_7572, plain, (![D_206, E_814]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', D_206, E_814, '#skF_9', '#skF_6'))=E_814 | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(E_814, k9_relat_1('#skF_9', D_206)) | ~m1_subset_1(E_814, '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0('#skF_6') | v1_xboole_0(D_206) | v1_xboole_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_213, c_7552])).
% 10.73/4.35  tff(c_7589, plain, (![D_206, E_814]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', D_206, E_814, '#skF_9', '#skF_6'))=E_814 | ~r2_hidden(E_814, k9_relat_1('#skF_9', D_206)) | ~m1_subset_1(E_814, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(D_206) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_92, c_58, c_7572])).
% 10.73/4.35  tff(c_7660, plain, (![D_820, E_821]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', D_820, E_821, '#skF_9', '#skF_6'))=E_821 | ~r2_hidden(E_821, k9_relat_1('#skF_9', D_820)) | ~m1_subset_1(E_821, '#skF_7') | v1_xboole_0(D_820))), inference(negUnitSimplification, [status(thm)], [c_98, c_520, c_7589])).
% 10.73/4.35  tff(c_7757, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'))='#skF_10' | ~m1_subset_1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_215, c_7660])).
% 10.73/4.35  tff(c_7850, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'))='#skF_10' | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_357, c_7757])).
% 10.73/4.35  tff(c_7852, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_1992, c_7850])).
% 10.73/4.35  tff(c_7853, plain, (r2_hidden('#skF_3'('#skF_7', '#skF_6', '#skF_9'), '#skF_6')), inference(splitRight, [status(thm)], [c_518])).
% 10.73/4.35  tff(c_7859, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_7853, c_2])).
% 10.73/4.35  tff(c_8503, plain, (![C_927, B_924, A_923, D_926, E_925]: (m1_subset_1('#skF_5'(A_923, B_924, E_925, D_926, C_927), C_927) | ~r2_hidden(E_925, k7_relset_1(C_927, A_923, D_926, B_924)) | ~m1_subset_1(E_925, A_923) | ~m1_subset_1(D_926, k1_zfmisc_1(k2_zfmisc_1(C_927, A_923))) | v1_xboole_0(C_927) | v1_xboole_0(B_924) | v1_xboole_0(A_923))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.73/4.35  tff(c_8514, plain, (![D_206, E_925]: (m1_subset_1('#skF_5'('#skF_7', D_206, E_925, '#skF_9', '#skF_6'), '#skF_6') | ~r2_hidden(E_925, k9_relat_1('#skF_9', D_206)) | ~m1_subset_1(E_925, '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0('#skF_6') | v1_xboole_0(D_206) | v1_xboole_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_213, c_8503])).
% 10.73/4.35  tff(c_8528, plain, (![D_206, E_925]: (m1_subset_1('#skF_5'('#skF_7', D_206, E_925, '#skF_9', '#skF_6'), '#skF_6') | ~r2_hidden(E_925, k9_relat_1('#skF_9', D_206)) | ~m1_subset_1(E_925, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(D_206) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_8514])).
% 10.73/4.35  tff(c_9031, plain, (![D_979, E_980]: (m1_subset_1('#skF_5'('#skF_7', D_979, E_980, '#skF_9', '#skF_6'), '#skF_6') | ~r2_hidden(E_980, k9_relat_1('#skF_9', D_979)) | ~m1_subset_1(E_980, '#skF_7') | v1_xboole_0(D_979))), inference(negUnitSimplification, [status(thm)], [c_98, c_7859, c_8528])).
% 10.73/4.35  tff(c_9058, plain, (m1_subset_1('#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'), '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_215, c_9031])).
% 10.73/4.35  tff(c_9082, plain, (m1_subset_1('#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'), '#skF_6') | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_357, c_9058])).
% 10.73/4.35  tff(c_9083, plain, (m1_subset_1('#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_236, c_9082])).
% 10.73/4.35  tff(c_8383, plain, (![E_898, C_900, A_896, B_897, D_899]: (r2_hidden('#skF_5'(A_896, B_897, E_898, D_899, C_900), B_897) | ~r2_hidden(E_898, k7_relset_1(C_900, A_896, D_899, B_897)) | ~m1_subset_1(E_898, A_896) | ~m1_subset_1(D_899, k1_zfmisc_1(k2_zfmisc_1(C_900, A_896))) | v1_xboole_0(C_900) | v1_xboole_0(B_897) | v1_xboole_0(A_896))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.73/4.35  tff(c_8388, plain, (![B_897, E_898]: (r2_hidden('#skF_5'('#skF_7', B_897, E_898, '#skF_9', '#skF_6'), B_897) | ~r2_hidden(E_898, k7_relset_1('#skF_6', '#skF_7', '#skF_9', B_897)) | ~m1_subset_1(E_898, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(B_897) | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_54, c_8383])).
% 10.73/4.35  tff(c_8391, plain, (![B_897, E_898]: (r2_hidden('#skF_5'('#skF_7', B_897, E_898, '#skF_9', '#skF_6'), B_897) | ~r2_hidden(E_898, k9_relat_1('#skF_9', B_897)) | ~m1_subset_1(E_898, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(B_897) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_8388])).
% 10.73/4.35  tff(c_8690, plain, (![B_958, E_959]: (r2_hidden('#skF_5'('#skF_7', B_958, E_959, '#skF_9', '#skF_6'), B_958) | ~r2_hidden(E_959, k9_relat_1('#skF_9', B_958)) | ~m1_subset_1(E_959, '#skF_7') | v1_xboole_0(B_958))), inference(negUnitSimplification, [status(thm)], [c_98, c_7859, c_8391])).
% 10.73/4.35  tff(c_8779, plain, (![E_959]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_8', E_959, '#skF_9', '#skF_6'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_7', '#skF_8', E_959, '#skF_9', '#skF_6'), '#skF_6') | ~r2_hidden(E_959, k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1(E_959, '#skF_7') | v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_8690, c_50])).
% 10.73/4.35  tff(c_9185, plain, (![E_994]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_8', E_994, '#skF_9', '#skF_6'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_7', '#skF_8', E_994, '#skF_9', '#skF_6'), '#skF_6') | ~r2_hidden(E_994, k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1(E_994, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_236, c_8779])).
% 10.73/4.35  tff(c_9208, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'))!='#skF_10' | ~m1_subset_1('#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'), '#skF_6') | ~m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_215, c_9185])).
% 10.73/4.35  tff(c_9230, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'))!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_357, c_9083, c_9208])).
% 10.73/4.35  tff(c_8810, plain, (![C_964, B_961, A_960, D_963, E_962]: (r2_hidden(k4_tarski('#skF_5'(A_960, B_961, E_962, D_963, C_964), E_962), D_963) | ~r2_hidden(E_962, k7_relset_1(C_964, A_960, D_963, B_961)) | ~m1_subset_1(E_962, A_960) | ~m1_subset_1(D_963, k1_zfmisc_1(k2_zfmisc_1(C_964, A_960))) | v1_xboole_0(C_964) | v1_xboole_0(B_961) | v1_xboole_0(A_960))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.73/4.35  tff(c_14057, plain, (![A_1423, C_1421, E_1425, B_1422, D_1424]: (k1_funct_1(D_1424, '#skF_5'(A_1423, B_1422, E_1425, D_1424, C_1421))=E_1425 | ~v1_funct_1(D_1424) | ~v1_relat_1(D_1424) | ~r2_hidden(E_1425, k7_relset_1(C_1421, A_1423, D_1424, B_1422)) | ~m1_subset_1(E_1425, A_1423) | ~m1_subset_1(D_1424, k1_zfmisc_1(k2_zfmisc_1(C_1421, A_1423))) | v1_xboole_0(C_1421) | v1_xboole_0(B_1422) | v1_xboole_0(A_1423))), inference(resolution, [status(thm)], [c_8810, c_24])).
% 10.73/4.35  tff(c_14077, plain, (![D_206, E_1425]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', D_206, E_1425, '#skF_9', '#skF_6'))=E_1425 | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(E_1425, k9_relat_1('#skF_9', D_206)) | ~m1_subset_1(E_1425, '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7'))) | v1_xboole_0('#skF_6') | v1_xboole_0(D_206) | v1_xboole_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_213, c_14057])).
% 10.73/4.35  tff(c_14094, plain, (![D_206, E_1425]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', D_206, E_1425, '#skF_9', '#skF_6'))=E_1425 | ~r2_hidden(E_1425, k9_relat_1('#skF_9', D_206)) | ~m1_subset_1(E_1425, '#skF_7') | v1_xboole_0('#skF_6') | v1_xboole_0(D_206) | v1_xboole_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_92, c_58, c_14077])).
% 10.73/4.35  tff(c_14099, plain, (![D_1426, E_1427]: (k1_funct_1('#skF_9', '#skF_5'('#skF_7', D_1426, E_1427, '#skF_9', '#skF_6'))=E_1427 | ~r2_hidden(E_1427, k9_relat_1('#skF_9', D_1426)) | ~m1_subset_1(E_1427, '#skF_7') | v1_xboole_0(D_1426))), inference(negUnitSimplification, [status(thm)], [c_98, c_7859, c_14094])).
% 10.73/4.35  tff(c_14172, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'))='#skF_10' | ~m1_subset_1('#skF_10', '#skF_7') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_215, c_14099])).
% 10.73/4.35  tff(c_14238, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_7', '#skF_8', '#skF_10', '#skF_9', '#skF_6'))='#skF_10' | v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_357, c_14172])).
% 10.73/4.35  tff(c_14240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_9230, c_14238])).
% 10.73/4.35  tff(c_14241, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_97])).
% 10.73/4.35  tff(c_14332, plain, (![A_1459, B_1460, C_1461, D_1462]: (k7_relset_1(A_1459, B_1460, C_1461, D_1462)=k9_relat_1(C_1461, D_1462) | ~m1_subset_1(C_1461, k1_zfmisc_1(k2_zfmisc_1(A_1459, B_1460))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.73/4.35  tff(c_14335, plain, (![D_1462]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_1462)=k9_relat_1('#skF_9', D_1462))), inference(resolution, [status(thm)], [c_54, c_14332])).
% 10.73/4.35  tff(c_14337, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_14335, c_52])).
% 10.73/4.35  tff(c_14462, plain, (![A_1482, B_1483, C_1484]: (r2_hidden(k4_tarski('#skF_2'(A_1482, B_1483, C_1484), A_1482), C_1484) | ~r2_hidden(A_1482, k9_relat_1(C_1484, B_1483)) | ~v1_relat_1(C_1484))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.73/4.35  tff(c_14505, plain, (![C_1485, A_1486, B_1487]: (~v1_xboole_0(C_1485) | ~r2_hidden(A_1486, k9_relat_1(C_1485, B_1487)) | ~v1_relat_1(C_1485))), inference(resolution, [status(thm)], [c_14462, c_2])).
% 10.73/4.35  tff(c_14512, plain, (~v1_xboole_0('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_14337, c_14505])).
% 10.73/4.35  tff(c_14529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_14241, c_14512])).
% 10.73/4.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.73/4.35  
% 10.73/4.35  Inference rules
% 10.73/4.35  ----------------------
% 10.73/4.35  #Ref     : 0
% 10.73/4.35  #Sup     : 3092
% 10.73/4.35  #Fact    : 0
% 10.73/4.35  #Define  : 0
% 10.73/4.35  #Split   : 40
% 10.73/4.35  #Chain   : 0
% 10.73/4.35  #Close   : 0
% 10.73/4.35  
% 10.73/4.35  Ordering : KBO
% 10.73/4.35  
% 10.73/4.35  Simplification rules
% 10.73/4.35  ----------------------
% 10.73/4.35  #Subsume      : 891
% 10.73/4.35  #Demod        : 846
% 10.73/4.35  #Tautology    : 139
% 10.73/4.35  #SimpNegUnit  : 236
% 10.73/4.35  #BackRed      : 6
% 10.73/4.35  
% 10.73/4.35  #Partial instantiations: 0
% 10.73/4.35  #Strategies tried      : 1
% 10.73/4.35  
% 10.73/4.35  Timing (in seconds)
% 10.73/4.35  ----------------------
% 10.73/4.35  Preprocessing        : 0.35
% 10.73/4.35  Parsing              : 0.18
% 10.73/4.35  CNF conversion       : 0.03
% 10.73/4.35  Main loop            : 3.18
% 10.73/4.35  Inferencing          : 0.83
% 10.73/4.35  Reduction            : 0.70
% 10.73/4.35  Demodulation         : 0.48
% 10.73/4.35  BG Simplification    : 0.09
% 10.73/4.35  Subsumption          : 1.36
% 10.73/4.35  Abstraction          : 0.13
% 10.73/4.35  MUC search           : 0.00
% 10.73/4.35  Cooper               : 0.00
% 10.73/4.36  Total                : 3.58
% 10.73/4.36  Index Insertion      : 0.00
% 10.73/4.36  Index Deletion       : 0.00
% 10.73/4.36  Index Matching       : 0.00
% 10.73/4.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
