%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:37 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 278 expanded)
%              Number of leaves         :   30 ( 106 expanded)
%              Depth                    :    9
%              Number of atoms          :  224 ( 832 expanded)
%              Number of equality atoms :   16 (  33 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_49,plain,(
    ! [C_115,A_116,B_117] :
      ( v1_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_53,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_49])).

tff(c_673,plain,(
    ! [A_273,B_274,C_275,D_276] :
      ( k8_relset_1(A_273,B_274,C_275,D_276) = k10_relat_1(C_275,D_276)
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_273,B_274))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_680,plain,(
    ! [D_276] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_276) = k10_relat_1('#skF_5',D_276) ),
    inference(resolution,[status(thm)],[c_26,c_673])).

tff(c_491,plain,(
    ! [A_224,B_225,C_226,D_227] :
      ( k8_relset_1(A_224,B_225,C_226,D_227) = k10_relat_1(C_226,D_227)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_498,plain,(
    ! [D_227] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_227) = k10_relat_1('#skF_5',D_227) ),
    inference(resolution,[status(thm)],[c_26,c_491])).

tff(c_341,plain,(
    ! [A_185,B_186,C_187,D_188] :
      ( k8_relset_1(A_185,B_186,C_187,D_188) = k10_relat_1(C_187,D_188)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_348,plain,(
    ! [D_188] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_188) = k10_relat_1('#skF_5',D_188) ),
    inference(resolution,[status(thm)],[c_26,c_341])).

tff(c_48,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | m1_subset_1('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_60,plain,(
    m1_subset_1('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_40,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | r2_hidden('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_59,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_44,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_63,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_121,plain,(
    ! [A_138,B_139,C_140,D_141] :
      ( k8_relset_1(A_138,B_139,C_140,D_141) = k10_relat_1(C_140,D_141)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_128,plain,(
    ! [D_141] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_141) = k10_relat_1('#skF_5',D_141) ),
    inference(resolution,[status(thm)],[c_26,c_121])).

tff(c_34,plain,(
    ! [F_114] :
      ( ~ r2_hidden(F_114,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_114),'#skF_5')
      | ~ m1_subset_1(F_114,'#skF_4')
      | ~ r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_196,plain,(
    ! [F_114] :
      ( ~ r2_hidden(F_114,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_114),'#skF_5')
      | ~ m1_subset_1(F_114,'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_34])).

tff(c_197,plain,(
    ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_12,plain,(
    ! [B_11,C_12,A_10] :
      ( r2_hidden(B_11,k2_relat_1(C_12))
      | ~ r2_hidden(k4_tarski(A_10,B_11),C_12)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_66,plain,
    ( r2_hidden('#skF_7',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_63,c_12])).

tff(c_72,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_66])).

tff(c_216,plain,(
    ! [A_164,C_165,B_166,D_167] :
      ( r2_hidden(A_164,k10_relat_1(C_165,B_166))
      | ~ r2_hidden(D_167,B_166)
      | ~ r2_hidden(k4_tarski(A_164,D_167),C_165)
      | ~ r2_hidden(D_167,k2_relat_1(C_165))
      | ~ v1_relat_1(C_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_238,plain,(
    ! [A_168,C_169] :
      ( r2_hidden(A_168,k10_relat_1(C_169,'#skF_3'))
      | ~ r2_hidden(k4_tarski(A_168,'#skF_7'),C_169)
      | ~ r2_hidden('#skF_7',k2_relat_1(C_169))
      | ~ v1_relat_1(C_169) ) ),
    inference(resolution,[status(thm)],[c_59,c_216])).

tff(c_241,plain,
    ( r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ r2_hidden('#skF_7',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_63,c_238])).

tff(c_244,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_72,c_241])).

tff(c_246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_244])).

tff(c_284,plain,(
    ! [F_174] :
      ( ~ r2_hidden(F_174,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_174),'#skF_5')
      | ~ m1_subset_1(F_174,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_291,plain,
    ( ~ r2_hidden('#skF_7','#skF_3')
    | ~ m1_subset_1('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_63,c_284])).

tff(c_298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_59,c_291])).

tff(c_299,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_349,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_299])).

tff(c_361,plain,(
    ! [A_191,B_192,C_193] :
      ( r2_hidden('#skF_1'(A_191,B_192,C_193),k2_relat_1(C_193))
      | ~ r2_hidden(A_191,k10_relat_1(C_193,B_192))
      | ~ v1_relat_1(C_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_302,plain,(
    ! [A_175,B_176,C_177] :
      ( k2_relset_1(A_175,B_176,C_177) = k2_relat_1(C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_306,plain,(
    k2_relset_1('#skF_2','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_302])).

tff(c_311,plain,(
    ! [A_178,B_179,C_180] :
      ( m1_subset_1(k2_relset_1(A_178,B_179,C_180),k1_zfmisc_1(B_179))
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_324,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_311])).

tff(c_329,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_324])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_332,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_4')
      | ~ r2_hidden(A_1,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_329,c_2])).

tff(c_365,plain,(
    ! [A_191,B_192] :
      ( m1_subset_1('#skF_1'(A_191,B_192,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_191,k10_relat_1('#skF_5',B_192))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_361,c_332])).

tff(c_369,plain,(
    ! [A_194,B_195] :
      ( m1_subset_1('#skF_1'(A_194,B_195,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_194,k10_relat_1('#skF_5',B_195)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_365])).

tff(c_377,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_349,c_369])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] :
      ( r2_hidden('#skF_1'(A_4,B_5,C_6),B_5)
      | ~ r2_hidden(A_4,k10_relat_1(C_6,B_5))
      | ~ v1_relat_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_379,plain,(
    ! [A_196,B_197,C_198] :
      ( r2_hidden(k4_tarski(A_196,'#skF_1'(A_196,B_197,C_198)),C_198)
      | ~ r2_hidden(A_196,k10_relat_1(C_198,B_197))
      | ~ v1_relat_1(C_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_300,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,(
    ! [F_114] :
      ( ~ r2_hidden(F_114,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_114),'#skF_5')
      | ~ m1_subset_1(F_114,'#skF_4')
      | r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_359,plain,(
    ! [F_114] :
      ( ~ r2_hidden(F_114,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_114),'#skF_5')
      | ~ m1_subset_1(F_114,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_42])).

tff(c_387,plain,(
    ! [B_197] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_197,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_197,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_197))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_379,c_359])).

tff(c_437,plain,(
    ! [B_206] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_206,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_206,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_206)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_387])).

tff(c_441,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_437])).

tff(c_445,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_349,c_377,c_441])).

tff(c_446,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_499,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_446])).

tff(c_510,plain,(
    ! [A_229,B_230,C_231] :
      ( r2_hidden('#skF_1'(A_229,B_230,C_231),k2_relat_1(C_231))
      | ~ r2_hidden(A_229,k10_relat_1(C_231,B_230))
      | ~ v1_relat_1(C_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_451,plain,(
    ! [A_213,B_214,C_215] :
      ( k2_relset_1(A_213,B_214,C_215) = k2_relat_1(C_215)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_455,plain,(
    k2_relset_1('#skF_2','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_451])).

tff(c_461,plain,(
    ! [A_219,B_220,C_221] :
      ( m1_subset_1(k2_relset_1(A_219,B_220,C_221),k1_zfmisc_1(B_220))
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_474,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_461])).

tff(c_479,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_474])).

tff(c_484,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_4')
      | ~ r2_hidden(A_1,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_479,c_2])).

tff(c_514,plain,(
    ! [A_229,B_230] :
      ( m1_subset_1('#skF_1'(A_229,B_230,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_229,k10_relat_1('#skF_5',B_230))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_510,c_484])).

tff(c_518,plain,(
    ! [A_232,B_233] :
      ( m1_subset_1('#skF_1'(A_232,B_233,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_232,k10_relat_1('#skF_5',B_233)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_514])).

tff(c_526,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_499,c_518])).

tff(c_528,plain,(
    ! [A_234,B_235,C_236] :
      ( r2_hidden(k4_tarski(A_234,'#skF_1'(A_234,B_235,C_236)),C_236)
      | ~ r2_hidden(A_234,k10_relat_1(C_236,B_235))
      | ~ v1_relat_1(C_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_447,plain,(
    ~ m1_subset_1('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [F_114] :
      ( ~ r2_hidden(F_114,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_114),'#skF_5')
      | ~ m1_subset_1(F_114,'#skF_4')
      | m1_subset_1('#skF_7','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_480,plain,(
    ! [F_114] :
      ( ~ r2_hidden(F_114,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_114),'#skF_5')
      | ~ m1_subset_1(F_114,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_447,c_46])).

tff(c_540,plain,(
    ! [B_235] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_235,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_235,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_235))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_528,c_480])).

tff(c_603,plain,(
    ! [B_250] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_250,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_250,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_250)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_540])).

tff(c_607,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_603])).

tff(c_611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_499,c_526,c_607])).

tff(c_612,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_681,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_612])).

tff(c_658,plain,(
    ! [A_268,B_269,C_270] :
      ( r2_hidden('#skF_1'(A_268,B_269,C_270),k2_relat_1(C_270))
      | ~ r2_hidden(A_268,k10_relat_1(C_270,B_269))
      | ~ v1_relat_1(C_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_618,plain,(
    ! [A_257,B_258,C_259] :
      ( k2_relset_1(A_257,B_258,C_259) = k2_relat_1(C_259)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_622,plain,(
    k2_relset_1('#skF_2','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_618])).

tff(c_627,plain,(
    ! [A_260,B_261,C_262] :
      ( m1_subset_1(k2_relset_1(A_260,B_261,C_262),k1_zfmisc_1(B_261))
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_640,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_627])).

tff(c_645,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_640])).

tff(c_648,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_4')
      | ~ r2_hidden(A_1,k2_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_645,c_2])).

tff(c_662,plain,(
    ! [A_268,B_269] :
      ( m1_subset_1('#skF_1'(A_268,B_269,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_268,k10_relat_1('#skF_5',B_269))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_658,c_648])).

tff(c_665,plain,(
    ! [A_268,B_269] :
      ( m1_subset_1('#skF_1'(A_268,B_269,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_268,k10_relat_1('#skF_5',B_269)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_662])).

tff(c_694,plain,(
    m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_681,c_665])).

tff(c_695,plain,(
    ! [A_278,B_279,C_280] :
      ( r2_hidden(k4_tarski(A_278,'#skF_1'(A_278,B_279,C_280)),C_280)
      | ~ r2_hidden(A_278,k10_relat_1(C_280,B_279))
      | ~ v1_relat_1(C_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_613,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,(
    ! [F_114] :
      ( ~ r2_hidden(F_114,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_114),'#skF_5')
      | ~ m1_subset_1(F_114,'#skF_4')
      | r2_hidden('#skF_7','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_649,plain,(
    ! [F_114] :
      ( ~ r2_hidden(F_114,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_114),'#skF_5')
      | ~ m1_subset_1(F_114,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_613,c_38])).

tff(c_707,plain,(
    ! [B_279] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_279,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_279,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_279))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_695,c_649])).

tff(c_770,plain,(
    ! [B_294] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_294,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_294,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_294)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_707])).

tff(c_774,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_770])).

tff(c_778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_681,c_694,c_774])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.42  
% 2.83/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.43  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.83/1.43  
% 2.83/1.43  %Foreground sorts:
% 2.83/1.43  
% 2.83/1.43  
% 2.83/1.43  %Background operators:
% 2.83/1.43  
% 2.83/1.43  
% 2.83/1.43  %Foreground operators:
% 2.83/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.83/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.83/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.83/1.43  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.83/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.83/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.83/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.83/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.83/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.43  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.83/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.83/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.83/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.83/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.43  
% 2.83/1.45  tff(f_93, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_relset_1)).
% 2.83/1.45  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.83/1.45  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.83/1.45  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 2.83/1.45  tff(f_42, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.83/1.45  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.83/1.45  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.83/1.45  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.83/1.45  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.83/1.45  tff(c_49, plain, (![C_115, A_116, B_117]: (v1_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.83/1.45  tff(c_53, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_49])).
% 2.83/1.45  tff(c_673, plain, (![A_273, B_274, C_275, D_276]: (k8_relset_1(A_273, B_274, C_275, D_276)=k10_relat_1(C_275, D_276) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(A_273, B_274))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.83/1.45  tff(c_680, plain, (![D_276]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_276)=k10_relat_1('#skF_5', D_276))), inference(resolution, [status(thm)], [c_26, c_673])).
% 2.83/1.45  tff(c_491, plain, (![A_224, B_225, C_226, D_227]: (k8_relset_1(A_224, B_225, C_226, D_227)=k10_relat_1(C_226, D_227) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.83/1.45  tff(c_498, plain, (![D_227]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_227)=k10_relat_1('#skF_5', D_227))), inference(resolution, [status(thm)], [c_26, c_491])).
% 2.83/1.45  tff(c_341, plain, (![A_185, B_186, C_187, D_188]: (k8_relset_1(A_185, B_186, C_187, D_188)=k10_relat_1(C_187, D_188) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.83/1.45  tff(c_348, plain, (![D_188]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_188)=k10_relat_1('#skF_5', D_188))), inference(resolution, [status(thm)], [c_26, c_341])).
% 2.83/1.45  tff(c_48, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | m1_subset_1('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.83/1.45  tff(c_60, plain, (m1_subset_1('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_48])).
% 2.83/1.45  tff(c_40, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | r2_hidden('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.83/1.45  tff(c_59, plain, (r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 2.83/1.45  tff(c_44, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.83/1.45  tff(c_63, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(splitLeft, [status(thm)], [c_44])).
% 2.83/1.45  tff(c_121, plain, (![A_138, B_139, C_140, D_141]: (k8_relset_1(A_138, B_139, C_140, D_141)=k10_relat_1(C_140, D_141) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.83/1.45  tff(c_128, plain, (![D_141]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_141)=k10_relat_1('#skF_5', D_141))), inference(resolution, [status(thm)], [c_26, c_121])).
% 2.83/1.45  tff(c_34, plain, (![F_114]: (~r2_hidden(F_114, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_114), '#skF_5') | ~m1_subset_1(F_114, '#skF_4') | ~r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.83/1.45  tff(c_196, plain, (![F_114]: (~r2_hidden(F_114, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_114), '#skF_5') | ~m1_subset_1(F_114, '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_34])).
% 2.83/1.45  tff(c_197, plain, (~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_196])).
% 2.83/1.45  tff(c_12, plain, (![B_11, C_12, A_10]: (r2_hidden(B_11, k2_relat_1(C_12)) | ~r2_hidden(k4_tarski(A_10, B_11), C_12) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.83/1.45  tff(c_66, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_63, c_12])).
% 2.83/1.45  tff(c_72, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_66])).
% 2.83/1.45  tff(c_216, plain, (![A_164, C_165, B_166, D_167]: (r2_hidden(A_164, k10_relat_1(C_165, B_166)) | ~r2_hidden(D_167, B_166) | ~r2_hidden(k4_tarski(A_164, D_167), C_165) | ~r2_hidden(D_167, k2_relat_1(C_165)) | ~v1_relat_1(C_165))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.83/1.45  tff(c_238, plain, (![A_168, C_169]: (r2_hidden(A_168, k10_relat_1(C_169, '#skF_3')) | ~r2_hidden(k4_tarski(A_168, '#skF_7'), C_169) | ~r2_hidden('#skF_7', k2_relat_1(C_169)) | ~v1_relat_1(C_169))), inference(resolution, [status(thm)], [c_59, c_216])).
% 2.83/1.45  tff(c_241, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~r2_hidden('#skF_7', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_63, c_238])).
% 2.83/1.45  tff(c_244, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_72, c_241])).
% 2.83/1.45  tff(c_246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197, c_244])).
% 2.83/1.45  tff(c_284, plain, (![F_174]: (~r2_hidden(F_174, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_174), '#skF_5') | ~m1_subset_1(F_174, '#skF_4'))), inference(splitRight, [status(thm)], [c_196])).
% 2.83/1.45  tff(c_291, plain, (~r2_hidden('#skF_7', '#skF_3') | ~m1_subset_1('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_63, c_284])).
% 2.83/1.45  tff(c_298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_59, c_291])).
% 2.83/1.45  tff(c_299, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_44])).
% 2.83/1.45  tff(c_349, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_348, c_299])).
% 2.83/1.45  tff(c_361, plain, (![A_191, B_192, C_193]: (r2_hidden('#skF_1'(A_191, B_192, C_193), k2_relat_1(C_193)) | ~r2_hidden(A_191, k10_relat_1(C_193, B_192)) | ~v1_relat_1(C_193))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.83/1.45  tff(c_302, plain, (![A_175, B_176, C_177]: (k2_relset_1(A_175, B_176, C_177)=k2_relat_1(C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.83/1.45  tff(c_306, plain, (k2_relset_1('#skF_2', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_302])).
% 2.83/1.45  tff(c_311, plain, (![A_178, B_179, C_180]: (m1_subset_1(k2_relset_1(A_178, B_179, C_180), k1_zfmisc_1(B_179)) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.83/1.45  tff(c_324, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_306, c_311])).
% 2.83/1.45  tff(c_329, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_324])).
% 2.83/1.45  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.83/1.45  tff(c_332, plain, (![A_1]: (m1_subset_1(A_1, '#skF_4') | ~r2_hidden(A_1, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_329, c_2])).
% 2.83/1.45  tff(c_365, plain, (![A_191, B_192]: (m1_subset_1('#skF_1'(A_191, B_192, '#skF_5'), '#skF_4') | ~r2_hidden(A_191, k10_relat_1('#skF_5', B_192)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_361, c_332])).
% 2.83/1.45  tff(c_369, plain, (![A_194, B_195]: (m1_subset_1('#skF_1'(A_194, B_195, '#skF_5'), '#skF_4') | ~r2_hidden(A_194, k10_relat_1('#skF_5', B_195)))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_365])).
% 2.83/1.45  tff(c_377, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_349, c_369])).
% 2.83/1.45  tff(c_6, plain, (![A_4, B_5, C_6]: (r2_hidden('#skF_1'(A_4, B_5, C_6), B_5) | ~r2_hidden(A_4, k10_relat_1(C_6, B_5)) | ~v1_relat_1(C_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.83/1.45  tff(c_379, plain, (![A_196, B_197, C_198]: (r2_hidden(k4_tarski(A_196, '#skF_1'(A_196, B_197, C_198)), C_198) | ~r2_hidden(A_196, k10_relat_1(C_198, B_197)) | ~v1_relat_1(C_198))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.83/1.45  tff(c_300, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_44])).
% 2.83/1.45  tff(c_42, plain, (![F_114]: (~r2_hidden(F_114, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_114), '#skF_5') | ~m1_subset_1(F_114, '#skF_4') | r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.83/1.45  tff(c_359, plain, (![F_114]: (~r2_hidden(F_114, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_114), '#skF_5') | ~m1_subset_1(F_114, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_300, c_42])).
% 2.83/1.45  tff(c_387, plain, (![B_197]: (~r2_hidden('#skF_1'('#skF_6', B_197, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_197, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_197)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_379, c_359])).
% 2.83/1.45  tff(c_437, plain, (![B_206]: (~r2_hidden('#skF_1'('#skF_6', B_206, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_206, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_206)))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_387])).
% 2.83/1.45  tff(c_441, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6, c_437])).
% 2.83/1.45  tff(c_445, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_349, c_377, c_441])).
% 2.83/1.45  tff(c_446, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_48])).
% 2.83/1.45  tff(c_499, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_498, c_446])).
% 2.83/1.45  tff(c_510, plain, (![A_229, B_230, C_231]: (r2_hidden('#skF_1'(A_229, B_230, C_231), k2_relat_1(C_231)) | ~r2_hidden(A_229, k10_relat_1(C_231, B_230)) | ~v1_relat_1(C_231))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.83/1.45  tff(c_451, plain, (![A_213, B_214, C_215]: (k2_relset_1(A_213, B_214, C_215)=k2_relat_1(C_215) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.83/1.45  tff(c_455, plain, (k2_relset_1('#skF_2', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_451])).
% 2.83/1.45  tff(c_461, plain, (![A_219, B_220, C_221]: (m1_subset_1(k2_relset_1(A_219, B_220, C_221), k1_zfmisc_1(B_220)) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.83/1.45  tff(c_474, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_455, c_461])).
% 2.83/1.45  tff(c_479, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_474])).
% 2.83/1.45  tff(c_484, plain, (![A_1]: (m1_subset_1(A_1, '#skF_4') | ~r2_hidden(A_1, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_479, c_2])).
% 2.83/1.45  tff(c_514, plain, (![A_229, B_230]: (m1_subset_1('#skF_1'(A_229, B_230, '#skF_5'), '#skF_4') | ~r2_hidden(A_229, k10_relat_1('#skF_5', B_230)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_510, c_484])).
% 2.83/1.45  tff(c_518, plain, (![A_232, B_233]: (m1_subset_1('#skF_1'(A_232, B_233, '#skF_5'), '#skF_4') | ~r2_hidden(A_232, k10_relat_1('#skF_5', B_233)))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_514])).
% 2.83/1.45  tff(c_526, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_499, c_518])).
% 2.83/1.45  tff(c_528, plain, (![A_234, B_235, C_236]: (r2_hidden(k4_tarski(A_234, '#skF_1'(A_234, B_235, C_236)), C_236) | ~r2_hidden(A_234, k10_relat_1(C_236, B_235)) | ~v1_relat_1(C_236))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.83/1.45  tff(c_447, plain, (~m1_subset_1('#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 2.83/1.45  tff(c_46, plain, (![F_114]: (~r2_hidden(F_114, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_114), '#skF_5') | ~m1_subset_1(F_114, '#skF_4') | m1_subset_1('#skF_7', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.83/1.45  tff(c_480, plain, (![F_114]: (~r2_hidden(F_114, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_114), '#skF_5') | ~m1_subset_1(F_114, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_447, c_46])).
% 2.83/1.45  tff(c_540, plain, (![B_235]: (~r2_hidden('#skF_1'('#skF_6', B_235, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_235, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_235)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_528, c_480])).
% 2.83/1.45  tff(c_603, plain, (![B_250]: (~r2_hidden('#skF_1'('#skF_6', B_250, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_250, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_250)))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_540])).
% 2.83/1.45  tff(c_607, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6, c_603])).
% 2.83/1.45  tff(c_611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_499, c_526, c_607])).
% 2.83/1.45  tff(c_612, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_40])).
% 2.83/1.45  tff(c_681, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_680, c_612])).
% 2.83/1.45  tff(c_658, plain, (![A_268, B_269, C_270]: (r2_hidden('#skF_1'(A_268, B_269, C_270), k2_relat_1(C_270)) | ~r2_hidden(A_268, k10_relat_1(C_270, B_269)) | ~v1_relat_1(C_270))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.83/1.45  tff(c_618, plain, (![A_257, B_258, C_259]: (k2_relset_1(A_257, B_258, C_259)=k2_relat_1(C_259) | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.83/1.45  tff(c_622, plain, (k2_relset_1('#skF_2', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_618])).
% 2.83/1.45  tff(c_627, plain, (![A_260, B_261, C_262]: (m1_subset_1(k2_relset_1(A_260, B_261, C_262), k1_zfmisc_1(B_261)) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.83/1.45  tff(c_640, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_622, c_627])).
% 2.83/1.45  tff(c_645, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_640])).
% 2.83/1.45  tff(c_648, plain, (![A_1]: (m1_subset_1(A_1, '#skF_4') | ~r2_hidden(A_1, k2_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_645, c_2])).
% 2.83/1.45  tff(c_662, plain, (![A_268, B_269]: (m1_subset_1('#skF_1'(A_268, B_269, '#skF_5'), '#skF_4') | ~r2_hidden(A_268, k10_relat_1('#skF_5', B_269)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_658, c_648])).
% 2.83/1.45  tff(c_665, plain, (![A_268, B_269]: (m1_subset_1('#skF_1'(A_268, B_269, '#skF_5'), '#skF_4') | ~r2_hidden(A_268, k10_relat_1('#skF_5', B_269)))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_662])).
% 2.83/1.45  tff(c_694, plain, (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_681, c_665])).
% 2.83/1.45  tff(c_695, plain, (![A_278, B_279, C_280]: (r2_hidden(k4_tarski(A_278, '#skF_1'(A_278, B_279, C_280)), C_280) | ~r2_hidden(A_278, k10_relat_1(C_280, B_279)) | ~v1_relat_1(C_280))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.83/1.45  tff(c_613, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 2.83/1.45  tff(c_38, plain, (![F_114]: (~r2_hidden(F_114, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_114), '#skF_5') | ~m1_subset_1(F_114, '#skF_4') | r2_hidden('#skF_7', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.83/1.45  tff(c_649, plain, (![F_114]: (~r2_hidden(F_114, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_114), '#skF_5') | ~m1_subset_1(F_114, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_613, c_38])).
% 2.83/1.45  tff(c_707, plain, (![B_279]: (~r2_hidden('#skF_1'('#skF_6', B_279, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_279, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_279)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_695, c_649])).
% 2.83/1.45  tff(c_770, plain, (![B_294]: (~r2_hidden('#skF_1'('#skF_6', B_294, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_294, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_294)))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_707])).
% 2.83/1.45  tff(c_774, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6, c_770])).
% 2.83/1.45  tff(c_778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_681, c_694, c_774])).
% 2.83/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.45  
% 2.83/1.45  Inference rules
% 2.83/1.45  ----------------------
% 2.83/1.45  #Ref     : 0
% 2.83/1.45  #Sup     : 142
% 2.83/1.45  #Fact    : 0
% 2.83/1.45  #Define  : 0
% 2.83/1.45  #Split   : 6
% 2.83/1.45  #Chain   : 0
% 2.83/1.45  #Close   : 0
% 2.83/1.45  
% 2.83/1.45  Ordering : KBO
% 2.83/1.45  
% 2.83/1.45  Simplification rules
% 2.83/1.45  ----------------------
% 2.83/1.45  #Subsume      : 15
% 2.83/1.45  #Demod        : 56
% 2.83/1.45  #Tautology    : 26
% 2.83/1.45  #SimpNegUnit  : 4
% 2.83/1.45  #BackRed      : 3
% 2.83/1.45  
% 2.83/1.45  #Partial instantiations: 0
% 2.83/1.45  #Strategies tried      : 1
% 2.83/1.45  
% 2.83/1.45  Timing (in seconds)
% 2.83/1.45  ----------------------
% 2.83/1.45  Preprocessing        : 0.32
% 2.83/1.45  Parsing              : 0.17
% 2.83/1.45  CNF conversion       : 0.03
% 2.83/1.45  Main loop            : 0.36
% 2.83/1.45  Inferencing          : 0.15
% 2.83/1.45  Reduction            : 0.10
% 2.83/1.45  Demodulation         : 0.07
% 2.83/1.45  BG Simplification    : 0.02
% 2.83/1.45  Subsumption          : 0.06
% 2.83/1.45  Abstraction          : 0.02
% 2.83/1.45  MUC search           : 0.00
% 2.83/1.45  Cooper               : 0.00
% 2.83/1.45  Total                : 0.72
% 2.83/1.45  Index Insertion      : 0.00
% 2.83/1.45  Index Deletion       : 0.00
% 2.83/1.45  Index Matching       : 0.00
% 2.83/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
