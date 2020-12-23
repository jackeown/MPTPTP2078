%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:32 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 258 expanded)
%              Number of leaves         :   33 ( 102 expanded)
%              Depth                    :    9
%              Number of atoms          :  210 ( 754 expanded)
%              Number of equality atoms :   17 (  31 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_98,negated_conjecture,(
    ~ ! [A] :
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_44,axiom,(
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

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_40,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_63,plain,(
    ! [C_154,A_155,B_156] :
      ( v1_relat_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_67,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_40,c_63])).

tff(c_722,plain,(
    ! [A_325,B_326,C_327,D_328] :
      ( k7_relset_1(A_325,B_326,C_327,D_328) = k9_relat_1(C_327,D_328)
      | ~ m1_subset_1(C_327,k1_zfmisc_1(k2_zfmisc_1(A_325,B_326))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_729,plain,(
    ! [D_328] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_328) = k9_relat_1('#skF_9',D_328) ),
    inference(resolution,[status(thm)],[c_40,c_722])).

tff(c_506,plain,(
    ! [A_268,B_269,C_270,D_271] :
      ( k7_relset_1(A_268,B_269,C_270,D_271) = k9_relat_1(C_270,D_271)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_268,B_269))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_513,plain,(
    ! [D_271] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_271) = k9_relat_1('#skF_9',D_271) ),
    inference(resolution,[status(thm)],[c_40,c_506])).

tff(c_322,plain,(
    ! [A_222,B_223,C_224,D_225] :
      ( k7_relset_1(A_222,B_223,C_224,D_225) = k9_relat_1(C_224,D_225)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_329,plain,(
    ! [D_225] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_225) = k9_relat_1('#skF_9',D_225) ),
    inference(resolution,[status(thm)],[c_40,c_322])).

tff(c_62,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_69,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_54,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_68,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_58,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_75,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_158,plain,(
    ! [D_184,A_185,B_186,E_187] :
      ( r2_hidden(D_184,k9_relat_1(A_185,B_186))
      | ~ r2_hidden(E_187,B_186)
      | ~ r2_hidden(k4_tarski(E_187,D_184),A_185)
      | ~ v1_relat_1(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_175,plain,(
    ! [D_188,A_189] :
      ( r2_hidden(D_188,k9_relat_1(A_189,'#skF_7'))
      | ~ r2_hidden(k4_tarski('#skF_11',D_188),A_189)
      | ~ v1_relat_1(A_189) ) ),
    inference(resolution,[status(thm)],[c_68,c_158])).

tff(c_178,plain,
    ( r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_75,c_175])).

tff(c_181,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_178])).

tff(c_130,plain,(
    ! [A_176,B_177,C_178,D_179] :
      ( k7_relset_1(A_176,B_177,C_178,D_179) = k9_relat_1(C_178,D_179)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_137,plain,(
    ! [D_179] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_179) = k9_relat_1('#skF_9',D_179) ),
    inference(resolution,[status(thm)],[c_40,c_130])).

tff(c_48,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_153,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8')
      | ~ r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_251,plain,(
    ! [F_206] :
      ( ~ r2_hidden(F_206,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_206,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_206,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_137,c_48])).

tff(c_258,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_75,c_251])).

tff(c_265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_68,c_258])).

tff(c_266,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_330,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_266])).

tff(c_306,plain,(
    ! [A_217,B_218,C_219] :
      ( r2_hidden('#skF_5'(A_217,B_218,C_219),k1_relat_1(C_219))
      | ~ r2_hidden(A_217,k9_relat_1(C_219,B_218))
      | ~ v1_relat_1(C_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_268,plain,(
    ! [A_207,B_208,C_209] :
      ( k1_relset_1(A_207,B_208,C_209) = k1_relat_1(C_209)
      | ~ m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_272,plain,(
    k1_relset_1('#skF_8','#skF_6','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_40,c_268])).

tff(c_277,plain,(
    ! [A_210,B_211,C_212] :
      ( m1_subset_1(k1_relset_1(A_210,B_211,C_212),k1_zfmisc_1(A_210))
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_290,plain,
    ( m1_subset_1(k1_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_277])).

tff(c_295,plain,(
    m1_subset_1(k1_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_290])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_299,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_8')
      | ~ r2_hidden(A_1,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_295,c_2])).

tff(c_310,plain,(
    ! [A_217,B_218] :
      ( m1_subset_1('#skF_5'(A_217,B_218,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_217,k9_relat_1('#skF_9',B_218))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_306,c_299])).

tff(c_313,plain,(
    ! [A_217,B_218] :
      ( m1_subset_1('#skF_5'(A_217,B_218,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_217,k9_relat_1('#skF_9',B_218)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_310])).

tff(c_343,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_330,c_313])).

tff(c_24,plain,(
    ! [A_46,B_47,C_48] :
      ( r2_hidden('#skF_5'(A_46,B_47,C_48),B_47)
      | ~ r2_hidden(A_46,k9_relat_1(C_48,B_47))
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_377,plain,(
    ! [A_237,B_238,C_239] :
      ( r2_hidden(k4_tarski('#skF_5'(A_237,B_238,C_239),A_237),C_239)
      | ~ r2_hidden(A_237,k9_relat_1(C_239,B_238))
      | ~ v1_relat_1(C_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_267,plain,(
    ~ r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_153,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8')
      | r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_374,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_153,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_267,c_56])).

tff(c_381,plain,(
    ! [B_238] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_238,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_238,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_238))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_377,c_374])).

tff(c_451,plain,(
    ! [B_253] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_253,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_253,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_253)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_381])).

tff(c_455,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_24,c_451])).

tff(c_459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_330,c_343,c_455])).

tff(c_460,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_516,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_460])).

tff(c_526,plain,(
    ! [A_274,B_275,C_276] :
      ( r2_hidden('#skF_5'(A_274,B_275,C_276),k1_relat_1(C_276))
      | ~ r2_hidden(A_274,k9_relat_1(C_276,B_275))
      | ~ v1_relat_1(C_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_468,plain,(
    ! [A_258,B_259,C_260] :
      ( k1_relset_1(A_258,B_259,C_260) = k1_relat_1(C_260)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(k2_zfmisc_1(A_258,B_259))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_472,plain,(
    k1_relset_1('#skF_8','#skF_6','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_40,c_468])).

tff(c_478,plain,(
    ! [A_264,B_265,C_266] :
      ( m1_subset_1(k1_relset_1(A_264,B_265,C_266),k1_zfmisc_1(A_264))
      | ~ m1_subset_1(C_266,k1_zfmisc_1(k2_zfmisc_1(A_264,B_265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_491,plain,
    ( m1_subset_1(k1_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_472,c_478])).

tff(c_496,plain,(
    m1_subset_1(k1_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_491])).

tff(c_499,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_8')
      | ~ r2_hidden(A_1,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_496,c_2])).

tff(c_530,plain,(
    ! [A_274,B_275] :
      ( m1_subset_1('#skF_5'(A_274,B_275,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_274,k9_relat_1('#skF_9',B_275))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_526,c_499])).

tff(c_534,plain,(
    ! [A_277,B_278] :
      ( m1_subset_1('#skF_5'(A_277,B_278,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_277,k9_relat_1('#skF_9',B_278)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_530])).

tff(c_542,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_516,c_534])).

tff(c_545,plain,(
    ! [A_279,B_280,C_281] :
      ( r2_hidden(k4_tarski('#skF_5'(A_279,B_280,C_281),A_279),C_281)
      | ~ r2_hidden(A_279,k9_relat_1(C_281,B_280))
      | ~ v1_relat_1(C_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_461,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_60,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_153,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_514,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_153,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_461,c_60])).

tff(c_553,plain,(
    ! [B_280] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_280,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_280,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_280))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_545,c_514])).

tff(c_650,plain,(
    ! [B_304] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_304,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_304,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_304)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_553])).

tff(c_654,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_24,c_650])).

tff(c_658,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_516,c_542,c_654])).

tff(c_659,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_730,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_729,c_659])).

tff(c_708,plain,(
    ! [A_320,B_321,C_322] :
      ( r2_hidden('#skF_5'(A_320,B_321,C_322),k1_relat_1(C_322))
      | ~ r2_hidden(A_320,k9_relat_1(C_322,B_321))
      | ~ v1_relat_1(C_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_668,plain,(
    ! [A_309,B_310,C_311] :
      ( k1_relset_1(A_309,B_310,C_311) = k1_relat_1(C_311)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_309,B_310))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_672,plain,(
    k1_relset_1('#skF_8','#skF_6','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_40,c_668])).

tff(c_678,plain,(
    ! [A_315,B_316,C_317] :
      ( m1_subset_1(k1_relset_1(A_315,B_316,C_317),k1_zfmisc_1(A_315))
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(A_315,B_316))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_691,plain,
    ( m1_subset_1(k1_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_678])).

tff(c_696,plain,(
    m1_subset_1(k1_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_691])).

tff(c_699,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_8')
      | ~ r2_hidden(A_1,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_696,c_2])).

tff(c_712,plain,(
    ! [A_320,B_321] :
      ( m1_subset_1('#skF_5'(A_320,B_321,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_320,k9_relat_1('#skF_9',B_321))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_708,c_699])).

tff(c_715,plain,(
    ! [A_320,B_321] :
      ( m1_subset_1('#skF_5'(A_320,B_321,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_320,k9_relat_1('#skF_9',B_321)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_712])).

tff(c_761,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_730,c_715])).

tff(c_740,plain,(
    ! [A_330,B_331,C_332] :
      ( r2_hidden(k4_tarski('#skF_5'(A_330,B_331,C_332),A_330),C_332)
      | ~ r2_hidden(A_330,k9_relat_1(C_332,B_331))
      | ~ v1_relat_1(C_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_660,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_153,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_706,plain,(
    ! [F_153] :
      ( ~ r2_hidden(F_153,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_153,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_153,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_660,c_52])).

tff(c_748,plain,(
    ! [B_331] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_331,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_331,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_331))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_740,c_706])).

tff(c_840,plain,(
    ! [B_353] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_353,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_353,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_353)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_748])).

tff(c_844,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_24,c_840])).

tff(c_848,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_730,c_761,c_844])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.56  
% 3.20/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.56  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 3.20/1.56  
% 3.20/1.56  %Foreground sorts:
% 3.20/1.56  
% 3.20/1.56  
% 3.20/1.56  %Background operators:
% 3.20/1.56  
% 3.20/1.56  
% 3.20/1.56  %Foreground operators:
% 3.20/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.20/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.56  tff('#skF_11', type, '#skF_11': $i).
% 3.20/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.20/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.20/1.56  tff('#skF_10', type, '#skF_10': $i).
% 3.20/1.56  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.20/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.20/1.56  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.20/1.56  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.20/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.20/1.56  tff('#skF_9', type, '#skF_9': $i).
% 3.20/1.56  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.20/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.56  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.20/1.56  tff('#skF_8', type, '#skF_8': $i).
% 3.20/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.20/1.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.20/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.20/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.56  
% 3.20/1.58  tff(f_98, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 3.20/1.58  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.20/1.58  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.20/1.58  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 3.20/1.58  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 3.20/1.58  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.20/1.58  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.20/1.58  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.20/1.58  tff(c_40, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.20/1.58  tff(c_63, plain, (![C_154, A_155, B_156]: (v1_relat_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.20/1.58  tff(c_67, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_40, c_63])).
% 3.20/1.58  tff(c_722, plain, (![A_325, B_326, C_327, D_328]: (k7_relset_1(A_325, B_326, C_327, D_328)=k9_relat_1(C_327, D_328) | ~m1_subset_1(C_327, k1_zfmisc_1(k2_zfmisc_1(A_325, B_326))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.20/1.58  tff(c_729, plain, (![D_328]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_328)=k9_relat_1('#skF_9', D_328))), inference(resolution, [status(thm)], [c_40, c_722])).
% 3.20/1.58  tff(c_506, plain, (![A_268, B_269, C_270, D_271]: (k7_relset_1(A_268, B_269, C_270, D_271)=k9_relat_1(C_270, D_271) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_268, B_269))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.20/1.58  tff(c_513, plain, (![D_271]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_271)=k9_relat_1('#skF_9', D_271))), inference(resolution, [status(thm)], [c_40, c_506])).
% 3.20/1.58  tff(c_322, plain, (![A_222, B_223, C_224, D_225]: (k7_relset_1(A_222, B_223, C_224, D_225)=k9_relat_1(C_224, D_225) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.20/1.58  tff(c_329, plain, (![D_225]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_225)=k9_relat_1('#skF_9', D_225))), inference(resolution, [status(thm)], [c_40, c_322])).
% 3.20/1.58  tff(c_62, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.20/1.58  tff(c_69, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_62])).
% 3.20/1.58  tff(c_54, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | r2_hidden('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.20/1.58  tff(c_68, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_54])).
% 3.20/1.58  tff(c_58, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.20/1.58  tff(c_75, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_58])).
% 3.20/1.58  tff(c_158, plain, (![D_184, A_185, B_186, E_187]: (r2_hidden(D_184, k9_relat_1(A_185, B_186)) | ~r2_hidden(E_187, B_186) | ~r2_hidden(k4_tarski(E_187, D_184), A_185) | ~v1_relat_1(A_185))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.20/1.58  tff(c_175, plain, (![D_188, A_189]: (r2_hidden(D_188, k9_relat_1(A_189, '#skF_7')) | ~r2_hidden(k4_tarski('#skF_11', D_188), A_189) | ~v1_relat_1(A_189))), inference(resolution, [status(thm)], [c_68, c_158])).
% 3.20/1.58  tff(c_178, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_75, c_175])).
% 3.20/1.58  tff(c_181, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_178])).
% 3.20/1.58  tff(c_130, plain, (![A_176, B_177, C_178, D_179]: (k7_relset_1(A_176, B_177, C_178, D_179)=k9_relat_1(C_178, D_179) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.20/1.58  tff(c_137, plain, (![D_179]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_179)=k9_relat_1('#skF_9', D_179))), inference(resolution, [status(thm)], [c_40, c_130])).
% 3.20/1.58  tff(c_48, plain, (![F_153]: (~r2_hidden(F_153, '#skF_7') | ~r2_hidden(k4_tarski(F_153, '#skF_10'), '#skF_9') | ~m1_subset_1(F_153, '#skF_8') | ~r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.20/1.58  tff(c_251, plain, (![F_206]: (~r2_hidden(F_206, '#skF_7') | ~r2_hidden(k4_tarski(F_206, '#skF_10'), '#skF_9') | ~m1_subset_1(F_206, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_137, c_48])).
% 3.20/1.58  tff(c_258, plain, (~r2_hidden('#skF_11', '#skF_7') | ~m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_75, c_251])).
% 3.20/1.58  tff(c_265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_68, c_258])).
% 3.20/1.58  tff(c_266, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_58])).
% 3.20/1.58  tff(c_330, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_329, c_266])).
% 3.20/1.58  tff(c_306, plain, (![A_217, B_218, C_219]: (r2_hidden('#skF_5'(A_217, B_218, C_219), k1_relat_1(C_219)) | ~r2_hidden(A_217, k9_relat_1(C_219, B_218)) | ~v1_relat_1(C_219))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.20/1.58  tff(c_268, plain, (![A_207, B_208, C_209]: (k1_relset_1(A_207, B_208, C_209)=k1_relat_1(C_209) | ~m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.20/1.58  tff(c_272, plain, (k1_relset_1('#skF_8', '#skF_6', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_40, c_268])).
% 3.20/1.58  tff(c_277, plain, (![A_210, B_211, C_212]: (m1_subset_1(k1_relset_1(A_210, B_211, C_212), k1_zfmisc_1(A_210)) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.20/1.58  tff(c_290, plain, (m1_subset_1(k1_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_272, c_277])).
% 3.20/1.58  tff(c_295, plain, (m1_subset_1(k1_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_290])).
% 3.20/1.58  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.58  tff(c_299, plain, (![A_1]: (m1_subset_1(A_1, '#skF_8') | ~r2_hidden(A_1, k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_295, c_2])).
% 3.20/1.58  tff(c_310, plain, (![A_217, B_218]: (m1_subset_1('#skF_5'(A_217, B_218, '#skF_9'), '#skF_8') | ~r2_hidden(A_217, k9_relat_1('#skF_9', B_218)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_306, c_299])).
% 3.20/1.58  tff(c_313, plain, (![A_217, B_218]: (m1_subset_1('#skF_5'(A_217, B_218, '#skF_9'), '#skF_8') | ~r2_hidden(A_217, k9_relat_1('#skF_9', B_218)))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_310])).
% 3.20/1.58  tff(c_343, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_330, c_313])).
% 3.20/1.58  tff(c_24, plain, (![A_46, B_47, C_48]: (r2_hidden('#skF_5'(A_46, B_47, C_48), B_47) | ~r2_hidden(A_46, k9_relat_1(C_48, B_47)) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.20/1.58  tff(c_377, plain, (![A_237, B_238, C_239]: (r2_hidden(k4_tarski('#skF_5'(A_237, B_238, C_239), A_237), C_239) | ~r2_hidden(A_237, k9_relat_1(C_239, B_238)) | ~v1_relat_1(C_239))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.20/1.58  tff(c_267, plain, (~r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_58])).
% 3.20/1.59  tff(c_56, plain, (![F_153]: (~r2_hidden(F_153, '#skF_7') | ~r2_hidden(k4_tarski(F_153, '#skF_10'), '#skF_9') | ~m1_subset_1(F_153, '#skF_8') | r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.20/1.59  tff(c_374, plain, (![F_153]: (~r2_hidden(F_153, '#skF_7') | ~r2_hidden(k4_tarski(F_153, '#skF_10'), '#skF_9') | ~m1_subset_1(F_153, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_267, c_56])).
% 3.20/1.59  tff(c_381, plain, (![B_238]: (~r2_hidden('#skF_5'('#skF_10', B_238, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_238, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_238)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_377, c_374])).
% 3.20/1.59  tff(c_451, plain, (![B_253]: (~r2_hidden('#skF_5'('#skF_10', B_253, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_253, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_253)))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_381])).
% 3.20/1.59  tff(c_455, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_24, c_451])).
% 3.20/1.59  tff(c_459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_330, c_343, c_455])).
% 3.20/1.59  tff(c_460, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_62])).
% 3.20/1.59  tff(c_516, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_513, c_460])).
% 3.20/1.59  tff(c_526, plain, (![A_274, B_275, C_276]: (r2_hidden('#skF_5'(A_274, B_275, C_276), k1_relat_1(C_276)) | ~r2_hidden(A_274, k9_relat_1(C_276, B_275)) | ~v1_relat_1(C_276))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.20/1.59  tff(c_468, plain, (![A_258, B_259, C_260]: (k1_relset_1(A_258, B_259, C_260)=k1_relat_1(C_260) | ~m1_subset_1(C_260, k1_zfmisc_1(k2_zfmisc_1(A_258, B_259))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.20/1.59  tff(c_472, plain, (k1_relset_1('#skF_8', '#skF_6', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_40, c_468])).
% 3.20/1.59  tff(c_478, plain, (![A_264, B_265, C_266]: (m1_subset_1(k1_relset_1(A_264, B_265, C_266), k1_zfmisc_1(A_264)) | ~m1_subset_1(C_266, k1_zfmisc_1(k2_zfmisc_1(A_264, B_265))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.20/1.59  tff(c_491, plain, (m1_subset_1(k1_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_472, c_478])).
% 3.20/1.59  tff(c_496, plain, (m1_subset_1(k1_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_491])).
% 3.20/1.59  tff(c_499, plain, (![A_1]: (m1_subset_1(A_1, '#skF_8') | ~r2_hidden(A_1, k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_496, c_2])).
% 3.20/1.59  tff(c_530, plain, (![A_274, B_275]: (m1_subset_1('#skF_5'(A_274, B_275, '#skF_9'), '#skF_8') | ~r2_hidden(A_274, k9_relat_1('#skF_9', B_275)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_526, c_499])).
% 3.20/1.59  tff(c_534, plain, (![A_277, B_278]: (m1_subset_1('#skF_5'(A_277, B_278, '#skF_9'), '#skF_8') | ~r2_hidden(A_277, k9_relat_1('#skF_9', B_278)))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_530])).
% 3.20/1.59  tff(c_542, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_516, c_534])).
% 3.20/1.59  tff(c_545, plain, (![A_279, B_280, C_281]: (r2_hidden(k4_tarski('#skF_5'(A_279, B_280, C_281), A_279), C_281) | ~r2_hidden(A_279, k9_relat_1(C_281, B_280)) | ~v1_relat_1(C_281))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.20/1.59  tff(c_461, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_62])).
% 3.20/1.59  tff(c_60, plain, (![F_153]: (~r2_hidden(F_153, '#skF_7') | ~r2_hidden(k4_tarski(F_153, '#skF_10'), '#skF_9') | ~m1_subset_1(F_153, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.20/1.59  tff(c_514, plain, (![F_153]: (~r2_hidden(F_153, '#skF_7') | ~r2_hidden(k4_tarski(F_153, '#skF_10'), '#skF_9') | ~m1_subset_1(F_153, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_461, c_60])).
% 3.20/1.59  tff(c_553, plain, (![B_280]: (~r2_hidden('#skF_5'('#skF_10', B_280, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_280, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_280)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_545, c_514])).
% 3.20/1.59  tff(c_650, plain, (![B_304]: (~r2_hidden('#skF_5'('#skF_10', B_304, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_304, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_304)))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_553])).
% 3.20/1.59  tff(c_654, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_24, c_650])).
% 3.20/1.59  tff(c_658, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_516, c_542, c_654])).
% 3.20/1.59  tff(c_659, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_54])).
% 3.20/1.59  tff(c_730, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_729, c_659])).
% 3.20/1.59  tff(c_708, plain, (![A_320, B_321, C_322]: (r2_hidden('#skF_5'(A_320, B_321, C_322), k1_relat_1(C_322)) | ~r2_hidden(A_320, k9_relat_1(C_322, B_321)) | ~v1_relat_1(C_322))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.20/1.59  tff(c_668, plain, (![A_309, B_310, C_311]: (k1_relset_1(A_309, B_310, C_311)=k1_relat_1(C_311) | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(A_309, B_310))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.20/1.59  tff(c_672, plain, (k1_relset_1('#skF_8', '#skF_6', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_40, c_668])).
% 3.20/1.59  tff(c_678, plain, (![A_315, B_316, C_317]: (m1_subset_1(k1_relset_1(A_315, B_316, C_317), k1_zfmisc_1(A_315)) | ~m1_subset_1(C_317, k1_zfmisc_1(k2_zfmisc_1(A_315, B_316))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.20/1.59  tff(c_691, plain, (m1_subset_1(k1_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_672, c_678])).
% 3.20/1.59  tff(c_696, plain, (m1_subset_1(k1_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_691])).
% 3.20/1.59  tff(c_699, plain, (![A_1]: (m1_subset_1(A_1, '#skF_8') | ~r2_hidden(A_1, k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_696, c_2])).
% 3.20/1.59  tff(c_712, plain, (![A_320, B_321]: (m1_subset_1('#skF_5'(A_320, B_321, '#skF_9'), '#skF_8') | ~r2_hidden(A_320, k9_relat_1('#skF_9', B_321)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_708, c_699])).
% 3.20/1.59  tff(c_715, plain, (![A_320, B_321]: (m1_subset_1('#skF_5'(A_320, B_321, '#skF_9'), '#skF_8') | ~r2_hidden(A_320, k9_relat_1('#skF_9', B_321)))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_712])).
% 3.20/1.59  tff(c_761, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_730, c_715])).
% 3.20/1.59  tff(c_740, plain, (![A_330, B_331, C_332]: (r2_hidden(k4_tarski('#skF_5'(A_330, B_331, C_332), A_330), C_332) | ~r2_hidden(A_330, k9_relat_1(C_332, B_331)) | ~v1_relat_1(C_332))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.20/1.59  tff(c_660, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_54])).
% 3.20/1.59  tff(c_52, plain, (![F_153]: (~r2_hidden(F_153, '#skF_7') | ~r2_hidden(k4_tarski(F_153, '#skF_10'), '#skF_9') | ~m1_subset_1(F_153, '#skF_8') | r2_hidden('#skF_11', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.20/1.59  tff(c_706, plain, (![F_153]: (~r2_hidden(F_153, '#skF_7') | ~r2_hidden(k4_tarski(F_153, '#skF_10'), '#skF_9') | ~m1_subset_1(F_153, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_660, c_52])).
% 3.20/1.59  tff(c_748, plain, (![B_331]: (~r2_hidden('#skF_5'('#skF_10', B_331, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_331, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_331)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_740, c_706])).
% 3.20/1.59  tff(c_840, plain, (![B_353]: (~r2_hidden('#skF_5'('#skF_10', B_353, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_353, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_353)))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_748])).
% 3.20/1.59  tff(c_844, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_24, c_840])).
% 3.20/1.59  tff(c_848, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_730, c_761, c_844])).
% 3.20/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.59  
% 3.20/1.59  Inference rules
% 3.20/1.59  ----------------------
% 3.20/1.59  #Ref     : 0
% 3.20/1.59  #Sup     : 158
% 3.20/1.59  #Fact    : 0
% 3.20/1.59  #Define  : 0
% 3.20/1.59  #Split   : 3
% 3.20/1.59  #Chain   : 0
% 3.20/1.59  #Close   : 0
% 3.20/1.59  
% 3.20/1.59  Ordering : KBO
% 3.20/1.59  
% 3.20/1.59  Simplification rules
% 3.20/1.59  ----------------------
% 3.20/1.59  #Subsume      : 9
% 3.20/1.59  #Demod        : 46
% 3.20/1.59  #Tautology    : 25
% 3.20/1.59  #SimpNegUnit  : 3
% 3.20/1.59  #BackRed      : 3
% 3.20/1.59  
% 3.20/1.59  #Partial instantiations: 0
% 3.20/1.59  #Strategies tried      : 1
% 3.20/1.59  
% 3.20/1.59  Timing (in seconds)
% 3.20/1.59  ----------------------
% 3.20/1.59  Preprocessing        : 0.40
% 3.20/1.59  Parsing              : 0.16
% 3.20/1.59  CNF conversion       : 0.05
% 3.20/1.59  Main loop            : 0.40
% 3.20/1.59  Inferencing          : 0.15
% 3.20/1.59  Reduction            : 0.11
% 3.20/1.59  Demodulation         : 0.08
% 3.20/1.59  BG Simplification    : 0.03
% 3.20/1.59  Subsumption          : 0.07
% 3.20/1.59  Abstraction          : 0.02
% 3.20/1.59  MUC search           : 0.00
% 3.20/1.59  Cooper               : 0.00
% 3.20/1.59  Total                : 0.85
% 3.20/1.59  Index Insertion      : 0.00
% 3.20/1.59  Index Deletion       : 0.00
% 3.20/1.59  Index Matching       : 0.00
% 3.20/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
