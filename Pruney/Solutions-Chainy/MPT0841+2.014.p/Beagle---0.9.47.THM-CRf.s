%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:34 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 288 expanded)
%              Number of leaves         :   34 ( 112 expanded)
%              Depth                    :    9
%              Number of atoms          :  216 ( 814 expanded)
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

tff(f_53,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_103,negated_conjecture,(
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

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_51,axiom,(
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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_68,axiom,(
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

tff(c_24,plain,(
    ! [A_49,B_50] : v1_relat_1(k2_zfmisc_1(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_66,plain,(
    ! [B_158,A_159] :
      ( v1_relat_1(B_158)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(A_159))
      | ~ v1_relat_1(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_42,c_66])).

tff(c_72,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_69])).

tff(c_718,plain,(
    ! [A_313,B_314,C_315,D_316] :
      ( k7_relset_1(A_313,B_314,C_315,D_316) = k9_relat_1(C_315,D_316)
      | ~ m1_subset_1(C_315,k1_zfmisc_1(k2_zfmisc_1(A_313,B_314))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_725,plain,(
    ! [D_316] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_316) = k9_relat_1('#skF_9',D_316) ),
    inference(resolution,[status(thm)],[c_42,c_718])).

tff(c_508,plain,(
    ! [A_263,B_264,C_265,D_266] :
      ( k7_relset_1(A_263,B_264,C_265,D_266) = k9_relat_1(C_265,D_266)
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(A_263,B_264))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_515,plain,(
    ! [D_266] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_266) = k9_relat_1('#skF_9',D_266) ),
    inference(resolution,[status(thm)],[c_42,c_508])).

tff(c_293,plain,(
    ! [A_212,B_213,C_214,D_215] :
      ( k7_relset_1(A_212,B_213,C_214,D_215) = k9_relat_1(C_214,D_215)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_212,B_213))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_300,plain,(
    ! [D_215] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_215) = k9_relat_1('#skF_9',D_215) ),
    inference(resolution,[status(thm)],[c_42,c_293])).

tff(c_64,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_73,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_56,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_74,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_60,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_85,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_179,plain,(
    ! [D_190,A_191,B_192,E_193] :
      ( r2_hidden(D_190,k9_relat_1(A_191,B_192))
      | ~ r2_hidden(E_193,B_192)
      | ~ r2_hidden(k4_tarski(E_193,D_190),A_191)
      | ~ v1_relat_1(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_195,plain,(
    ! [D_194,A_195] :
      ( r2_hidden(D_194,k9_relat_1(A_195,'#skF_7'))
      | ~ r2_hidden(k4_tarski('#skF_11',D_194),A_195)
      | ~ v1_relat_1(A_195) ) ),
    inference(resolution,[status(thm)],[c_74,c_179])).

tff(c_198,plain,
    ( r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_85,c_195])).

tff(c_201,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_198])).

tff(c_151,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( k7_relset_1(A_182,B_183,C_184,D_185) = k9_relat_1(C_184,D_185)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_158,plain,(
    ! [D_185] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_185) = k9_relat_1('#skF_9',D_185) ),
    inference(resolution,[status(thm)],[c_42,c_151])).

tff(c_50,plain,(
    ! [F_155] :
      ( ~ r2_hidden(F_155,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_155,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_155,'#skF_8')
      | ~ r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_226,plain,(
    ! [F_201] :
      ( ~ r2_hidden(F_201,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_201,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_201,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_158,c_50])).

tff(c_233,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_85,c_226])).

tff(c_240,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_74,c_233])).

tff(c_241,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_301,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_241])).

tff(c_311,plain,(
    ! [A_217,B_218,C_219] :
      ( r2_hidden('#skF_5'(A_217,B_218,C_219),k1_relat_1(C_219))
      | ~ r2_hidden(A_217,k9_relat_1(C_219,B_218))
      | ~ v1_relat_1(C_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_80,plain,(
    ! [A_164,B_165,C_166] :
      ( k1_relset_1(A_164,B_165,C_166) = k1_relat_1(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_84,plain,(
    k1_relset_1('#skF_8','#skF_6','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_42,c_80])).

tff(c_248,plain,(
    ! [A_205,B_206,C_207] :
      ( m1_subset_1(k1_relset_1(A_205,B_206,C_207),k1_zfmisc_1(A_205))
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_205,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_260,plain,
    ( m1_subset_1(k1_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_248])).

tff(c_265,plain,(
    m1_subset_1(k1_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_260])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( m1_subset_1(A_1,C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_272,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_8')
      | ~ r2_hidden(A_1,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_265,c_2])).

tff(c_315,plain,(
    ! [A_217,B_218] :
      ( m1_subset_1('#skF_5'(A_217,B_218,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_217,k9_relat_1('#skF_9',B_218))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_311,c_272])).

tff(c_319,plain,(
    ! [A_220,B_221] :
      ( m1_subset_1('#skF_5'(A_220,B_221,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_220,k9_relat_1('#skF_9',B_221)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_315])).

tff(c_327,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_301,c_319])).

tff(c_28,plain,(
    ! [A_51,B_52,C_53] :
      ( r2_hidden('#skF_5'(A_51,B_52,C_53),B_52)
      | ~ r2_hidden(A_51,k9_relat_1(C_53,B_52))
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_362,plain,(
    ! [A_232,B_233,C_234] :
      ( r2_hidden(k4_tarski('#skF_5'(A_232,B_233,C_234),A_232),C_234)
      | ~ r2_hidden(A_232,k9_relat_1(C_234,B_233))
      | ~ v1_relat_1(C_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_242,plain,(
    ~ r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,(
    ! [F_155] :
      ( ~ r2_hidden(F_155,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_155,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_155,'#skF_8')
      | r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_342,plain,(
    ! [F_155] :
      ( ~ r2_hidden(F_155,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_155,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_155,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_58])).

tff(c_366,plain,(
    ! [B_233] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_233,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_233,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_233))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_362,c_342])).

tff(c_430,plain,(
    ! [B_244] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_244,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_244,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_244)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_366])).

tff(c_434,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_28,c_430])).

tff(c_438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_301,c_327,c_434])).

tff(c_439,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_516,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_439])).

tff(c_526,plain,(
    ! [A_268,B_269,C_270] :
      ( r2_hidden('#skF_5'(A_268,B_269,C_270),k1_relat_1(C_270))
      | ~ r2_hidden(A_268,k9_relat_1(C_270,B_269))
      | ~ v1_relat_1(C_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_447,plain,(
    ! [A_249,B_250,C_251] :
      ( k1_relset_1(A_249,B_250,C_251) = k1_relat_1(C_251)
      | ~ m1_subset_1(C_251,k1_zfmisc_1(k2_zfmisc_1(A_249,B_250))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_451,plain,(
    k1_relset_1('#skF_8','#skF_6','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_42,c_447])).

tff(c_456,plain,(
    ! [A_252,B_253,C_254] :
      ( m1_subset_1(k1_relset_1(A_252,B_253,C_254),k1_zfmisc_1(A_252))
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_468,plain,
    ( m1_subset_1(k1_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_451,c_456])).

tff(c_473,plain,(
    m1_subset_1(k1_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_468])).

tff(c_479,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_8')
      | ~ r2_hidden(A_1,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_473,c_2])).

tff(c_530,plain,(
    ! [A_268,B_269] :
      ( m1_subset_1('#skF_5'(A_268,B_269,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_268,k9_relat_1('#skF_9',B_269))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_526,c_479])).

tff(c_535,plain,(
    ! [A_271,B_272] :
      ( m1_subset_1('#skF_5'(A_271,B_272,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_271,k9_relat_1('#skF_9',B_272)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_530])).

tff(c_543,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_516,c_535])).

tff(c_575,plain,(
    ! [A_281,B_282,C_283] :
      ( r2_hidden(k4_tarski('#skF_5'(A_281,B_282,C_283),A_281),C_283)
      | ~ r2_hidden(A_281,k9_relat_1(C_283,B_282))
      | ~ v1_relat_1(C_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_440,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,(
    ! [F_155] :
      ( ~ r2_hidden(F_155,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_155,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_155,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_481,plain,(
    ! [F_155] :
      ( ~ r2_hidden(F_155,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_155,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_155,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_440,c_54])).

tff(c_589,plain,(
    ! [B_282] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_282,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_282,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_282))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_575,c_481])).

tff(c_645,plain,(
    ! [B_294] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_294,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_294,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_294)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_589])).

tff(c_649,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_28,c_645])).

tff(c_653,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_516,c_543,c_649])).

tff(c_654,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_726,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_725,c_654])).

tff(c_736,plain,(
    ! [A_318,B_319,C_320] :
      ( r2_hidden('#skF_5'(A_318,B_319,C_320),k1_relat_1(C_320))
      | ~ r2_hidden(A_318,k9_relat_1(C_320,B_319))
      | ~ v1_relat_1(C_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_663,plain,(
    ! [A_299,B_300,C_301] :
      ( k1_relset_1(A_299,B_300,C_301) = k1_relat_1(C_301)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_299,B_300))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_667,plain,(
    k1_relset_1('#skF_8','#skF_6','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_42,c_663])).

tff(c_674,plain,(
    ! [A_303,B_304,C_305] :
      ( m1_subset_1(k1_relset_1(A_303,B_304,C_305),k1_zfmisc_1(A_303))
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(A_303,B_304))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_686,plain,
    ( m1_subset_1(k1_relat_1('#skF_9'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_667,c_674])).

tff(c_691,plain,(
    m1_subset_1(k1_relat_1('#skF_9'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_686])).

tff(c_697,plain,(
    ! [A_1] :
      ( m1_subset_1(A_1,'#skF_8')
      | ~ r2_hidden(A_1,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_691,c_2])).

tff(c_740,plain,(
    ! [A_318,B_319] :
      ( m1_subset_1('#skF_5'(A_318,B_319,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_318,k9_relat_1('#skF_9',B_319))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_736,c_697])).

tff(c_744,plain,(
    ! [A_321,B_322] :
      ( m1_subset_1('#skF_5'(A_321,B_322,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_321,k9_relat_1('#skF_9',B_322)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_740])).

tff(c_752,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_726,c_744])).

tff(c_754,plain,(
    ! [A_323,B_324,C_325] :
      ( r2_hidden(k4_tarski('#skF_5'(A_323,B_324,C_325),A_323),C_325)
      | ~ r2_hidden(A_323,k9_relat_1(C_325,B_324))
      | ~ v1_relat_1(C_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_655,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_62,plain,(
    ! [F_155] :
      ( ~ r2_hidden(F_155,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_155,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_155,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_668,plain,(
    ! [F_155] :
      ( ~ r2_hidden(F_155,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_155,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_155,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_655,c_62])).

tff(c_766,plain,(
    ! [B_324] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_324,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_324,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_324))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_754,c_668])).

tff(c_844,plain,(
    ! [B_342] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_342,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_342,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_342)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_766])).

tff(c_848,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_28,c_844])).

tff(c_852,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_726,c_752,c_848])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:19:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.45  
% 2.89/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.46  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 2.89/1.46  
% 2.89/1.46  %Foreground sorts:
% 2.89/1.46  
% 2.89/1.46  
% 2.89/1.46  %Background operators:
% 2.89/1.46  
% 2.89/1.46  
% 2.89/1.46  %Foreground operators:
% 2.89/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.89/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.46  tff('#skF_11', type, '#skF_11': $i).
% 2.89/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.89/1.46  tff('#skF_7', type, '#skF_7': $i).
% 2.89/1.46  tff('#skF_10', type, '#skF_10': $i).
% 2.89/1.46  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.89/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.89/1.46  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.89/1.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.89/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.89/1.46  tff('#skF_9', type, '#skF_9': $i).
% 2.89/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.89/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.89/1.46  tff('#skF_8', type, '#skF_8': $i).
% 2.89/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.89/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.89/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.89/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.89/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.89/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.46  
% 3.18/1.48  tff(f_53, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.18/1.48  tff(f_103, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 3.18/1.48  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.18/1.48  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.18/1.48  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 3.18/1.48  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 3.18/1.48  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.18/1.48  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.18/1.48  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.18/1.48  tff(c_24, plain, (![A_49, B_50]: (v1_relat_1(k2_zfmisc_1(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.18/1.48  tff(c_42, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.18/1.48  tff(c_66, plain, (![B_158, A_159]: (v1_relat_1(B_158) | ~m1_subset_1(B_158, k1_zfmisc_1(A_159)) | ~v1_relat_1(A_159))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.18/1.48  tff(c_69, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_6'))), inference(resolution, [status(thm)], [c_42, c_66])).
% 3.18/1.48  tff(c_72, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_69])).
% 3.18/1.48  tff(c_718, plain, (![A_313, B_314, C_315, D_316]: (k7_relset_1(A_313, B_314, C_315, D_316)=k9_relat_1(C_315, D_316) | ~m1_subset_1(C_315, k1_zfmisc_1(k2_zfmisc_1(A_313, B_314))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.18/1.48  tff(c_725, plain, (![D_316]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_316)=k9_relat_1('#skF_9', D_316))), inference(resolution, [status(thm)], [c_42, c_718])).
% 3.18/1.48  tff(c_508, plain, (![A_263, B_264, C_265, D_266]: (k7_relset_1(A_263, B_264, C_265, D_266)=k9_relat_1(C_265, D_266) | ~m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1(A_263, B_264))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.18/1.48  tff(c_515, plain, (![D_266]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_266)=k9_relat_1('#skF_9', D_266))), inference(resolution, [status(thm)], [c_42, c_508])).
% 3.18/1.48  tff(c_293, plain, (![A_212, B_213, C_214, D_215]: (k7_relset_1(A_212, B_213, C_214, D_215)=k9_relat_1(C_214, D_215) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_212, B_213))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.18/1.48  tff(c_300, plain, (![D_215]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_215)=k9_relat_1('#skF_9', D_215))), inference(resolution, [status(thm)], [c_42, c_293])).
% 3.18/1.48  tff(c_64, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.18/1.48  tff(c_73, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_64])).
% 3.18/1.48  tff(c_56, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | r2_hidden('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.18/1.48  tff(c_74, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_56])).
% 3.18/1.48  tff(c_60, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.18/1.48  tff(c_85, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_60])).
% 3.18/1.48  tff(c_179, plain, (![D_190, A_191, B_192, E_193]: (r2_hidden(D_190, k9_relat_1(A_191, B_192)) | ~r2_hidden(E_193, B_192) | ~r2_hidden(k4_tarski(E_193, D_190), A_191) | ~v1_relat_1(A_191))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.18/1.48  tff(c_195, plain, (![D_194, A_195]: (r2_hidden(D_194, k9_relat_1(A_195, '#skF_7')) | ~r2_hidden(k4_tarski('#skF_11', D_194), A_195) | ~v1_relat_1(A_195))), inference(resolution, [status(thm)], [c_74, c_179])).
% 3.18/1.48  tff(c_198, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_85, c_195])).
% 3.18/1.48  tff(c_201, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_198])).
% 3.18/1.48  tff(c_151, plain, (![A_182, B_183, C_184, D_185]: (k7_relset_1(A_182, B_183, C_184, D_185)=k9_relat_1(C_184, D_185) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.18/1.48  tff(c_158, plain, (![D_185]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_185)=k9_relat_1('#skF_9', D_185))), inference(resolution, [status(thm)], [c_42, c_151])).
% 3.18/1.48  tff(c_50, plain, (![F_155]: (~r2_hidden(F_155, '#skF_7') | ~r2_hidden(k4_tarski(F_155, '#skF_10'), '#skF_9') | ~m1_subset_1(F_155, '#skF_8') | ~r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.18/1.48  tff(c_226, plain, (![F_201]: (~r2_hidden(F_201, '#skF_7') | ~r2_hidden(k4_tarski(F_201, '#skF_10'), '#skF_9') | ~m1_subset_1(F_201, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_158, c_50])).
% 3.18/1.48  tff(c_233, plain, (~r2_hidden('#skF_11', '#skF_7') | ~m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_85, c_226])).
% 3.18/1.48  tff(c_240, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_74, c_233])).
% 3.18/1.48  tff(c_241, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_60])).
% 3.18/1.48  tff(c_301, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_300, c_241])).
% 3.18/1.48  tff(c_311, plain, (![A_217, B_218, C_219]: (r2_hidden('#skF_5'(A_217, B_218, C_219), k1_relat_1(C_219)) | ~r2_hidden(A_217, k9_relat_1(C_219, B_218)) | ~v1_relat_1(C_219))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.18/1.48  tff(c_80, plain, (![A_164, B_165, C_166]: (k1_relset_1(A_164, B_165, C_166)=k1_relat_1(C_166) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.18/1.48  tff(c_84, plain, (k1_relset_1('#skF_8', '#skF_6', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_42, c_80])).
% 3.18/1.48  tff(c_248, plain, (![A_205, B_206, C_207]: (m1_subset_1(k1_relset_1(A_205, B_206, C_207), k1_zfmisc_1(A_205)) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_205, B_206))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.18/1.48  tff(c_260, plain, (m1_subset_1(k1_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_84, c_248])).
% 3.18/1.48  tff(c_265, plain, (m1_subset_1(k1_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_260])).
% 3.18/1.48  tff(c_2, plain, (![A_1, C_3, B_2]: (m1_subset_1(A_1, C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.18/1.48  tff(c_272, plain, (![A_1]: (m1_subset_1(A_1, '#skF_8') | ~r2_hidden(A_1, k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_265, c_2])).
% 3.18/1.48  tff(c_315, plain, (![A_217, B_218]: (m1_subset_1('#skF_5'(A_217, B_218, '#skF_9'), '#skF_8') | ~r2_hidden(A_217, k9_relat_1('#skF_9', B_218)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_311, c_272])).
% 3.18/1.48  tff(c_319, plain, (![A_220, B_221]: (m1_subset_1('#skF_5'(A_220, B_221, '#skF_9'), '#skF_8') | ~r2_hidden(A_220, k9_relat_1('#skF_9', B_221)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_315])).
% 3.18/1.48  tff(c_327, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_301, c_319])).
% 3.18/1.48  tff(c_28, plain, (![A_51, B_52, C_53]: (r2_hidden('#skF_5'(A_51, B_52, C_53), B_52) | ~r2_hidden(A_51, k9_relat_1(C_53, B_52)) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.18/1.48  tff(c_362, plain, (![A_232, B_233, C_234]: (r2_hidden(k4_tarski('#skF_5'(A_232, B_233, C_234), A_232), C_234) | ~r2_hidden(A_232, k9_relat_1(C_234, B_233)) | ~v1_relat_1(C_234))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.18/1.48  tff(c_242, plain, (~r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_60])).
% 3.18/1.48  tff(c_58, plain, (![F_155]: (~r2_hidden(F_155, '#skF_7') | ~r2_hidden(k4_tarski(F_155, '#skF_10'), '#skF_9') | ~m1_subset_1(F_155, '#skF_8') | r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.18/1.48  tff(c_342, plain, (![F_155]: (~r2_hidden(F_155, '#skF_7') | ~r2_hidden(k4_tarski(F_155, '#skF_10'), '#skF_9') | ~m1_subset_1(F_155, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_242, c_58])).
% 3.18/1.48  tff(c_366, plain, (![B_233]: (~r2_hidden('#skF_5'('#skF_10', B_233, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_233, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_233)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_362, c_342])).
% 3.18/1.48  tff(c_430, plain, (![B_244]: (~r2_hidden('#skF_5'('#skF_10', B_244, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_244, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_244)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_366])).
% 3.18/1.48  tff(c_434, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_28, c_430])).
% 3.18/1.48  tff(c_438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_301, c_327, c_434])).
% 3.18/1.48  tff(c_439, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_56])).
% 3.18/1.48  tff(c_516, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_515, c_439])).
% 3.18/1.48  tff(c_526, plain, (![A_268, B_269, C_270]: (r2_hidden('#skF_5'(A_268, B_269, C_270), k1_relat_1(C_270)) | ~r2_hidden(A_268, k9_relat_1(C_270, B_269)) | ~v1_relat_1(C_270))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.18/1.48  tff(c_447, plain, (![A_249, B_250, C_251]: (k1_relset_1(A_249, B_250, C_251)=k1_relat_1(C_251) | ~m1_subset_1(C_251, k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.18/1.48  tff(c_451, plain, (k1_relset_1('#skF_8', '#skF_6', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_42, c_447])).
% 3.18/1.48  tff(c_456, plain, (![A_252, B_253, C_254]: (m1_subset_1(k1_relset_1(A_252, B_253, C_254), k1_zfmisc_1(A_252)) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_252, B_253))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.18/1.48  tff(c_468, plain, (m1_subset_1(k1_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_451, c_456])).
% 3.18/1.48  tff(c_473, plain, (m1_subset_1(k1_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_468])).
% 3.18/1.48  tff(c_479, plain, (![A_1]: (m1_subset_1(A_1, '#skF_8') | ~r2_hidden(A_1, k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_473, c_2])).
% 3.18/1.48  tff(c_530, plain, (![A_268, B_269]: (m1_subset_1('#skF_5'(A_268, B_269, '#skF_9'), '#skF_8') | ~r2_hidden(A_268, k9_relat_1('#skF_9', B_269)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_526, c_479])).
% 3.18/1.48  tff(c_535, plain, (![A_271, B_272]: (m1_subset_1('#skF_5'(A_271, B_272, '#skF_9'), '#skF_8') | ~r2_hidden(A_271, k9_relat_1('#skF_9', B_272)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_530])).
% 3.18/1.48  tff(c_543, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_516, c_535])).
% 3.18/1.48  tff(c_575, plain, (![A_281, B_282, C_283]: (r2_hidden(k4_tarski('#skF_5'(A_281, B_282, C_283), A_281), C_283) | ~r2_hidden(A_281, k9_relat_1(C_283, B_282)) | ~v1_relat_1(C_283))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.18/1.48  tff(c_440, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_56])).
% 3.18/1.48  tff(c_54, plain, (![F_155]: (~r2_hidden(F_155, '#skF_7') | ~r2_hidden(k4_tarski(F_155, '#skF_10'), '#skF_9') | ~m1_subset_1(F_155, '#skF_8') | r2_hidden('#skF_11', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.18/1.48  tff(c_481, plain, (![F_155]: (~r2_hidden(F_155, '#skF_7') | ~r2_hidden(k4_tarski(F_155, '#skF_10'), '#skF_9') | ~m1_subset_1(F_155, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_440, c_54])).
% 3.18/1.48  tff(c_589, plain, (![B_282]: (~r2_hidden('#skF_5'('#skF_10', B_282, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_282, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_282)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_575, c_481])).
% 3.18/1.48  tff(c_645, plain, (![B_294]: (~r2_hidden('#skF_5'('#skF_10', B_294, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_294, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_294)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_589])).
% 3.18/1.48  tff(c_649, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_28, c_645])).
% 3.18/1.48  tff(c_653, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_516, c_543, c_649])).
% 3.18/1.48  tff(c_654, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_64])).
% 3.18/1.48  tff(c_726, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_725, c_654])).
% 3.18/1.48  tff(c_736, plain, (![A_318, B_319, C_320]: (r2_hidden('#skF_5'(A_318, B_319, C_320), k1_relat_1(C_320)) | ~r2_hidden(A_318, k9_relat_1(C_320, B_319)) | ~v1_relat_1(C_320))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.18/1.48  tff(c_663, plain, (![A_299, B_300, C_301]: (k1_relset_1(A_299, B_300, C_301)=k1_relat_1(C_301) | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(A_299, B_300))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.18/1.48  tff(c_667, plain, (k1_relset_1('#skF_8', '#skF_6', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_42, c_663])).
% 3.18/1.48  tff(c_674, plain, (![A_303, B_304, C_305]: (m1_subset_1(k1_relset_1(A_303, B_304, C_305), k1_zfmisc_1(A_303)) | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(A_303, B_304))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.18/1.48  tff(c_686, plain, (m1_subset_1(k1_relat_1('#skF_9'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_667, c_674])).
% 3.18/1.48  tff(c_691, plain, (m1_subset_1(k1_relat_1('#skF_9'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_686])).
% 3.18/1.48  tff(c_697, plain, (![A_1]: (m1_subset_1(A_1, '#skF_8') | ~r2_hidden(A_1, k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_691, c_2])).
% 3.18/1.48  tff(c_740, plain, (![A_318, B_319]: (m1_subset_1('#skF_5'(A_318, B_319, '#skF_9'), '#skF_8') | ~r2_hidden(A_318, k9_relat_1('#skF_9', B_319)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_736, c_697])).
% 3.18/1.48  tff(c_744, plain, (![A_321, B_322]: (m1_subset_1('#skF_5'(A_321, B_322, '#skF_9'), '#skF_8') | ~r2_hidden(A_321, k9_relat_1('#skF_9', B_322)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_740])).
% 3.18/1.48  tff(c_752, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_726, c_744])).
% 3.18/1.48  tff(c_754, plain, (![A_323, B_324, C_325]: (r2_hidden(k4_tarski('#skF_5'(A_323, B_324, C_325), A_323), C_325) | ~r2_hidden(A_323, k9_relat_1(C_325, B_324)) | ~v1_relat_1(C_325))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.18/1.48  tff(c_655, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_64])).
% 3.18/1.48  tff(c_62, plain, (![F_155]: (~r2_hidden(F_155, '#skF_7') | ~r2_hidden(k4_tarski(F_155, '#skF_10'), '#skF_9') | ~m1_subset_1(F_155, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.18/1.48  tff(c_668, plain, (![F_155]: (~r2_hidden(F_155, '#skF_7') | ~r2_hidden(k4_tarski(F_155, '#skF_10'), '#skF_9') | ~m1_subset_1(F_155, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_655, c_62])).
% 3.18/1.48  tff(c_766, plain, (![B_324]: (~r2_hidden('#skF_5'('#skF_10', B_324, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_324, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_324)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_754, c_668])).
% 3.18/1.48  tff(c_844, plain, (![B_342]: (~r2_hidden('#skF_5'('#skF_10', B_342, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_342, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_342)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_766])).
% 3.18/1.48  tff(c_848, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_28, c_844])).
% 3.18/1.48  tff(c_852, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_726, c_752, c_848])).
% 3.18/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.48  
% 3.18/1.48  Inference rules
% 3.18/1.48  ----------------------
% 3.18/1.48  #Ref     : 0
% 3.18/1.48  #Sup     : 158
% 3.18/1.48  #Fact    : 0
% 3.18/1.48  #Define  : 0
% 3.18/1.48  #Split   : 8
% 3.18/1.48  #Chain   : 0
% 3.18/1.48  #Close   : 0
% 3.18/1.48  
% 3.18/1.48  Ordering : KBO
% 3.18/1.48  
% 3.18/1.48  Simplification rules
% 3.18/1.48  ----------------------
% 3.18/1.48  #Subsume      : 13
% 3.18/1.48  #Demod        : 50
% 3.18/1.48  #Tautology    : 24
% 3.18/1.48  #SimpNegUnit  : 3
% 3.18/1.48  #BackRed      : 3
% 3.18/1.48  
% 3.18/1.48  #Partial instantiations: 0
% 3.18/1.48  #Strategies tried      : 1
% 3.18/1.48  
% 3.18/1.48  Timing (in seconds)
% 3.18/1.48  ----------------------
% 3.18/1.48  Preprocessing        : 0.33
% 3.18/1.48  Parsing              : 0.17
% 3.18/1.48  CNF conversion       : 0.03
% 3.18/1.48  Main loop            : 0.36
% 3.18/1.48  Inferencing          : 0.14
% 3.18/1.48  Reduction            : 0.10
% 3.18/1.48  Demodulation         : 0.07
% 3.18/1.48  BG Simplification    : 0.02
% 3.18/1.48  Subsumption          : 0.07
% 3.18/1.48  Abstraction          : 0.02
% 3.18/1.48  MUC search           : 0.00
% 3.18/1.48  Cooper               : 0.00
% 3.18/1.48  Total                : 0.74
% 3.18/1.48  Index Insertion      : 0.00
% 3.18/1.48  Index Deletion       : 0.00
% 3.18/1.48  Index Matching       : 0.00
% 3.18/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
