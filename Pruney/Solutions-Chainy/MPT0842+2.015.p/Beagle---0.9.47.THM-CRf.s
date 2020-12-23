%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:37 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 283 expanded)
%              Number of leaves         :   35 ( 110 expanded)
%              Depth                    :    9
%              Number of atoms          :  224 ( 805 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
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

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_44,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_804,plain,(
    ! [C_324,B_325,A_326] :
      ( v5_relat_1(C_324,B_325)
      | ~ m1_subset_1(C_324,k1_zfmisc_1(k2_zfmisc_1(A_326,B_325))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_808,plain,(
    v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_804])).

tff(c_24,plain,(
    ! [A_48,B_49] : v1_relat_1(k2_zfmisc_1(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_69,plain,(
    ! [B_160,A_161] :
      ( v1_relat_1(B_160)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(A_161))
      | ~ v1_relat_1(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_72,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_44,c_69])).

tff(c_75,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_72])).

tff(c_1069,plain,(
    ! [A_388,B_389,C_390,D_391] :
      ( k8_relset_1(A_388,B_389,C_390,D_391) = k10_relat_1(C_390,D_391)
      | ~ m1_subset_1(C_390,k1_zfmisc_1(k2_zfmisc_1(A_388,B_389))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1072,plain,(
    ! [D_391] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_391) = k10_relat_1('#skF_9',D_391) ),
    inference(resolution,[status(thm)],[c_44,c_1069])).

tff(c_86,plain,(
    ! [C_165,B_166,A_167] :
      ( v5_relat_1(C_165,B_166)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_167,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_90,plain,(
    v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_86])).

tff(c_530,plain,(
    ! [A_269,B_270,C_271,D_272] :
      ( k8_relset_1(A_269,B_270,C_271,D_272) = k10_relat_1(C_271,D_272)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_269,B_270))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_533,plain,(
    ! [D_272] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_272) = k10_relat_1('#skF_9',D_272) ),
    inference(resolution,[status(thm)],[c_44,c_530])).

tff(c_252,plain,(
    ! [A_211,B_212,C_213,D_214] :
      ( k8_relset_1(A_211,B_212,C_213,D_214) = k10_relat_1(C_213,D_214)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_255,plain,(
    ! [D_214] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_214) = k10_relat_1('#skF_9',D_214) ),
    inference(resolution,[status(thm)],[c_44,c_252])).

tff(c_66,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_91,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_58,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_76,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_62,plain,
    ( r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_93,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_137,plain,(
    ! [D_188,A_189,B_190,E_191] :
      ( r2_hidden(D_188,k10_relat_1(A_189,B_190))
      | ~ r2_hidden(E_191,B_190)
      | ~ r2_hidden(k4_tarski(D_188,E_191),A_189)
      | ~ v1_relat_1(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_150,plain,(
    ! [D_192,A_193] :
      ( r2_hidden(D_192,k10_relat_1(A_193,'#skF_7'))
      | ~ r2_hidden(k4_tarski(D_192,'#skF_11'),A_193)
      | ~ v1_relat_1(A_193) ) ),
    inference(resolution,[status(thm)],[c_76,c_137])).

tff(c_153,plain,
    ( r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_93,c_150])).

tff(c_156,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_153])).

tff(c_121,plain,(
    ! [A_180,B_181,C_182,D_183] :
      ( k8_relset_1(A_180,B_181,C_182,D_183) = k10_relat_1(C_182,D_183)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_124,plain,(
    ! [D_183] : k8_relset_1('#skF_6','#skF_8','#skF_9',D_183) = k10_relat_1('#skF_9',D_183) ),
    inference(resolution,[status(thm)],[c_44,c_121])).

tff(c_52,plain,(
    ! [F_155] :
      ( ~ r2_hidden(F_155,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_155),'#skF_9')
      | ~ m1_subset_1(F_155,'#skF_8')
      | ~ r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_209,plain,(
    ! [F_201] :
      ( ~ r2_hidden(F_201,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_201),'#skF_9')
      | ~ m1_subset_1(F_201,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_124,c_52])).

tff(c_216,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_93,c_209])).

tff(c_223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_76,c_216])).

tff(c_224,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_257,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_224])).

tff(c_244,plain,(
    ! [A_208,B_209,C_210] :
      ( r2_hidden('#skF_5'(A_208,B_209,C_210),k2_relat_1(C_210))
      | ~ r2_hidden(A_208,k10_relat_1(C_210,B_209))
      | ~ v1_relat_1(C_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    ! [C_59,A_56,B_57] :
      ( r2_hidden(C_59,A_56)
      | ~ r2_hidden(C_59,k2_relat_1(B_57))
      | ~ v5_relat_1(B_57,A_56)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_372,plain,(
    ! [A_239,B_240,C_241,A_242] :
      ( r2_hidden('#skF_5'(A_239,B_240,C_241),A_242)
      | ~ v5_relat_1(C_241,A_242)
      | ~ r2_hidden(A_239,k10_relat_1(C_241,B_240))
      | ~ v1_relat_1(C_241) ) ),
    inference(resolution,[status(thm)],[c_244,c_34])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_408,plain,(
    ! [A_246,B_247,C_248,A_249] :
      ( m1_subset_1('#skF_5'(A_246,B_247,C_248),A_249)
      | ~ v5_relat_1(C_248,A_249)
      | ~ r2_hidden(A_246,k10_relat_1(C_248,B_247))
      | ~ v1_relat_1(C_248) ) ),
    inference(resolution,[status(thm)],[c_372,c_2])).

tff(c_421,plain,(
    ! [A_249] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_249)
      | ~ v5_relat_1('#skF_9',A_249)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_257,c_408])).

tff(c_431,plain,(
    ! [A_249] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_249)
      | ~ v5_relat_1('#skF_9',A_249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_421])).

tff(c_28,plain,(
    ! [A_50,B_51,C_52] :
      ( r2_hidden('#skF_5'(A_50,B_51,C_52),B_51)
      | ~ r2_hidden(A_50,k10_relat_1(C_52,B_51))
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,(
    ! [A_50,B_51,C_52] :
      ( r2_hidden(k4_tarski(A_50,'#skF_5'(A_50,B_51,C_52)),C_52)
      | ~ r2_hidden(A_50,k10_relat_1(C_52,B_51))
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_225,plain,(
    ~ r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_60,plain,(
    ! [F_155] :
      ( ~ r2_hidden(F_155,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_155),'#skF_9')
      | ~ m1_subset_1(F_155,'#skF_8')
      | r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_328,plain,(
    ! [F_232] :
      ( ~ r2_hidden(F_232,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_232),'#skF_9')
      | ~ m1_subset_1(F_232,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_225,c_60])).

tff(c_332,plain,(
    ! [B_51] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_51,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_51,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_51))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_30,c_328])).

tff(c_486,plain,(
    ! [B_259] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_259,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_259,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_259)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_332])).

tff(c_494,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_28,c_486])).

tff(c_500,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_257,c_494])).

tff(c_503,plain,(
    ~ v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_431,c_500])).

tff(c_507,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_503])).

tff(c_508,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_535,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_508])).

tff(c_545,plain,(
    ! [A_274,B_275,C_276] :
      ( r2_hidden('#skF_5'(A_274,B_275,C_276),k2_relat_1(C_276))
      | ~ r2_hidden(A_274,k10_relat_1(C_276,B_275))
      | ~ v1_relat_1(C_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_659,plain,(
    ! [A_300,B_301,C_302,A_303] :
      ( r2_hidden('#skF_5'(A_300,B_301,C_302),A_303)
      | ~ v5_relat_1(C_302,A_303)
      | ~ r2_hidden(A_300,k10_relat_1(C_302,B_301))
      | ~ v1_relat_1(C_302) ) ),
    inference(resolution,[status(thm)],[c_545,c_34])).

tff(c_695,plain,(
    ! [A_307,B_308,C_309,A_310] :
      ( m1_subset_1('#skF_5'(A_307,B_308,C_309),A_310)
      | ~ v5_relat_1(C_309,A_310)
      | ~ r2_hidden(A_307,k10_relat_1(C_309,B_308))
      | ~ v1_relat_1(C_309) ) ),
    inference(resolution,[status(thm)],[c_659,c_2])).

tff(c_708,plain,(
    ! [A_310] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_310)
      | ~ v5_relat_1('#skF_9',A_310)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_535,c_695])).

tff(c_718,plain,(
    ! [A_310] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_310)
      | ~ v5_relat_1('#skF_9',A_310) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_708])).

tff(c_567,plain,(
    ! [A_281,B_282,C_283] :
      ( r2_hidden(k4_tarski(A_281,'#skF_5'(A_281,B_282,C_283)),C_283)
      | ~ r2_hidden(A_281,k10_relat_1(C_283,B_282))
      | ~ v1_relat_1(C_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_509,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_64,plain,(
    ! [F_155] :
      ( ~ r2_hidden(F_155,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_155),'#skF_9')
      | ~ m1_subset_1(F_155,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_563,plain,(
    ! [F_155] :
      ( ~ r2_hidden(F_155,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_155),'#skF_9')
      | ~ m1_subset_1(F_155,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_509,c_64])).

tff(c_571,plain,(
    ! [B_282] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_282,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_282,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_282))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_567,c_563])).

tff(c_771,plain,(
    ! [B_320] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_320,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_320,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_320)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_571])).

tff(c_779,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_28,c_771])).

tff(c_785,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_535,c_779])).

tff(c_788,plain,(
    ~ v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_718,c_785])).

tff(c_792,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_788])).

tff(c_793,plain,(
    r2_hidden('#skF_10',k8_relset_1('#skF_6','#skF_8','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1094,plain,(
    r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1072,c_793])).

tff(c_1059,plain,(
    ! [A_384,B_385,C_386] :
      ( r2_hidden('#skF_5'(A_384,B_385,C_386),k2_relat_1(C_386))
      | ~ r2_hidden(A_384,k10_relat_1(C_386,B_385))
      | ~ v1_relat_1(C_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1176,plain,(
    ! [A_413,B_414,C_415,A_416] :
      ( r2_hidden('#skF_5'(A_413,B_414,C_415),A_416)
      | ~ v5_relat_1(C_415,A_416)
      | ~ r2_hidden(A_413,k10_relat_1(C_415,B_414))
      | ~ v1_relat_1(C_415) ) ),
    inference(resolution,[status(thm)],[c_1059,c_34])).

tff(c_1214,plain,(
    ! [A_420,B_421,C_422,A_423] :
      ( m1_subset_1('#skF_5'(A_420,B_421,C_422),A_423)
      | ~ v5_relat_1(C_422,A_423)
      | ~ r2_hidden(A_420,k10_relat_1(C_422,B_421))
      | ~ v1_relat_1(C_422) ) ),
    inference(resolution,[status(thm)],[c_1176,c_2])).

tff(c_1224,plain,(
    ! [A_423] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_423)
      | ~ v5_relat_1('#skF_9',A_423)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1094,c_1214])).

tff(c_1236,plain,(
    ! [A_423] :
      ( m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),A_423)
      | ~ v5_relat_1('#skF_9',A_423) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1224])).

tff(c_1073,plain,(
    ! [A_392,B_393,C_394] :
      ( r2_hidden(k4_tarski(A_392,'#skF_5'(A_392,B_393,C_394)),C_394)
      | ~ r2_hidden(A_392,k10_relat_1(C_394,B_393))
      | ~ v1_relat_1(C_394) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_794,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,(
    ! [F_155] :
      ( ~ r2_hidden(F_155,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_155),'#skF_9')
      | ~ m1_subset_1(F_155,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1067,plain,(
    ! [F_155] :
      ( ~ r2_hidden(F_155,'#skF_7')
      | ~ r2_hidden(k4_tarski('#skF_10',F_155),'#skF_9')
      | ~ m1_subset_1(F_155,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_794,c_56])).

tff(c_1077,plain,(
    ! [B_393] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_393,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_393,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_393))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1073,c_1067])).

tff(c_1269,plain,(
    ! [B_433] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_433,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_433,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9',B_433)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1077])).

tff(c_1277,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k10_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_28,c_1269])).

tff(c_1283,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1094,c_1277])).

tff(c_1286,plain,(
    ~ v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_1236,c_1283])).

tff(c_1290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_1286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.78/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.70  
% 3.78/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.70  %$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 3.78/1.70  
% 3.78/1.70  %Foreground sorts:
% 3.78/1.70  
% 3.78/1.70  
% 3.78/1.70  %Background operators:
% 3.78/1.70  
% 3.78/1.70  
% 3.78/1.70  %Foreground operators:
% 3.78/1.70  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.78/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.78/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.78/1.70  tff('#skF_11', type, '#skF_11': $i).
% 3.78/1.70  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.78/1.70  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.78/1.70  tff('#skF_7', type, '#skF_7': $i).
% 3.78/1.70  tff('#skF_10', type, '#skF_10': $i).
% 3.78/1.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.78/1.70  tff('#skF_6', type, '#skF_6': $i).
% 3.78/1.70  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.78/1.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.78/1.70  tff('#skF_9', type, '#skF_9': $i).
% 3.78/1.70  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.78/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.78/1.70  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.78/1.70  tff('#skF_8', type, '#skF_8': $i).
% 3.78/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.78/1.70  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.78/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.78/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.78/1.70  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.78/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.78/1.70  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.78/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.78/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.78/1.70  
% 3.78/1.72  tff(f_108, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_relset_1)).
% 3.78/1.72  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.78/1.72  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.78/1.72  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.78/1.72  tff(f_81, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.78/1.72  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 3.78/1.72  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 3.78/1.72  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 3.78/1.72  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.78/1.72  tff(c_44, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.78/1.72  tff(c_804, plain, (![C_324, B_325, A_326]: (v5_relat_1(C_324, B_325) | ~m1_subset_1(C_324, k1_zfmisc_1(k2_zfmisc_1(A_326, B_325))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.78/1.72  tff(c_808, plain, (v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_44, c_804])).
% 3.78/1.72  tff(c_24, plain, (![A_48, B_49]: (v1_relat_1(k2_zfmisc_1(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.78/1.72  tff(c_69, plain, (![B_160, A_161]: (v1_relat_1(B_160) | ~m1_subset_1(B_160, k1_zfmisc_1(A_161)) | ~v1_relat_1(A_161))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.78/1.72  tff(c_72, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_44, c_69])).
% 3.78/1.72  tff(c_75, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_72])).
% 3.78/1.72  tff(c_1069, plain, (![A_388, B_389, C_390, D_391]: (k8_relset_1(A_388, B_389, C_390, D_391)=k10_relat_1(C_390, D_391) | ~m1_subset_1(C_390, k1_zfmisc_1(k2_zfmisc_1(A_388, B_389))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.78/1.72  tff(c_1072, plain, (![D_391]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_391)=k10_relat_1('#skF_9', D_391))), inference(resolution, [status(thm)], [c_44, c_1069])).
% 3.78/1.72  tff(c_86, plain, (![C_165, B_166, A_167]: (v5_relat_1(C_165, B_166) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_167, B_166))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.78/1.72  tff(c_90, plain, (v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_44, c_86])).
% 3.78/1.72  tff(c_530, plain, (![A_269, B_270, C_271, D_272]: (k8_relset_1(A_269, B_270, C_271, D_272)=k10_relat_1(C_271, D_272) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_269, B_270))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.78/1.72  tff(c_533, plain, (![D_272]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_272)=k10_relat_1('#skF_9', D_272))), inference(resolution, [status(thm)], [c_44, c_530])).
% 3.78/1.72  tff(c_252, plain, (![A_211, B_212, C_213, D_214]: (k8_relset_1(A_211, B_212, C_213, D_214)=k10_relat_1(C_213, D_214) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.78/1.72  tff(c_255, plain, (![D_214]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_214)=k10_relat_1('#skF_9', D_214))), inference(resolution, [status(thm)], [c_44, c_252])).
% 3.78/1.72  tff(c_66, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.78/1.72  tff(c_91, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_66])).
% 3.78/1.72  tff(c_58, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.78/1.72  tff(c_76, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_58])).
% 3.78/1.72  tff(c_62, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')) | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.78/1.72  tff(c_93, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitLeft, [status(thm)], [c_62])).
% 3.78/1.72  tff(c_137, plain, (![D_188, A_189, B_190, E_191]: (r2_hidden(D_188, k10_relat_1(A_189, B_190)) | ~r2_hidden(E_191, B_190) | ~r2_hidden(k4_tarski(D_188, E_191), A_189) | ~v1_relat_1(A_189))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.78/1.72  tff(c_150, plain, (![D_192, A_193]: (r2_hidden(D_192, k10_relat_1(A_193, '#skF_7')) | ~r2_hidden(k4_tarski(D_192, '#skF_11'), A_193) | ~v1_relat_1(A_193))), inference(resolution, [status(thm)], [c_76, c_137])).
% 3.78/1.72  tff(c_153, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_93, c_150])).
% 3.78/1.72  tff(c_156, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_153])).
% 3.78/1.72  tff(c_121, plain, (![A_180, B_181, C_182, D_183]: (k8_relset_1(A_180, B_181, C_182, D_183)=k10_relat_1(C_182, D_183) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.78/1.72  tff(c_124, plain, (![D_183]: (k8_relset_1('#skF_6', '#skF_8', '#skF_9', D_183)=k10_relat_1('#skF_9', D_183))), inference(resolution, [status(thm)], [c_44, c_121])).
% 3.78/1.72  tff(c_52, plain, (![F_155]: (~r2_hidden(F_155, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_155), '#skF_9') | ~m1_subset_1(F_155, '#skF_8') | ~r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.78/1.72  tff(c_209, plain, (![F_201]: (~r2_hidden(F_201, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_201), '#skF_9') | ~m1_subset_1(F_201, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_124, c_52])).
% 3.78/1.72  tff(c_216, plain, (~r2_hidden('#skF_11', '#skF_7') | ~m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_93, c_209])).
% 3.78/1.72  tff(c_223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_76, c_216])).
% 3.78/1.72  tff(c_224, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_62])).
% 3.78/1.72  tff(c_257, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_255, c_224])).
% 3.78/1.72  tff(c_244, plain, (![A_208, B_209, C_210]: (r2_hidden('#skF_5'(A_208, B_209, C_210), k2_relat_1(C_210)) | ~r2_hidden(A_208, k10_relat_1(C_210, B_209)) | ~v1_relat_1(C_210))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.78/1.72  tff(c_34, plain, (![C_59, A_56, B_57]: (r2_hidden(C_59, A_56) | ~r2_hidden(C_59, k2_relat_1(B_57)) | ~v5_relat_1(B_57, A_56) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.78/1.72  tff(c_372, plain, (![A_239, B_240, C_241, A_242]: (r2_hidden('#skF_5'(A_239, B_240, C_241), A_242) | ~v5_relat_1(C_241, A_242) | ~r2_hidden(A_239, k10_relat_1(C_241, B_240)) | ~v1_relat_1(C_241))), inference(resolution, [status(thm)], [c_244, c_34])).
% 3.78/1.72  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.78/1.72  tff(c_408, plain, (![A_246, B_247, C_248, A_249]: (m1_subset_1('#skF_5'(A_246, B_247, C_248), A_249) | ~v5_relat_1(C_248, A_249) | ~r2_hidden(A_246, k10_relat_1(C_248, B_247)) | ~v1_relat_1(C_248))), inference(resolution, [status(thm)], [c_372, c_2])).
% 3.78/1.72  tff(c_421, plain, (![A_249]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_249) | ~v5_relat_1('#skF_9', A_249) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_257, c_408])).
% 3.78/1.72  tff(c_431, plain, (![A_249]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_249) | ~v5_relat_1('#skF_9', A_249))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_421])).
% 3.78/1.72  tff(c_28, plain, (![A_50, B_51, C_52]: (r2_hidden('#skF_5'(A_50, B_51, C_52), B_51) | ~r2_hidden(A_50, k10_relat_1(C_52, B_51)) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.78/1.72  tff(c_30, plain, (![A_50, B_51, C_52]: (r2_hidden(k4_tarski(A_50, '#skF_5'(A_50, B_51, C_52)), C_52) | ~r2_hidden(A_50, k10_relat_1(C_52, B_51)) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.78/1.72  tff(c_225, plain, (~r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9')), inference(splitRight, [status(thm)], [c_62])).
% 3.78/1.72  tff(c_60, plain, (![F_155]: (~r2_hidden(F_155, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_155), '#skF_9') | ~m1_subset_1(F_155, '#skF_8') | r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.78/1.72  tff(c_328, plain, (![F_232]: (~r2_hidden(F_232, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_232), '#skF_9') | ~m1_subset_1(F_232, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_225, c_60])).
% 3.78/1.72  tff(c_332, plain, (![B_51]: (~r2_hidden('#skF_5'('#skF_10', B_51, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_51, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_51)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_30, c_328])).
% 3.78/1.72  tff(c_486, plain, (![B_259]: (~r2_hidden('#skF_5'('#skF_10', B_259, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_259, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_259)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_332])).
% 3.78/1.72  tff(c_494, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_28, c_486])).
% 3.78/1.72  tff(c_500, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_257, c_494])).
% 3.78/1.72  tff(c_503, plain, (~v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_431, c_500])).
% 3.78/1.72  tff(c_507, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_503])).
% 3.78/1.72  tff(c_508, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_66])).
% 3.78/1.72  tff(c_535, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_533, c_508])).
% 3.78/1.72  tff(c_545, plain, (![A_274, B_275, C_276]: (r2_hidden('#skF_5'(A_274, B_275, C_276), k2_relat_1(C_276)) | ~r2_hidden(A_274, k10_relat_1(C_276, B_275)) | ~v1_relat_1(C_276))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.78/1.72  tff(c_659, plain, (![A_300, B_301, C_302, A_303]: (r2_hidden('#skF_5'(A_300, B_301, C_302), A_303) | ~v5_relat_1(C_302, A_303) | ~r2_hidden(A_300, k10_relat_1(C_302, B_301)) | ~v1_relat_1(C_302))), inference(resolution, [status(thm)], [c_545, c_34])).
% 3.78/1.72  tff(c_695, plain, (![A_307, B_308, C_309, A_310]: (m1_subset_1('#skF_5'(A_307, B_308, C_309), A_310) | ~v5_relat_1(C_309, A_310) | ~r2_hidden(A_307, k10_relat_1(C_309, B_308)) | ~v1_relat_1(C_309))), inference(resolution, [status(thm)], [c_659, c_2])).
% 3.78/1.72  tff(c_708, plain, (![A_310]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_310) | ~v5_relat_1('#skF_9', A_310) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_535, c_695])).
% 3.78/1.72  tff(c_718, plain, (![A_310]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_310) | ~v5_relat_1('#skF_9', A_310))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_708])).
% 3.78/1.72  tff(c_567, plain, (![A_281, B_282, C_283]: (r2_hidden(k4_tarski(A_281, '#skF_5'(A_281, B_282, C_283)), C_283) | ~r2_hidden(A_281, k10_relat_1(C_283, B_282)) | ~v1_relat_1(C_283))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.78/1.72  tff(c_509, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_66])).
% 3.78/1.72  tff(c_64, plain, (![F_155]: (~r2_hidden(F_155, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_155), '#skF_9') | ~m1_subset_1(F_155, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.78/1.72  tff(c_563, plain, (![F_155]: (~r2_hidden(F_155, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_155), '#skF_9') | ~m1_subset_1(F_155, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_509, c_64])).
% 3.78/1.72  tff(c_571, plain, (![B_282]: (~r2_hidden('#skF_5'('#skF_10', B_282, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_282, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_282)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_567, c_563])).
% 3.78/1.72  tff(c_771, plain, (![B_320]: (~r2_hidden('#skF_5'('#skF_10', B_320, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_320, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_320)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_571])).
% 3.78/1.72  tff(c_779, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_28, c_771])).
% 3.78/1.72  tff(c_785, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_535, c_779])).
% 3.78/1.72  tff(c_788, plain, (~v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_718, c_785])).
% 3.78/1.72  tff(c_792, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_788])).
% 3.78/1.72  tff(c_793, plain, (r2_hidden('#skF_10', k8_relset_1('#skF_6', '#skF_8', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_58])).
% 3.78/1.72  tff(c_1094, plain, (r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1072, c_793])).
% 3.78/1.72  tff(c_1059, plain, (![A_384, B_385, C_386]: (r2_hidden('#skF_5'(A_384, B_385, C_386), k2_relat_1(C_386)) | ~r2_hidden(A_384, k10_relat_1(C_386, B_385)) | ~v1_relat_1(C_386))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.78/1.72  tff(c_1176, plain, (![A_413, B_414, C_415, A_416]: (r2_hidden('#skF_5'(A_413, B_414, C_415), A_416) | ~v5_relat_1(C_415, A_416) | ~r2_hidden(A_413, k10_relat_1(C_415, B_414)) | ~v1_relat_1(C_415))), inference(resolution, [status(thm)], [c_1059, c_34])).
% 3.78/1.72  tff(c_1214, plain, (![A_420, B_421, C_422, A_423]: (m1_subset_1('#skF_5'(A_420, B_421, C_422), A_423) | ~v5_relat_1(C_422, A_423) | ~r2_hidden(A_420, k10_relat_1(C_422, B_421)) | ~v1_relat_1(C_422))), inference(resolution, [status(thm)], [c_1176, c_2])).
% 3.78/1.72  tff(c_1224, plain, (![A_423]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_423) | ~v5_relat_1('#skF_9', A_423) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1094, c_1214])).
% 3.78/1.72  tff(c_1236, plain, (![A_423]: (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), A_423) | ~v5_relat_1('#skF_9', A_423))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1224])).
% 3.78/1.72  tff(c_1073, plain, (![A_392, B_393, C_394]: (r2_hidden(k4_tarski(A_392, '#skF_5'(A_392, B_393, C_394)), C_394) | ~r2_hidden(A_392, k10_relat_1(C_394, B_393)) | ~v1_relat_1(C_394))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.78/1.72  tff(c_794, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_58])).
% 3.78/1.72  tff(c_56, plain, (![F_155]: (~r2_hidden(F_155, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_155), '#skF_9') | ~m1_subset_1(F_155, '#skF_8') | r2_hidden('#skF_11', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.78/1.72  tff(c_1067, plain, (![F_155]: (~r2_hidden(F_155, '#skF_7') | ~r2_hidden(k4_tarski('#skF_10', F_155), '#skF_9') | ~m1_subset_1(F_155, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_794, c_56])).
% 3.78/1.72  tff(c_1077, plain, (![B_393]: (~r2_hidden('#skF_5'('#skF_10', B_393, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_393, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_393)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1073, c_1067])).
% 3.78/1.72  tff(c_1269, plain, (![B_433]: (~r2_hidden('#skF_5'('#skF_10', B_433, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_433, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', B_433)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1077])).
% 3.78/1.72  tff(c_1277, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k10_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_28, c_1269])).
% 3.78/1.72  tff(c_1283, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1094, c_1277])).
% 3.78/1.72  tff(c_1286, plain, (~v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_1236, c_1283])).
% 3.78/1.72  tff(c_1290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_808, c_1286])).
% 3.78/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.72  
% 3.78/1.72  Inference rules
% 3.78/1.72  ----------------------
% 3.78/1.72  #Ref     : 0
% 3.78/1.72  #Sup     : 252
% 3.78/1.72  #Fact    : 0
% 3.78/1.72  #Define  : 0
% 3.78/1.72  #Split   : 8
% 3.78/1.72  #Chain   : 0
% 3.78/1.72  #Close   : 0
% 3.78/1.72  
% 3.78/1.72  Ordering : KBO
% 3.78/1.72  
% 3.78/1.72  Simplification rules
% 3.78/1.72  ----------------------
% 3.78/1.72  #Subsume      : 10
% 3.78/1.72  #Demod        : 67
% 3.78/1.72  #Tautology    : 23
% 3.78/1.72  #SimpNegUnit  : 4
% 3.78/1.72  #BackRed      : 8
% 3.78/1.72  
% 3.78/1.72  #Partial instantiations: 0
% 3.78/1.72  #Strategies tried      : 1
% 3.78/1.72  
% 3.78/1.72  Timing (in seconds)
% 3.78/1.72  ----------------------
% 3.78/1.72  Preprocessing        : 0.35
% 3.78/1.72  Parsing              : 0.17
% 3.78/1.72  CNF conversion       : 0.04
% 3.78/1.72  Main loop            : 0.56
% 3.78/1.73  Inferencing          : 0.21
% 3.78/1.73  Reduction            : 0.16
% 3.78/1.73  Demodulation         : 0.11
% 3.78/1.73  BG Simplification    : 0.03
% 3.78/1.73  Subsumption          : 0.10
% 3.78/1.73  Abstraction          : 0.03
% 3.78/1.73  MUC search           : 0.00
% 3.78/1.73  Cooper               : 0.00
% 3.78/1.73  Total                : 0.95
% 3.78/1.73  Index Insertion      : 0.00
% 3.78/1.73  Index Deletion       : 0.00
% 3.78/1.73  Index Matching       : 0.00
% 3.78/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
