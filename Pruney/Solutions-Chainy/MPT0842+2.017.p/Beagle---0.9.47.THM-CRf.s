%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:37 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 306 expanded)
%              Number of leaves         :   32 ( 115 expanded)
%              Depth                    :    9
%              Number of atoms          :  238 ( 889 expanded)
%              Number of equality atoms :    9 (  24 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_58,axiom,(
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

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_743,plain,(
    ! [C_272,B_273,A_274] :
      ( v5_relat_1(C_272,B_273)
      | ~ m1_subset_1(C_272,k1_zfmisc_1(k2_zfmisc_1(A_274,B_273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_747,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_743])).

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_55,plain,(
    ! [B_121,A_122] :
      ( v1_relat_1(B_121)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(A_122))
      | ~ v1_relat_1(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_58,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_55])).

tff(c_61,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_58])).

tff(c_780,plain,(
    ! [A_296,B_297,C_298,D_299] :
      ( k8_relset_1(A_296,B_297,C_298,D_299) = k10_relat_1(C_298,D_299)
      | ~ m1_subset_1(C_298,k1_zfmisc_1(k2_zfmisc_1(A_296,B_297))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_783,plain,(
    ! [D_299] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_299) = k10_relat_1('#skF_5',D_299) ),
    inference(resolution,[status(thm)],[c_30,c_780])).

tff(c_67,plain,(
    ! [C_123,B_124,A_125] :
      ( v5_relat_1(C_123,B_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_71,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_67])).

tff(c_566,plain,(
    ! [A_245,B_246,C_247,D_248] :
      ( k8_relset_1(A_245,B_246,C_247,D_248) = k10_relat_1(C_247,D_248)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_569,plain,(
    ! [D_248] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_248) = k10_relat_1('#skF_5',D_248) ),
    inference(resolution,[status(thm)],[c_30,c_566])).

tff(c_351,plain,(
    ! [A_195,B_196,C_197,D_198] :
      ( k8_relset_1(A_195,B_196,C_197,D_198) = k10_relat_1(C_197,D_198)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_354,plain,(
    ! [D_198] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_198) = k10_relat_1('#skF_5',D_198) ),
    inference(resolution,[status(thm)],[c_30,c_351])).

tff(c_52,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | m1_subset_1('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_77,plain,(
    m1_subset_1('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_44,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | r2_hidden('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_62,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_48,plain,
    ( r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3'))
    | r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_79,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_136,plain,(
    ! [A_145,B_146,C_147,D_148] :
      ( k8_relset_1(A_145,B_146,C_147,D_148) = k10_relat_1(C_147,D_148)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_139,plain,(
    ! [D_148] : k8_relset_1('#skF_2','#skF_4','#skF_5',D_148) = k10_relat_1('#skF_5',D_148) ),
    inference(resolution,[status(thm)],[c_30,c_136])).

tff(c_38,plain,(
    ! [F_116] :
      ( ~ r2_hidden(F_116,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_116),'#skF_5')
      | ~ m1_subset_1(F_116,'#skF_4')
      | ~ r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_243,plain,(
    ! [F_116] :
      ( ~ r2_hidden(F_116,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_116),'#skF_5')
      | ~ m1_subset_1(F_116,'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_38])).

tff(c_244,plain,(
    ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_243])).

tff(c_18,plain,(
    ! [B_19,C_20,A_18] :
      ( r2_hidden(B_19,k2_relat_1(C_20))
      | ~ r2_hidden(k4_tarski(A_18,B_19),C_20)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_82,plain,
    ( r2_hidden('#skF_7',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_79,c_18])).

tff(c_88,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_82])).

tff(c_245,plain,(
    ! [A_173,C_174,B_175,D_176] :
      ( r2_hidden(A_173,k10_relat_1(C_174,B_175))
      | ~ r2_hidden(D_176,B_175)
      | ~ r2_hidden(k4_tarski(A_173,D_176),C_174)
      | ~ r2_hidden(D_176,k2_relat_1(C_174))
      | ~ v1_relat_1(C_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_273,plain,(
    ! [A_177,C_178] :
      ( r2_hidden(A_177,k10_relat_1(C_178,'#skF_3'))
      | ~ r2_hidden(k4_tarski(A_177,'#skF_7'),C_178)
      | ~ r2_hidden('#skF_7',k2_relat_1(C_178))
      | ~ v1_relat_1(C_178) ) ),
    inference(resolution,[status(thm)],[c_62,c_245])).

tff(c_276,plain,
    ( r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ r2_hidden('#skF_7',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_79,c_273])).

tff(c_279,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_88,c_276])).

tff(c_281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_279])).

tff(c_304,plain,(
    ! [F_179] :
      ( ~ r2_hidden(F_179,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_179),'#skF_5')
      | ~ m1_subset_1(F_179,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_311,plain,
    ( ~ r2_hidden('#skF_7','#skF_3')
    | ~ m1_subset_1('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_79,c_304])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_62,c_311])).

tff(c_319,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_356,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_319])).

tff(c_342,plain,(
    ! [A_192,B_193,C_194] :
      ( r2_hidden('#skF_1'(A_192,B_193,C_194),k2_relat_1(C_194))
      | ~ r2_hidden(A_192,k10_relat_1(C_194,B_193))
      | ~ v1_relat_1(C_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [C_17,A_14,B_15] :
      ( r2_hidden(C_17,A_14)
      | ~ r2_hidden(C_17,k2_relat_1(B_15))
      | ~ v5_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_448,plain,(
    ! [A_213,B_214,C_215,A_216] :
      ( r2_hidden('#skF_1'(A_213,B_214,C_215),A_216)
      | ~ v5_relat_1(C_215,A_216)
      | ~ r2_hidden(A_213,k10_relat_1(C_215,B_214))
      | ~ v1_relat_1(C_215) ) ),
    inference(resolution,[status(thm)],[c_342,c_16])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_466,plain,(
    ! [A_217,B_218,C_219,A_220] :
      ( m1_subset_1('#skF_1'(A_217,B_218,C_219),A_220)
      | ~ v5_relat_1(C_219,A_220)
      | ~ r2_hidden(A_217,k10_relat_1(C_219,B_218))
      | ~ v1_relat_1(C_219) ) ),
    inference(resolution,[status(thm)],[c_448,c_2])).

tff(c_474,plain,(
    ! [A_220] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_220)
      | ~ v5_relat_1('#skF_5',A_220)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_356,c_466])).

tff(c_482,plain,(
    ! [A_220] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_220)
      | ~ v5_relat_1('#skF_5',A_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_474])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( r2_hidden('#skF_1'(A_8,B_9,C_10),B_9)
      | ~ r2_hidden(A_8,k10_relat_1(C_10,B_9))
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( r2_hidden(k4_tarski(A_8,'#skF_1'(A_8,B_9,C_10)),C_10)
      | ~ r2_hidden(A_8,k10_relat_1(C_10,B_9))
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_320,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [F_116] :
      ( ~ r2_hidden(F_116,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_116),'#skF_5')
      | ~ m1_subset_1(F_116,'#skF_4')
      | r2_hidden(k4_tarski('#skF_6','#skF_7'),'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_419,plain,(
    ! [F_206] :
      ( ~ r2_hidden(F_206,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_206),'#skF_5')
      | ~ m1_subset_1(F_206,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_46])).

tff(c_423,plain,(
    ! [B_9] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_9,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_9,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_9))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_419])).

tff(c_509,plain,(
    ! [B_225] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_225,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_225,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_225)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_423])).

tff(c_517,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_509])).

tff(c_523,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_356,c_517])).

tff(c_526,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_482,c_523])).

tff(c_530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_526])).

tff(c_531,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_599,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_569,c_531])).

tff(c_556,plain,(
    ! [A_241,B_242,C_243] :
      ( r2_hidden('#skF_1'(A_241,B_242,C_243),k2_relat_1(C_243))
      | ~ r2_hidden(A_241,k10_relat_1(C_243,B_242))
      | ~ v1_relat_1(C_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_663,plain,(
    ! [A_262,B_263,C_264,A_265] :
      ( r2_hidden('#skF_1'(A_262,B_263,C_264),A_265)
      | ~ v5_relat_1(C_264,A_265)
      | ~ r2_hidden(A_262,k10_relat_1(C_264,B_263))
      | ~ v1_relat_1(C_264) ) ),
    inference(resolution,[status(thm)],[c_556,c_16])).

tff(c_681,plain,(
    ! [A_266,B_267,C_268,A_269] :
      ( m1_subset_1('#skF_1'(A_266,B_267,C_268),A_269)
      | ~ v5_relat_1(C_268,A_269)
      | ~ r2_hidden(A_266,k10_relat_1(C_268,B_267))
      | ~ v1_relat_1(C_268) ) ),
    inference(resolution,[status(thm)],[c_663,c_2])).

tff(c_686,plain,(
    ! [A_269] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_269)
      | ~ v5_relat_1('#skF_5',A_269)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_599,c_681])).

tff(c_714,plain,(
    ! [A_271] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_271)
      | ~ v5_relat_1('#skF_5',A_271) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_686])).

tff(c_570,plain,(
    ! [A_249,B_250,C_251] :
      ( r2_hidden(k4_tarski(A_249,'#skF_1'(A_249,B_250,C_251)),C_251)
      | ~ r2_hidden(A_249,k10_relat_1(C_251,B_250))
      | ~ v1_relat_1(C_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_532,plain,(
    ~ m1_subset_1('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,(
    ! [F_116] :
      ( ~ r2_hidden(F_116,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_116),'#skF_5')
      | ~ m1_subset_1(F_116,'#skF_4')
      | m1_subset_1('#skF_7','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_564,plain,(
    ! [F_116] :
      ( ~ r2_hidden(F_116,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_116),'#skF_5')
      | ~ m1_subset_1(F_116,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_532,c_50])).

tff(c_574,plain,(
    ! [B_250] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_250,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_250,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_250))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_570,c_564])).

tff(c_699,plain,(
    ! [B_270] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_270,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_270,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_270)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_574])).

tff(c_707,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_699])).

tff(c_713,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_599,c_707])).

tff(c_717,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_714,c_713])).

tff(c_736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_717])).

tff(c_737,plain,(
    r2_hidden('#skF_6',k8_relset_1('#skF_2','#skF_4','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_785,plain,(
    r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_737])).

tff(c_767,plain,(
    ! [A_290,B_291,C_292] :
      ( r2_hidden('#skF_1'(A_290,B_291,C_292),k2_relat_1(C_292))
      | ~ r2_hidden(A_290,k10_relat_1(C_292,B_291))
      | ~ v1_relat_1(C_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_877,plain,(
    ! [A_314,B_315,C_316,A_317] :
      ( r2_hidden('#skF_1'(A_314,B_315,C_316),A_317)
      | ~ v5_relat_1(C_316,A_317)
      | ~ r2_hidden(A_314,k10_relat_1(C_316,B_315))
      | ~ v1_relat_1(C_316) ) ),
    inference(resolution,[status(thm)],[c_767,c_16])).

tff(c_895,plain,(
    ! [A_318,B_319,C_320,A_321] :
      ( m1_subset_1('#skF_1'(A_318,B_319,C_320),A_321)
      | ~ v5_relat_1(C_320,A_321)
      | ~ r2_hidden(A_318,k10_relat_1(C_320,B_319))
      | ~ v1_relat_1(C_320) ) ),
    inference(resolution,[status(thm)],[c_877,c_2])).

tff(c_903,plain,(
    ! [A_321] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_321)
      | ~ v5_relat_1('#skF_5',A_321)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_785,c_895])).

tff(c_911,plain,(
    ! [A_321] :
      ( m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),A_321)
      | ~ v5_relat_1('#skF_5',A_321) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_903])).

tff(c_807,plain,(
    ! [A_302,B_303,C_304] :
      ( r2_hidden(k4_tarski(A_302,'#skF_1'(A_302,B_303,C_304)),C_304)
      | ~ r2_hidden(A_302,k10_relat_1(C_304,B_303))
      | ~ v1_relat_1(C_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_738,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,(
    ! [F_116] :
      ( ~ r2_hidden(F_116,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_116),'#skF_5')
      | ~ m1_subset_1(F_116,'#skF_4')
      | r2_hidden('#skF_7','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_795,plain,(
    ! [F_116] :
      ( ~ r2_hidden(F_116,'#skF_3')
      | ~ r2_hidden(k4_tarski('#skF_6',F_116),'#skF_5')
      | ~ m1_subset_1(F_116,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_738,c_42])).

tff(c_811,plain,(
    ! [B_303] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_303,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_303,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_303))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_807,c_795])).

tff(c_938,plain,(
    ! [B_326] :
      ( ~ r2_hidden('#skF_1'('#skF_6',B_326,'#skF_5'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_6',B_326,'#skF_5'),'#skF_4')
      | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5',B_326)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_811])).

tff(c_946,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4')
    | ~ r2_hidden('#skF_6',k10_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_938])).

tff(c_952,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6','#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_785,c_946])).

tff(c_955,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_911,c_952])).

tff(c_959,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_747,c_955])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.52  
% 3.12/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.52  %$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.12/1.52  
% 3.12/1.52  %Foreground sorts:
% 3.12/1.52  
% 3.12/1.52  
% 3.12/1.52  %Background operators:
% 3.12/1.52  
% 3.12/1.52  
% 3.12/1.52  %Foreground operators:
% 3.12/1.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.12/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.12/1.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.12/1.52  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.12/1.52  tff('#skF_7', type, '#skF_7': $i).
% 3.12/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.12/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.12/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.12/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.12/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.12/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.12/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.12/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.52  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.12/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.12/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.12/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.12/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.12/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.12/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.12/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.12/1.52  
% 3.36/1.55  tff(f_103, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k8_relset_1(A, C, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(E, F), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_relset_1)).
% 3.36/1.55  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.36/1.55  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.36/1.55  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.36/1.55  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.36/1.55  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 3.36/1.55  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 3.36/1.55  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t202_relat_1)).
% 3.36/1.55  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.36/1.55  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.36/1.55  tff(c_743, plain, (![C_272, B_273, A_274]: (v5_relat_1(C_272, B_273) | ~m1_subset_1(C_272, k1_zfmisc_1(k2_zfmisc_1(A_274, B_273))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.36/1.55  tff(c_747, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_743])).
% 3.36/1.55  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.36/1.55  tff(c_55, plain, (![B_121, A_122]: (v1_relat_1(B_121) | ~m1_subset_1(B_121, k1_zfmisc_1(A_122)) | ~v1_relat_1(A_122))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.36/1.55  tff(c_58, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_55])).
% 3.36/1.55  tff(c_61, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_58])).
% 3.36/1.55  tff(c_780, plain, (![A_296, B_297, C_298, D_299]: (k8_relset_1(A_296, B_297, C_298, D_299)=k10_relat_1(C_298, D_299) | ~m1_subset_1(C_298, k1_zfmisc_1(k2_zfmisc_1(A_296, B_297))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.36/1.55  tff(c_783, plain, (![D_299]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_299)=k10_relat_1('#skF_5', D_299))), inference(resolution, [status(thm)], [c_30, c_780])).
% 3.36/1.55  tff(c_67, plain, (![C_123, B_124, A_125]: (v5_relat_1(C_123, B_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_125, B_124))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.36/1.55  tff(c_71, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_67])).
% 3.36/1.55  tff(c_566, plain, (![A_245, B_246, C_247, D_248]: (k8_relset_1(A_245, B_246, C_247, D_248)=k10_relat_1(C_247, D_248) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.36/1.55  tff(c_569, plain, (![D_248]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_248)=k10_relat_1('#skF_5', D_248))), inference(resolution, [status(thm)], [c_30, c_566])).
% 3.36/1.55  tff(c_351, plain, (![A_195, B_196, C_197, D_198]: (k8_relset_1(A_195, B_196, C_197, D_198)=k10_relat_1(C_197, D_198) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.36/1.55  tff(c_354, plain, (![D_198]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_198)=k10_relat_1('#skF_5', D_198))), inference(resolution, [status(thm)], [c_30, c_351])).
% 3.36/1.55  tff(c_52, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | m1_subset_1('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.36/1.55  tff(c_77, plain, (m1_subset_1('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 3.36/1.55  tff(c_44, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | r2_hidden('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.36/1.55  tff(c_62, plain, (r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 3.36/1.55  tff(c_48, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')) | r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.36/1.55  tff(c_79, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(splitLeft, [status(thm)], [c_48])).
% 3.36/1.55  tff(c_136, plain, (![A_145, B_146, C_147, D_148]: (k8_relset_1(A_145, B_146, C_147, D_148)=k10_relat_1(C_147, D_148) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.36/1.55  tff(c_139, plain, (![D_148]: (k8_relset_1('#skF_2', '#skF_4', '#skF_5', D_148)=k10_relat_1('#skF_5', D_148))), inference(resolution, [status(thm)], [c_30, c_136])).
% 3.36/1.55  tff(c_38, plain, (![F_116]: (~r2_hidden(F_116, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_116), '#skF_5') | ~m1_subset_1(F_116, '#skF_4') | ~r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.36/1.55  tff(c_243, plain, (![F_116]: (~r2_hidden(F_116, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_116), '#skF_5') | ~m1_subset_1(F_116, '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_38])).
% 3.36/1.55  tff(c_244, plain, (~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_243])).
% 3.36/1.55  tff(c_18, plain, (![B_19, C_20, A_18]: (r2_hidden(B_19, k2_relat_1(C_20)) | ~r2_hidden(k4_tarski(A_18, B_19), C_20) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.36/1.55  tff(c_82, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_79, c_18])).
% 3.36/1.55  tff(c_88, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_82])).
% 3.36/1.55  tff(c_245, plain, (![A_173, C_174, B_175, D_176]: (r2_hidden(A_173, k10_relat_1(C_174, B_175)) | ~r2_hidden(D_176, B_175) | ~r2_hidden(k4_tarski(A_173, D_176), C_174) | ~r2_hidden(D_176, k2_relat_1(C_174)) | ~v1_relat_1(C_174))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.36/1.55  tff(c_273, plain, (![A_177, C_178]: (r2_hidden(A_177, k10_relat_1(C_178, '#skF_3')) | ~r2_hidden(k4_tarski(A_177, '#skF_7'), C_178) | ~r2_hidden('#skF_7', k2_relat_1(C_178)) | ~v1_relat_1(C_178))), inference(resolution, [status(thm)], [c_62, c_245])).
% 3.36/1.55  tff(c_276, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~r2_hidden('#skF_7', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_79, c_273])).
% 3.36/1.55  tff(c_279, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_88, c_276])).
% 3.36/1.55  tff(c_281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_244, c_279])).
% 3.36/1.55  tff(c_304, plain, (![F_179]: (~r2_hidden(F_179, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_179), '#skF_5') | ~m1_subset_1(F_179, '#skF_4'))), inference(splitRight, [status(thm)], [c_243])).
% 3.36/1.55  tff(c_311, plain, (~r2_hidden('#skF_7', '#skF_3') | ~m1_subset_1('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_79, c_304])).
% 3.36/1.55  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_77, c_62, c_311])).
% 3.36/1.55  tff(c_319, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_48])).
% 3.36/1.55  tff(c_356, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_354, c_319])).
% 3.36/1.55  tff(c_342, plain, (![A_192, B_193, C_194]: (r2_hidden('#skF_1'(A_192, B_193, C_194), k2_relat_1(C_194)) | ~r2_hidden(A_192, k10_relat_1(C_194, B_193)) | ~v1_relat_1(C_194))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.36/1.55  tff(c_16, plain, (![C_17, A_14, B_15]: (r2_hidden(C_17, A_14) | ~r2_hidden(C_17, k2_relat_1(B_15)) | ~v5_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.36/1.55  tff(c_448, plain, (![A_213, B_214, C_215, A_216]: (r2_hidden('#skF_1'(A_213, B_214, C_215), A_216) | ~v5_relat_1(C_215, A_216) | ~r2_hidden(A_213, k10_relat_1(C_215, B_214)) | ~v1_relat_1(C_215))), inference(resolution, [status(thm)], [c_342, c_16])).
% 3.36/1.55  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.36/1.55  tff(c_466, plain, (![A_217, B_218, C_219, A_220]: (m1_subset_1('#skF_1'(A_217, B_218, C_219), A_220) | ~v5_relat_1(C_219, A_220) | ~r2_hidden(A_217, k10_relat_1(C_219, B_218)) | ~v1_relat_1(C_219))), inference(resolution, [status(thm)], [c_448, c_2])).
% 3.36/1.55  tff(c_474, plain, (![A_220]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_220) | ~v5_relat_1('#skF_5', A_220) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_356, c_466])).
% 3.36/1.55  tff(c_482, plain, (![A_220]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_220) | ~v5_relat_1('#skF_5', A_220))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_474])).
% 3.36/1.55  tff(c_10, plain, (![A_8, B_9, C_10]: (r2_hidden('#skF_1'(A_8, B_9, C_10), B_9) | ~r2_hidden(A_8, k10_relat_1(C_10, B_9)) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.36/1.55  tff(c_12, plain, (![A_8, B_9, C_10]: (r2_hidden(k4_tarski(A_8, '#skF_1'(A_8, B_9, C_10)), C_10) | ~r2_hidden(A_8, k10_relat_1(C_10, B_9)) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.36/1.55  tff(c_320, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_48])).
% 3.36/1.55  tff(c_46, plain, (![F_116]: (~r2_hidden(F_116, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_116), '#skF_5') | ~m1_subset_1(F_116, '#skF_4') | r2_hidden(k4_tarski('#skF_6', '#skF_7'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.36/1.55  tff(c_419, plain, (![F_206]: (~r2_hidden(F_206, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_206), '#skF_5') | ~m1_subset_1(F_206, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_320, c_46])).
% 3.36/1.55  tff(c_423, plain, (![B_9]: (~r2_hidden('#skF_1'('#skF_6', B_9, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_9, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_9)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_419])).
% 3.36/1.55  tff(c_509, plain, (![B_225]: (~r2_hidden('#skF_1'('#skF_6', B_225, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_225, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_225)))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_423])).
% 3.36/1.55  tff(c_517, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_509])).
% 3.36/1.55  tff(c_523, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_356, c_517])).
% 3.36/1.55  tff(c_526, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_482, c_523])).
% 3.36/1.55  tff(c_530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_526])).
% 3.36/1.55  tff(c_531, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_52])).
% 3.36/1.55  tff(c_599, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_569, c_531])).
% 3.36/1.55  tff(c_556, plain, (![A_241, B_242, C_243]: (r2_hidden('#skF_1'(A_241, B_242, C_243), k2_relat_1(C_243)) | ~r2_hidden(A_241, k10_relat_1(C_243, B_242)) | ~v1_relat_1(C_243))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.36/1.55  tff(c_663, plain, (![A_262, B_263, C_264, A_265]: (r2_hidden('#skF_1'(A_262, B_263, C_264), A_265) | ~v5_relat_1(C_264, A_265) | ~r2_hidden(A_262, k10_relat_1(C_264, B_263)) | ~v1_relat_1(C_264))), inference(resolution, [status(thm)], [c_556, c_16])).
% 3.36/1.55  tff(c_681, plain, (![A_266, B_267, C_268, A_269]: (m1_subset_1('#skF_1'(A_266, B_267, C_268), A_269) | ~v5_relat_1(C_268, A_269) | ~r2_hidden(A_266, k10_relat_1(C_268, B_267)) | ~v1_relat_1(C_268))), inference(resolution, [status(thm)], [c_663, c_2])).
% 3.36/1.55  tff(c_686, plain, (![A_269]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_269) | ~v5_relat_1('#skF_5', A_269) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_599, c_681])).
% 3.36/1.55  tff(c_714, plain, (![A_271]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_271) | ~v5_relat_1('#skF_5', A_271))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_686])).
% 3.36/1.55  tff(c_570, plain, (![A_249, B_250, C_251]: (r2_hidden(k4_tarski(A_249, '#skF_1'(A_249, B_250, C_251)), C_251) | ~r2_hidden(A_249, k10_relat_1(C_251, B_250)) | ~v1_relat_1(C_251))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.36/1.55  tff(c_532, plain, (~m1_subset_1('#skF_7', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 3.36/1.55  tff(c_50, plain, (![F_116]: (~r2_hidden(F_116, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_116), '#skF_5') | ~m1_subset_1(F_116, '#skF_4') | m1_subset_1('#skF_7', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.36/1.55  tff(c_564, plain, (![F_116]: (~r2_hidden(F_116, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_116), '#skF_5') | ~m1_subset_1(F_116, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_532, c_50])).
% 3.36/1.55  tff(c_574, plain, (![B_250]: (~r2_hidden('#skF_1'('#skF_6', B_250, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_250, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_250)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_570, c_564])).
% 3.36/1.55  tff(c_699, plain, (![B_270]: (~r2_hidden('#skF_1'('#skF_6', B_270, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_270, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_270)))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_574])).
% 3.36/1.55  tff(c_707, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_699])).
% 3.36/1.55  tff(c_713, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_599, c_707])).
% 3.36/1.55  tff(c_717, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_714, c_713])).
% 3.36/1.55  tff(c_736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_717])).
% 3.36/1.55  tff(c_737, plain, (r2_hidden('#skF_6', k8_relset_1('#skF_2', '#skF_4', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_44])).
% 3.36/1.55  tff(c_785, plain, (r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_783, c_737])).
% 3.36/1.55  tff(c_767, plain, (![A_290, B_291, C_292]: (r2_hidden('#skF_1'(A_290, B_291, C_292), k2_relat_1(C_292)) | ~r2_hidden(A_290, k10_relat_1(C_292, B_291)) | ~v1_relat_1(C_292))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.36/1.55  tff(c_877, plain, (![A_314, B_315, C_316, A_317]: (r2_hidden('#skF_1'(A_314, B_315, C_316), A_317) | ~v5_relat_1(C_316, A_317) | ~r2_hidden(A_314, k10_relat_1(C_316, B_315)) | ~v1_relat_1(C_316))), inference(resolution, [status(thm)], [c_767, c_16])).
% 3.36/1.55  tff(c_895, plain, (![A_318, B_319, C_320, A_321]: (m1_subset_1('#skF_1'(A_318, B_319, C_320), A_321) | ~v5_relat_1(C_320, A_321) | ~r2_hidden(A_318, k10_relat_1(C_320, B_319)) | ~v1_relat_1(C_320))), inference(resolution, [status(thm)], [c_877, c_2])).
% 3.36/1.55  tff(c_903, plain, (![A_321]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_321) | ~v5_relat_1('#skF_5', A_321) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_785, c_895])).
% 3.36/1.55  tff(c_911, plain, (![A_321]: (m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), A_321) | ~v5_relat_1('#skF_5', A_321))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_903])).
% 3.36/1.55  tff(c_807, plain, (![A_302, B_303, C_304]: (r2_hidden(k4_tarski(A_302, '#skF_1'(A_302, B_303, C_304)), C_304) | ~r2_hidden(A_302, k10_relat_1(C_304, B_303)) | ~v1_relat_1(C_304))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.36/1.55  tff(c_738, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 3.36/1.55  tff(c_42, plain, (![F_116]: (~r2_hidden(F_116, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_116), '#skF_5') | ~m1_subset_1(F_116, '#skF_4') | r2_hidden('#skF_7', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.36/1.55  tff(c_795, plain, (![F_116]: (~r2_hidden(F_116, '#skF_3') | ~r2_hidden(k4_tarski('#skF_6', F_116), '#skF_5') | ~m1_subset_1(F_116, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_738, c_42])).
% 3.36/1.55  tff(c_811, plain, (![B_303]: (~r2_hidden('#skF_1'('#skF_6', B_303, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_303, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_303)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_807, c_795])).
% 3.36/1.55  tff(c_938, plain, (![B_326]: (~r2_hidden('#skF_1'('#skF_6', B_326, '#skF_5'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_6', B_326, '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', B_326)))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_811])).
% 3.36/1.55  tff(c_946, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4') | ~r2_hidden('#skF_6', k10_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_938])).
% 3.36/1.55  tff(c_952, plain, (~m1_subset_1('#skF_1'('#skF_6', '#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_785, c_946])).
% 3.36/1.55  tff(c_955, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_911, c_952])).
% 3.36/1.55  tff(c_959, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_747, c_955])).
% 3.36/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.55  
% 3.36/1.55  Inference rules
% 3.36/1.55  ----------------------
% 3.36/1.55  #Ref     : 0
% 3.36/1.55  #Sup     : 176
% 3.36/1.55  #Fact    : 0
% 3.36/1.55  #Define  : 0
% 3.36/1.55  #Split   : 6
% 3.36/1.55  #Chain   : 0
% 3.36/1.55  #Close   : 0
% 3.36/1.55  
% 3.36/1.55  Ordering : KBO
% 3.36/1.55  
% 3.36/1.55  Simplification rules
% 3.36/1.55  ----------------------
% 3.36/1.55  #Subsume      : 10
% 3.36/1.55  #Demod        : 63
% 3.36/1.55  #Tautology    : 23
% 3.36/1.55  #SimpNegUnit  : 4
% 3.36/1.55  #BackRed      : 6
% 3.36/1.55  
% 3.36/1.55  #Partial instantiations: 0
% 3.36/1.55  #Strategies tried      : 1
% 3.36/1.55  
% 3.36/1.55  Timing (in seconds)
% 3.36/1.55  ----------------------
% 3.36/1.55  Preprocessing        : 0.33
% 3.36/1.55  Parsing              : 0.17
% 3.36/1.55  CNF conversion       : 0.03
% 3.36/1.55  Main loop            : 0.40
% 3.36/1.55  Inferencing          : 0.16
% 3.36/1.55  Reduction            : 0.11
% 3.36/1.55  Demodulation         : 0.08
% 3.36/1.55  BG Simplification    : 0.02
% 3.36/1.55  Subsumption          : 0.07
% 3.36/1.55  Abstraction          : 0.02
% 3.36/1.55  MUC search           : 0.00
% 3.36/1.55  Cooper               : 0.00
% 3.36/1.55  Total                : 0.77
% 3.36/1.55  Index Insertion      : 0.00
% 3.36/1.55  Index Deletion       : 0.00
% 3.36/1.55  Index Matching       : 0.00
% 3.36/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
