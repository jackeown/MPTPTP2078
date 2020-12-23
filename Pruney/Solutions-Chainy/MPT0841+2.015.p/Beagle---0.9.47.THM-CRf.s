%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:34 EST 2020

% Result     : Theorem 5.93s
% Output     : CNFRefutation 5.93s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 292 expanded)
%              Number of leaves         :   33 ( 111 expanded)
%              Depth                    :    8
%              Number of atoms          :  221 ( 840 expanded)
%              Number of equality atoms :   10 (  25 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_106,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_32,plain,(
    ! [A_56,B_57] : v1_relat_1(k2_zfmisc_1(A_56,B_57)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_71,plain,(
    ! [B_161,A_162] :
      ( v1_relat_1(B_161)
      | ~ m1_subset_1(B_161,k1_zfmisc_1(A_162))
      | ~ v1_relat_1(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_74,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_46,c_71])).

tff(c_77,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_74])).

tff(c_3251,plain,(
    ! [A_696,B_697,C_698,D_699] :
      ( k7_relset_1(A_696,B_697,C_698,D_699) = k9_relat_1(C_698,D_699)
      | ~ m1_subset_1(C_698,k1_zfmisc_1(k2_zfmisc_1(A_696,B_697))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3254,plain,(
    ! [D_699] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_699) = k9_relat_1('#skF_9',D_699) ),
    inference(resolution,[status(thm)],[c_46,c_3251])).

tff(c_1952,plain,(
    ! [A_484,B_485,C_486,D_487] :
      ( k7_relset_1(A_484,B_485,C_486,D_487) = k9_relat_1(C_486,D_487)
      | ~ m1_subset_1(C_486,k1_zfmisc_1(k2_zfmisc_1(A_484,B_485))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1955,plain,(
    ! [D_487] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_487) = k9_relat_1('#skF_9',D_487) ),
    inference(resolution,[status(thm)],[c_46,c_1952])).

tff(c_430,plain,(
    ! [A_251,B_252,C_253,D_254] :
      ( k7_relset_1(A_251,B_252,C_253,D_254) = k9_relat_1(C_253,D_254)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_433,plain,(
    ! [D_254] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_254) = k9_relat_1('#skF_9',D_254) ),
    inference(resolution,[status(thm)],[c_46,c_430])).

tff(c_68,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_78,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_60,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_81,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_64,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_91,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_207,plain,(
    ! [A_203,B_204,C_205,D_206] :
      ( k7_relset_1(A_203,B_204,C_205,D_206) = k9_relat_1(C_205,D_206)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_214,plain,(
    ! [D_206] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_206) = k9_relat_1('#skF_9',D_206) ),
    inference(resolution,[status(thm)],[c_46,c_207])).

tff(c_54,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_156,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8')
      | ~ r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_296,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_156,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_54])).

tff(c_297,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_268,plain,(
    ! [D_221,A_222,B_223,E_224] :
      ( r2_hidden(D_221,k9_relat_1(A_222,B_223))
      | ~ r2_hidden(E_224,B_223)
      | ~ r2_hidden(k4_tarski(E_224,D_221),A_222)
      | ~ v1_relat_1(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_298,plain,(
    ! [D_225,A_226] :
      ( r2_hidden(D_225,k9_relat_1(A_226,'#skF_7'))
      | ~ r2_hidden(k4_tarski('#skF_11',D_225),A_226)
      | ~ v1_relat_1(A_226) ) ),
    inference(resolution,[status(thm)],[c_81,c_268])).

tff(c_308,plain,
    ( r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_91,c_298])).

tff(c_315,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_308])).

tff(c_317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_297,c_315])).

tff(c_356,plain,(
    ! [F_231] :
      ( ~ r2_hidden(F_231,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_231,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_231,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_367,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_91,c_356])).

tff(c_377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_81,c_367])).

tff(c_378,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_436,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_378])).

tff(c_36,plain,(
    ! [A_58,B_59,C_60] :
      ( r2_hidden('#skF_5'(A_58,B_59,C_60),B_59)
      | ~ r2_hidden(A_58,k9_relat_1(C_60,B_59))
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_529,plain,(
    ! [A_277,B_278,C_279] :
      ( r2_hidden(k4_tarski('#skF_5'(A_277,B_278,C_279),A_277),C_279)
      | ~ r2_hidden(A_277,k9_relat_1(C_279,B_278))
      | ~ v1_relat_1(C_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_379,plain,(
    ~ r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_62,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_156,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8')
      | r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_428,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_156,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_379,c_62])).

tff(c_535,plain,(
    ! [B_278] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_278,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_278,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_278))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_529,c_428])).

tff(c_608,plain,(
    ! [B_290] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_290,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_290,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_290)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_535])).

tff(c_612,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_608])).

tff(c_615,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_436,c_612])).

tff(c_8,plain,(
    ! [C_8,A_5,B_6] :
      ( r2_hidden(C_8,A_5)
      | ~ r2_hidden(C_8,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1133,plain,(
    ! [A_376,B_377,C_378,A_379] :
      ( r2_hidden(k4_tarski('#skF_5'(A_376,B_377,C_378),A_376),A_379)
      | ~ m1_subset_1(C_378,k1_zfmisc_1(A_379))
      | ~ r2_hidden(A_376,k9_relat_1(C_378,B_377))
      | ~ v1_relat_1(C_378) ) ),
    inference(resolution,[status(thm)],[c_529,c_8])).

tff(c_6,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r2_hidden(A_1,C_3)
      | ~ r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1749,plain,(
    ! [C_456,B_457,C_453,A_455,D_454] :
      ( r2_hidden('#skF_5'(A_455,B_457,C_453),C_456)
      | ~ m1_subset_1(C_453,k1_zfmisc_1(k2_zfmisc_1(C_456,D_454)))
      | ~ r2_hidden(A_455,k9_relat_1(C_453,B_457))
      | ~ v1_relat_1(C_453) ) ),
    inference(resolution,[status(thm)],[c_1133,c_6])).

tff(c_1793,plain,(
    ! [A_455,B_457] :
      ( r2_hidden('#skF_5'(A_455,B_457,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_455,k9_relat_1('#skF_9',B_457))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_46,c_1749])).

tff(c_1811,plain,(
    ! [A_458,B_459] :
      ( r2_hidden('#skF_5'(A_458,B_459,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_458,k9_relat_1('#skF_9',B_459)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_1793])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1822,plain,(
    ! [A_460,B_461] :
      ( m1_subset_1('#skF_5'(A_460,B_461,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_460,k9_relat_1('#skF_9',B_461)) ) ),
    inference(resolution,[status(thm)],[c_1811,c_10])).

tff(c_1877,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_436,c_1822])).

tff(c_1900,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_615,c_1877])).

tff(c_1901,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1958,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1955,c_1901])).

tff(c_1998,plain,(
    ! [A_498,B_499,C_500] :
      ( r2_hidden(k4_tarski('#skF_5'(A_498,B_499,C_500),A_498),C_500)
      | ~ r2_hidden(A_498,k9_relat_1(C_500,B_499))
      | ~ v1_relat_1(C_500) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1902,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_156,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1981,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_156,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1902,c_58])).

tff(c_2004,plain,(
    ! [B_499] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_499,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_499,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_499))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1998,c_1981])).

tff(c_2222,plain,(
    ! [B_538] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_538,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_538,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_538)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_2004])).

tff(c_2230,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_2222])).

tff(c_2236,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_1958,c_2230])).

tff(c_2502,plain,(
    ! [A_581,B_582,C_583,A_584] :
      ( r2_hidden(k4_tarski('#skF_5'(A_581,B_582,C_583),A_581),A_584)
      | ~ m1_subset_1(C_583,k1_zfmisc_1(A_584))
      | ~ r2_hidden(A_581,k9_relat_1(C_583,B_582))
      | ~ v1_relat_1(C_583) ) ),
    inference(resolution,[status(thm)],[c_1998,c_8])).

tff(c_3052,plain,(
    ! [C_659,A_661,D_658,B_657,C_660] :
      ( r2_hidden('#skF_5'(A_661,B_657,C_659),C_660)
      | ~ m1_subset_1(C_659,k1_zfmisc_1(k2_zfmisc_1(C_660,D_658)))
      | ~ r2_hidden(A_661,k9_relat_1(C_659,B_657))
      | ~ v1_relat_1(C_659) ) ),
    inference(resolution,[status(thm)],[c_2502,c_6])).

tff(c_3090,plain,(
    ! [A_661,B_657] :
      ( r2_hidden('#skF_5'(A_661,B_657,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_661,k9_relat_1('#skF_9',B_657))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_46,c_3052])).

tff(c_3106,plain,(
    ! [A_662,B_663] :
      ( r2_hidden('#skF_5'(A_662,B_663,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_662,k9_relat_1('#skF_9',B_663)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_3090])).

tff(c_3117,plain,(
    ! [A_664,B_665] :
      ( m1_subset_1('#skF_5'(A_664,B_665,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_664,k9_relat_1('#skF_9',B_665)) ) ),
    inference(resolution,[status(thm)],[c_3106,c_10])).

tff(c_3172,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_1958,c_3117])).

tff(c_3195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2236,c_3172])).

tff(c_3196,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_3257,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3254,c_3196])).

tff(c_3295,plain,(
    ! [A_709,B_710,C_711] :
      ( r2_hidden(k4_tarski('#skF_5'(A_709,B_710,C_711),A_709),C_711)
      | ~ r2_hidden(A_709,k9_relat_1(C_711,B_710))
      | ~ v1_relat_1(C_711) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3197,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_66,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_156,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3211,plain,(
    ! [F_156] :
      ( ~ r2_hidden(F_156,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_156,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_156,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3197,c_66])).

tff(c_3304,plain,(
    ! [B_710] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_710,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_710,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_710))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_3295,c_3211])).

tff(c_3494,plain,(
    ! [B_740] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_740,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_740,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_740)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_3304])).

tff(c_3498,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_3494])).

tff(c_3501,plain,(
    ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_3257,c_3498])).

tff(c_3785,plain,(
    ! [A_792,B_793,C_794,A_795] :
      ( r2_hidden(k4_tarski('#skF_5'(A_792,B_793,C_794),A_792),A_795)
      | ~ m1_subset_1(C_794,k1_zfmisc_1(A_795))
      | ~ r2_hidden(A_792,k9_relat_1(C_794,B_793))
      | ~ v1_relat_1(C_794) ) ),
    inference(resolution,[status(thm)],[c_3295,c_8])).

tff(c_4224,plain,(
    ! [C_855,D_854,C_853,B_856,A_852] :
      ( r2_hidden('#skF_5'(A_852,B_856,C_853),C_855)
      | ~ m1_subset_1(C_853,k1_zfmisc_1(k2_zfmisc_1(C_855,D_854)))
      | ~ r2_hidden(A_852,k9_relat_1(C_853,B_856))
      | ~ v1_relat_1(C_853) ) ),
    inference(resolution,[status(thm)],[c_3785,c_6])).

tff(c_4259,plain,(
    ! [A_852,B_856] :
      ( r2_hidden('#skF_5'(A_852,B_856,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_852,k9_relat_1('#skF_9',B_856))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_46,c_4224])).

tff(c_4274,plain,(
    ! [A_857,B_858] :
      ( r2_hidden('#skF_5'(A_857,B_858,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_857,k9_relat_1('#skF_9',B_858)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_4259])).

tff(c_4312,plain,(
    ! [A_863,B_864] :
      ( m1_subset_1('#skF_5'(A_863,B_864,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_863,k9_relat_1('#skF_9',B_864)) ) ),
    inference(resolution,[status(thm)],[c_4274,c_10])).

tff(c_4363,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_3257,c_4312])).

tff(c_4385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3501,c_4363])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:17:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.93/2.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.14  
% 5.93/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.14  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 5.93/2.14  
% 5.93/2.14  %Foreground sorts:
% 5.93/2.14  
% 5.93/2.14  
% 5.93/2.14  %Background operators:
% 5.93/2.14  
% 5.93/2.14  
% 5.93/2.14  %Foreground operators:
% 5.93/2.14  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.93/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.93/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.93/2.14  tff('#skF_11', type, '#skF_11': $i).
% 5.93/2.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.93/2.14  tff('#skF_7', type, '#skF_7': $i).
% 5.93/2.14  tff('#skF_10', type, '#skF_10': $i).
% 5.93/2.14  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.93/2.14  tff('#skF_6', type, '#skF_6': $i).
% 5.93/2.14  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.93/2.14  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.93/2.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.93/2.14  tff('#skF_9', type, '#skF_9': $i).
% 5.93/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.93/2.14  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 5.93/2.14  tff('#skF_8', type, '#skF_8': $i).
% 5.93/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.93/2.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.93/2.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.93/2.14  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.93/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.93/2.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.93/2.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.93/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.93/2.14  
% 5.93/2.16  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.93/2.16  tff(f_106, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 5.93/2.16  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.93/2.16  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.93/2.16  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 5.93/2.16  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 5.93/2.16  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 5.93/2.16  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.93/2.16  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 5.93/2.16  tff(c_32, plain, (![A_56, B_57]: (v1_relat_1(k2_zfmisc_1(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.93/2.16  tff(c_46, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.93/2.16  tff(c_71, plain, (![B_161, A_162]: (v1_relat_1(B_161) | ~m1_subset_1(B_161, k1_zfmisc_1(A_162)) | ~v1_relat_1(A_162))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.93/2.16  tff(c_74, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_6'))), inference(resolution, [status(thm)], [c_46, c_71])).
% 5.93/2.16  tff(c_77, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_74])).
% 5.93/2.16  tff(c_3251, plain, (![A_696, B_697, C_698, D_699]: (k7_relset_1(A_696, B_697, C_698, D_699)=k9_relat_1(C_698, D_699) | ~m1_subset_1(C_698, k1_zfmisc_1(k2_zfmisc_1(A_696, B_697))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.93/2.16  tff(c_3254, plain, (![D_699]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_699)=k9_relat_1('#skF_9', D_699))), inference(resolution, [status(thm)], [c_46, c_3251])).
% 5.93/2.16  tff(c_1952, plain, (![A_484, B_485, C_486, D_487]: (k7_relset_1(A_484, B_485, C_486, D_487)=k9_relat_1(C_486, D_487) | ~m1_subset_1(C_486, k1_zfmisc_1(k2_zfmisc_1(A_484, B_485))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.93/2.16  tff(c_1955, plain, (![D_487]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_487)=k9_relat_1('#skF_9', D_487))), inference(resolution, [status(thm)], [c_46, c_1952])).
% 5.93/2.16  tff(c_430, plain, (![A_251, B_252, C_253, D_254]: (k7_relset_1(A_251, B_252, C_253, D_254)=k9_relat_1(C_253, D_254) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.93/2.16  tff(c_433, plain, (![D_254]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_254)=k9_relat_1('#skF_9', D_254))), inference(resolution, [status(thm)], [c_46, c_430])).
% 5.93/2.16  tff(c_68, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.93/2.16  tff(c_78, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_68])).
% 5.93/2.16  tff(c_60, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | r2_hidden('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.93/2.16  tff(c_81, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_60])).
% 5.93/2.16  tff(c_64, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.93/2.16  tff(c_91, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_64])).
% 5.93/2.16  tff(c_207, plain, (![A_203, B_204, C_205, D_206]: (k7_relset_1(A_203, B_204, C_205, D_206)=k9_relat_1(C_205, D_206) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.93/2.16  tff(c_214, plain, (![D_206]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_206)=k9_relat_1('#skF_9', D_206))), inference(resolution, [status(thm)], [c_46, c_207])).
% 5.93/2.16  tff(c_54, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski(F_156, '#skF_10'), '#skF_9') | ~m1_subset_1(F_156, '#skF_8') | ~r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.93/2.16  tff(c_296, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski(F_156, '#skF_10'), '#skF_9') | ~m1_subset_1(F_156, '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_54])).
% 5.93/2.16  tff(c_297, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(splitLeft, [status(thm)], [c_296])).
% 5.93/2.16  tff(c_268, plain, (![D_221, A_222, B_223, E_224]: (r2_hidden(D_221, k9_relat_1(A_222, B_223)) | ~r2_hidden(E_224, B_223) | ~r2_hidden(k4_tarski(E_224, D_221), A_222) | ~v1_relat_1(A_222))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.93/2.16  tff(c_298, plain, (![D_225, A_226]: (r2_hidden(D_225, k9_relat_1(A_226, '#skF_7')) | ~r2_hidden(k4_tarski('#skF_11', D_225), A_226) | ~v1_relat_1(A_226))), inference(resolution, [status(thm)], [c_81, c_268])).
% 5.93/2.16  tff(c_308, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_91, c_298])).
% 5.93/2.16  tff(c_315, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_308])).
% 5.93/2.16  tff(c_317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_297, c_315])).
% 5.93/2.16  tff(c_356, plain, (![F_231]: (~r2_hidden(F_231, '#skF_7') | ~r2_hidden(k4_tarski(F_231, '#skF_10'), '#skF_9') | ~m1_subset_1(F_231, '#skF_8'))), inference(splitRight, [status(thm)], [c_296])).
% 5.93/2.16  tff(c_367, plain, (~r2_hidden('#skF_11', '#skF_7') | ~m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_91, c_356])).
% 5.93/2.16  tff(c_377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_81, c_367])).
% 5.93/2.16  tff(c_378, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_64])).
% 5.93/2.16  tff(c_436, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_433, c_378])).
% 5.93/2.16  tff(c_36, plain, (![A_58, B_59, C_60]: (r2_hidden('#skF_5'(A_58, B_59, C_60), B_59) | ~r2_hidden(A_58, k9_relat_1(C_60, B_59)) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.93/2.16  tff(c_529, plain, (![A_277, B_278, C_279]: (r2_hidden(k4_tarski('#skF_5'(A_277, B_278, C_279), A_277), C_279) | ~r2_hidden(A_277, k9_relat_1(C_279, B_278)) | ~v1_relat_1(C_279))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.93/2.16  tff(c_379, plain, (~r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_64])).
% 5.93/2.16  tff(c_62, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski(F_156, '#skF_10'), '#skF_9') | ~m1_subset_1(F_156, '#skF_8') | r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.93/2.16  tff(c_428, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski(F_156, '#skF_10'), '#skF_9') | ~m1_subset_1(F_156, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_379, c_62])).
% 5.93/2.16  tff(c_535, plain, (![B_278]: (~r2_hidden('#skF_5'('#skF_10', B_278, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_278, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_278)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_529, c_428])).
% 5.93/2.16  tff(c_608, plain, (![B_290]: (~r2_hidden('#skF_5'('#skF_10', B_290, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_290, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_290)))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_535])).
% 5.93/2.16  tff(c_612, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_36, c_608])).
% 5.93/2.16  tff(c_615, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_436, c_612])).
% 5.93/2.16  tff(c_8, plain, (![C_8, A_5, B_6]: (r2_hidden(C_8, A_5) | ~r2_hidden(C_8, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.93/2.16  tff(c_1133, plain, (![A_376, B_377, C_378, A_379]: (r2_hidden(k4_tarski('#skF_5'(A_376, B_377, C_378), A_376), A_379) | ~m1_subset_1(C_378, k1_zfmisc_1(A_379)) | ~r2_hidden(A_376, k9_relat_1(C_378, B_377)) | ~v1_relat_1(C_378))), inference(resolution, [status(thm)], [c_529, c_8])).
% 5.93/2.16  tff(c_6, plain, (![A_1, C_3, B_2, D_4]: (r2_hidden(A_1, C_3) | ~r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.93/2.16  tff(c_1749, plain, (![C_456, B_457, C_453, A_455, D_454]: (r2_hidden('#skF_5'(A_455, B_457, C_453), C_456) | ~m1_subset_1(C_453, k1_zfmisc_1(k2_zfmisc_1(C_456, D_454))) | ~r2_hidden(A_455, k9_relat_1(C_453, B_457)) | ~v1_relat_1(C_453))), inference(resolution, [status(thm)], [c_1133, c_6])).
% 5.93/2.16  tff(c_1793, plain, (![A_455, B_457]: (r2_hidden('#skF_5'(A_455, B_457, '#skF_9'), '#skF_8') | ~r2_hidden(A_455, k9_relat_1('#skF_9', B_457)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_46, c_1749])).
% 5.93/2.16  tff(c_1811, plain, (![A_458, B_459]: (r2_hidden('#skF_5'(A_458, B_459, '#skF_9'), '#skF_8') | ~r2_hidden(A_458, k9_relat_1('#skF_9', B_459)))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_1793])).
% 5.93/2.16  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.93/2.16  tff(c_1822, plain, (![A_460, B_461]: (m1_subset_1('#skF_5'(A_460, B_461, '#skF_9'), '#skF_8') | ~r2_hidden(A_460, k9_relat_1('#skF_9', B_461)))), inference(resolution, [status(thm)], [c_1811, c_10])).
% 5.93/2.16  tff(c_1877, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_436, c_1822])).
% 5.93/2.16  tff(c_1900, plain, $false, inference(negUnitSimplification, [status(thm)], [c_615, c_1877])).
% 5.93/2.16  tff(c_1901, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_60])).
% 5.93/2.16  tff(c_1958, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1955, c_1901])).
% 5.93/2.16  tff(c_1998, plain, (![A_498, B_499, C_500]: (r2_hidden(k4_tarski('#skF_5'(A_498, B_499, C_500), A_498), C_500) | ~r2_hidden(A_498, k9_relat_1(C_500, B_499)) | ~v1_relat_1(C_500))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.93/2.16  tff(c_1902, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_60])).
% 5.93/2.16  tff(c_58, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski(F_156, '#skF_10'), '#skF_9') | ~m1_subset_1(F_156, '#skF_8') | r2_hidden('#skF_11', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.93/2.16  tff(c_1981, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski(F_156, '#skF_10'), '#skF_9') | ~m1_subset_1(F_156, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1902, c_58])).
% 5.93/2.16  tff(c_2004, plain, (![B_499]: (~r2_hidden('#skF_5'('#skF_10', B_499, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_499, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_499)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1998, c_1981])).
% 5.93/2.16  tff(c_2222, plain, (![B_538]: (~r2_hidden('#skF_5'('#skF_10', B_538, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_538, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_538)))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_2004])).
% 5.93/2.16  tff(c_2230, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_36, c_2222])).
% 5.93/2.16  tff(c_2236, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_1958, c_2230])).
% 5.93/2.16  tff(c_2502, plain, (![A_581, B_582, C_583, A_584]: (r2_hidden(k4_tarski('#skF_5'(A_581, B_582, C_583), A_581), A_584) | ~m1_subset_1(C_583, k1_zfmisc_1(A_584)) | ~r2_hidden(A_581, k9_relat_1(C_583, B_582)) | ~v1_relat_1(C_583))), inference(resolution, [status(thm)], [c_1998, c_8])).
% 5.93/2.16  tff(c_3052, plain, (![C_659, A_661, D_658, B_657, C_660]: (r2_hidden('#skF_5'(A_661, B_657, C_659), C_660) | ~m1_subset_1(C_659, k1_zfmisc_1(k2_zfmisc_1(C_660, D_658))) | ~r2_hidden(A_661, k9_relat_1(C_659, B_657)) | ~v1_relat_1(C_659))), inference(resolution, [status(thm)], [c_2502, c_6])).
% 5.93/2.16  tff(c_3090, plain, (![A_661, B_657]: (r2_hidden('#skF_5'(A_661, B_657, '#skF_9'), '#skF_8') | ~r2_hidden(A_661, k9_relat_1('#skF_9', B_657)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_46, c_3052])).
% 5.93/2.16  tff(c_3106, plain, (![A_662, B_663]: (r2_hidden('#skF_5'(A_662, B_663, '#skF_9'), '#skF_8') | ~r2_hidden(A_662, k9_relat_1('#skF_9', B_663)))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_3090])).
% 5.93/2.16  tff(c_3117, plain, (![A_664, B_665]: (m1_subset_1('#skF_5'(A_664, B_665, '#skF_9'), '#skF_8') | ~r2_hidden(A_664, k9_relat_1('#skF_9', B_665)))), inference(resolution, [status(thm)], [c_3106, c_10])).
% 5.93/2.16  tff(c_3172, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_1958, c_3117])).
% 5.93/2.16  tff(c_3195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2236, c_3172])).
% 5.93/2.16  tff(c_3196, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_68])).
% 5.93/2.16  tff(c_3257, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_3254, c_3196])).
% 5.93/2.16  tff(c_3295, plain, (![A_709, B_710, C_711]: (r2_hidden(k4_tarski('#skF_5'(A_709, B_710, C_711), A_709), C_711) | ~r2_hidden(A_709, k9_relat_1(C_711, B_710)) | ~v1_relat_1(C_711))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.93/2.16  tff(c_3197, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_68])).
% 5.93/2.16  tff(c_66, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski(F_156, '#skF_10'), '#skF_9') | ~m1_subset_1(F_156, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.93/2.16  tff(c_3211, plain, (![F_156]: (~r2_hidden(F_156, '#skF_7') | ~r2_hidden(k4_tarski(F_156, '#skF_10'), '#skF_9') | ~m1_subset_1(F_156, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_3197, c_66])).
% 5.93/2.16  tff(c_3304, plain, (![B_710]: (~r2_hidden('#skF_5'('#skF_10', B_710, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_710, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_710)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_3295, c_3211])).
% 5.93/2.16  tff(c_3494, plain, (![B_740]: (~r2_hidden('#skF_5'('#skF_10', B_740, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_740, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_740)))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_3304])).
% 5.93/2.16  tff(c_3498, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_36, c_3494])).
% 5.93/2.16  tff(c_3501, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_3257, c_3498])).
% 5.93/2.16  tff(c_3785, plain, (![A_792, B_793, C_794, A_795]: (r2_hidden(k4_tarski('#skF_5'(A_792, B_793, C_794), A_792), A_795) | ~m1_subset_1(C_794, k1_zfmisc_1(A_795)) | ~r2_hidden(A_792, k9_relat_1(C_794, B_793)) | ~v1_relat_1(C_794))), inference(resolution, [status(thm)], [c_3295, c_8])).
% 5.93/2.16  tff(c_4224, plain, (![C_855, D_854, C_853, B_856, A_852]: (r2_hidden('#skF_5'(A_852, B_856, C_853), C_855) | ~m1_subset_1(C_853, k1_zfmisc_1(k2_zfmisc_1(C_855, D_854))) | ~r2_hidden(A_852, k9_relat_1(C_853, B_856)) | ~v1_relat_1(C_853))), inference(resolution, [status(thm)], [c_3785, c_6])).
% 5.93/2.16  tff(c_4259, plain, (![A_852, B_856]: (r2_hidden('#skF_5'(A_852, B_856, '#skF_9'), '#skF_8') | ~r2_hidden(A_852, k9_relat_1('#skF_9', B_856)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_46, c_4224])).
% 5.93/2.16  tff(c_4274, plain, (![A_857, B_858]: (r2_hidden('#skF_5'(A_857, B_858, '#skF_9'), '#skF_8') | ~r2_hidden(A_857, k9_relat_1('#skF_9', B_858)))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_4259])).
% 5.93/2.16  tff(c_4312, plain, (![A_863, B_864]: (m1_subset_1('#skF_5'(A_863, B_864, '#skF_9'), '#skF_8') | ~r2_hidden(A_863, k9_relat_1('#skF_9', B_864)))), inference(resolution, [status(thm)], [c_4274, c_10])).
% 5.93/2.16  tff(c_4363, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_3257, c_4312])).
% 5.93/2.16  tff(c_4385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3501, c_4363])).
% 5.93/2.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.93/2.16  
% 5.93/2.16  Inference rules
% 5.93/2.16  ----------------------
% 5.93/2.16  #Ref     : 0
% 5.93/2.16  #Sup     : 929
% 5.93/2.16  #Fact    : 0
% 5.93/2.16  #Define  : 0
% 5.93/2.16  #Split   : 9
% 5.93/2.16  #Chain   : 0
% 5.93/2.16  #Close   : 0
% 5.93/2.16  
% 5.93/2.16  Ordering : KBO
% 5.93/2.16  
% 5.93/2.16  Simplification rules
% 5.93/2.16  ----------------------
% 5.93/2.16  #Subsume      : 27
% 5.93/2.16  #Demod        : 137
% 5.93/2.16  #Tautology    : 38
% 5.93/2.16  #SimpNegUnit  : 7
% 5.93/2.16  #BackRed      : 9
% 5.93/2.16  
% 5.93/2.16  #Partial instantiations: 0
% 5.93/2.16  #Strategies tried      : 1
% 5.93/2.16  
% 5.93/2.16  Timing (in seconds)
% 5.93/2.16  ----------------------
% 5.93/2.16  Preprocessing        : 0.35
% 5.93/2.16  Parsing              : 0.17
% 5.93/2.16  CNF conversion       : 0.04
% 5.93/2.16  Main loop            : 1.05
% 5.93/2.16  Inferencing          : 0.42
% 5.93/2.16  Reduction            : 0.27
% 5.93/2.16  Demodulation         : 0.19
% 5.93/2.16  BG Simplification    : 0.05
% 5.93/2.16  Subsumption          : 0.21
% 5.93/2.16  Abstraction          : 0.06
% 5.93/2.16  MUC search           : 0.00
% 5.93/2.16  Cooper               : 0.00
% 5.93/2.16  Total                : 1.44
% 5.93/2.16  Index Insertion      : 0.00
% 5.93/2.16  Index Deletion       : 0.00
% 5.93/2.17  Index Matching       : 0.00
% 5.93/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
