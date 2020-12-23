%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:08 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 266 expanded)
%              Number of leaves         :   37 ( 109 expanded)
%              Depth                    :    9
%              Number of atoms          :  136 ( 587 expanded)
%              Number of equality atoms :   19 (  82 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_90,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_924,plain,(
    ! [A_276,B_277,C_278] :
      ( k2_relset_1(A_276,B_277,C_278) = k2_relat_1(C_278)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_928,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_924])).

tff(c_275,plain,(
    ! [A_145,B_146,C_147] :
      ( k2_relset_1(A_145,B_146,C_147) = k2_relat_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_279,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_275])).

tff(c_52,plain,
    ( m1_subset_1('#skF_10','#skF_7')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_62,plain,(
    r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_281,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_62])).

tff(c_18,plain,(
    ! [A_25,B_26] : v1_relat_1(k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_55,plain,(
    ! [B_89,A_90] :
      ( v1_relat_1(B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_90))
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_58,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_36,c_55])).

tff(c_61,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_58])).

tff(c_777,plain,(
    ! [A_248,B_249,C_250,D_251] :
      ( k7_relset_1(A_248,B_249,C_250,D_251) = k9_relat_1(C_250,D_251)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_784,plain,(
    ! [D_251] : k7_relset_1('#skF_7','#skF_6','#skF_8',D_251) = k9_relat_1('#skF_8',D_251) ),
    inference(resolution,[status(thm)],[c_36,c_777])).

tff(c_795,plain,(
    ! [A_256,B_257,C_258] :
      ( k7_relset_1(A_256,B_257,C_258,A_256) = k2_relset_1(A_256,B_257,C_258)
      | ~ m1_subset_1(C_258,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_800,plain,(
    k7_relset_1('#skF_7','#skF_6','#skF_8','#skF_7') = k2_relset_1('#skF_7','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_795])).

tff(c_803,plain,(
    k9_relat_1('#skF_8','#skF_7') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_784,c_279,c_800])).

tff(c_742,plain,(
    ! [A_235,B_236,C_237] :
      ( r2_hidden('#skF_5'(A_235,B_236,C_237),B_236)
      | ~ r2_hidden(A_235,k9_relat_1(C_237,B_236))
      | ~ v1_relat_1(C_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_746,plain,(
    ! [A_235,B_236,C_237] :
      ( m1_subset_1('#skF_5'(A_235,B_236,C_237),B_236)
      | ~ r2_hidden(A_235,k9_relat_1(C_237,B_236))
      | ~ v1_relat_1(C_237) ) ),
    inference(resolution,[status(thm)],[c_742,c_2])).

tff(c_807,plain,(
    ! [A_235] :
      ( m1_subset_1('#skF_5'(A_235,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_235,k2_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_803,c_746])).

tff(c_813,plain,(
    ! [A_262] :
      ( m1_subset_1('#skF_5'(A_262,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_262,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_807])).

tff(c_836,plain,(
    m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_281,c_813])).

tff(c_849,plain,(
    ! [A_266,B_267,C_268] :
      ( r2_hidden(k4_tarski('#skF_5'(A_266,B_267,C_268),A_266),C_268)
      | ~ r2_hidden(A_266,k9_relat_1(C_268,B_267))
      | ~ v1_relat_1(C_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_48,plain,
    ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_286,plain,
    ( ~ r2_hidden('#skF_9',k2_relat_1('#skF_8'))
    | r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_279,c_48])).

tff(c_287,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_286])).

tff(c_347,plain,(
    ! [A_163,B_164,C_165,D_166] :
      ( k7_relset_1(A_163,B_164,C_165,D_166) = k9_relat_1(C_165,D_166)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_354,plain,(
    ! [D_166] : k7_relset_1('#skF_7','#skF_6','#skF_8',D_166) = k9_relat_1('#skF_8',D_166) ),
    inference(resolution,[status(thm)],[c_36,c_347])).

tff(c_370,plain,(
    ! [A_174,B_175,C_176] :
      ( k7_relset_1(A_174,B_175,C_176,A_174) = k2_relset_1(A_174,B_175,C_176)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_375,plain,(
    k7_relset_1('#skF_7','#skF_6','#skF_8','#skF_7') = k2_relset_1('#skF_7','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_370])).

tff(c_378,plain,(
    k9_relat_1('#skF_8','#skF_7') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_279,c_375])).

tff(c_317,plain,(
    ! [A_153,B_154,C_155] :
      ( r2_hidden('#skF_5'(A_153,B_154,C_155),B_154)
      | ~ r2_hidden(A_153,k9_relat_1(C_155,B_154))
      | ~ v1_relat_1(C_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_321,plain,(
    ! [A_153,B_154,C_155] :
      ( m1_subset_1('#skF_5'(A_153,B_154,C_155),B_154)
      | ~ r2_hidden(A_153,k9_relat_1(C_155,B_154))
      | ~ v1_relat_1(C_155) ) ),
    inference(resolution,[status(thm)],[c_317,c_2])).

tff(c_381,plain,(
    ! [A_153] :
      ( m1_subset_1('#skF_5'(A_153,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_153,k2_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_321])).

tff(c_387,plain,(
    ! [A_177] :
      ( m1_subset_1('#skF_5'(A_177,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_177,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_381])).

tff(c_406,plain,(
    m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_281,c_387])).

tff(c_407,plain,(
    ! [A_178,B_179,C_180] :
      ( r2_hidden(k4_tarski('#skF_5'(A_178,B_179,C_180),A_178),C_180)
      | ~ r2_hidden(A_178,k9_relat_1(C_180,B_179))
      | ~ v1_relat_1(C_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    ! [E_84] :
      ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
      | ~ r2_hidden(k4_tarski(E_84,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_84,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_302,plain,(
    ! [E_84] :
      ( ~ r2_hidden(k4_tarski(E_84,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_84,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_418,plain,(
    ! [B_179] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_179,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_179))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_407,c_302])).

tff(c_458,plain,(
    ! [B_184] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_184,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_184)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_418])).

tff(c_461,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_458])).

tff(c_464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_406,c_461])).

tff(c_465,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_8,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k2_relat_1(A_6))
      | ~ r2_hidden(k4_tarski(D_24,C_21),A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_468,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_465,c_8])).

tff(c_475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_468])).

tff(c_477,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_286])).

tff(c_42,plain,(
    ! [E_84] :
      ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(E_84,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_84,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_710,plain,(
    ! [E_84] :
      ( ~ r2_hidden(k4_tarski(E_84,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_84,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_279,c_42])).

tff(c_860,plain,(
    ! [B_267] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_267,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_267))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_849,c_710])).

tff(c_900,plain,(
    ! [B_272] :
      ( ~ m1_subset_1('#skF_5'('#skF_11',B_272,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_11',k9_relat_1('#skF_8',B_272)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_860])).

tff(c_903,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_11','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_803,c_900])).

tff(c_906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_836,c_903])).

tff(c_908,plain,(
    ~ r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,
    ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_910,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_908,c_50])).

tff(c_917,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_910,c_8])).

tff(c_935,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_917,c_928,c_48])).

tff(c_929,plain,(
    ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_928,c_908])).

tff(c_941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_929])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:09:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.47  
% 3.08/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.47  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 3.08/1.47  
% 3.08/1.47  %Foreground sorts:
% 3.08/1.47  
% 3.08/1.47  
% 3.08/1.47  %Background operators:
% 3.08/1.47  
% 3.08/1.47  
% 3.08/1.47  %Foreground operators:
% 3.08/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.08/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.08/1.47  tff('#skF_11', type, '#skF_11': $i).
% 3.08/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.08/1.47  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.08/1.47  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.08/1.47  tff('#skF_7', type, '#skF_7': $i).
% 3.08/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.08/1.47  tff('#skF_10', type, '#skF_10': $i).
% 3.08/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.08/1.47  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.08/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.08/1.47  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.08/1.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.08/1.47  tff('#skF_9', type, '#skF_9': $i).
% 3.08/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.08/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.47  tff('#skF_8', type, '#skF_8': $i).
% 3.08/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.08/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.08/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.08/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.08/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.08/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.08/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.47  
% 3.08/1.49  tff(f_90, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (![D]: (r2_hidden(D, k2_relset_1(B, A, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(E, D), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relset_1)).
% 3.08/1.49  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.08/1.49  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.08/1.49  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.08/1.49  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.08/1.49  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.08/1.49  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 3.08/1.49  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.08/1.49  tff(f_44, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 3.08/1.49  tff(c_36, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.08/1.49  tff(c_924, plain, (![A_276, B_277, C_278]: (k2_relset_1(A_276, B_277, C_278)=k2_relat_1(C_278) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.08/1.49  tff(c_928, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_924])).
% 3.08/1.49  tff(c_275, plain, (![A_145, B_146, C_147]: (k2_relset_1(A_145, B_146, C_147)=k2_relat_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.08/1.49  tff(c_279, plain, (k2_relset_1('#skF_7', '#skF_6', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_36, c_275])).
% 3.08/1.49  tff(c_52, plain, (m1_subset_1('#skF_10', '#skF_7') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.08/1.49  tff(c_62, plain, (r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_52])).
% 3.08/1.49  tff(c_281, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_62])).
% 3.08/1.49  tff(c_18, plain, (![A_25, B_26]: (v1_relat_1(k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.08/1.49  tff(c_55, plain, (![B_89, A_90]: (v1_relat_1(B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(A_90)) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.08/1.49  tff(c_58, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_55])).
% 3.08/1.49  tff(c_61, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_58])).
% 3.08/1.49  tff(c_777, plain, (![A_248, B_249, C_250, D_251]: (k7_relset_1(A_248, B_249, C_250, D_251)=k9_relat_1(C_250, D_251) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.08/1.49  tff(c_784, plain, (![D_251]: (k7_relset_1('#skF_7', '#skF_6', '#skF_8', D_251)=k9_relat_1('#skF_8', D_251))), inference(resolution, [status(thm)], [c_36, c_777])).
% 3.08/1.49  tff(c_795, plain, (![A_256, B_257, C_258]: (k7_relset_1(A_256, B_257, C_258, A_256)=k2_relset_1(A_256, B_257, C_258) | ~m1_subset_1(C_258, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.08/1.49  tff(c_800, plain, (k7_relset_1('#skF_7', '#skF_6', '#skF_8', '#skF_7')=k2_relset_1('#skF_7', '#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_36, c_795])).
% 3.08/1.49  tff(c_803, plain, (k9_relat_1('#skF_8', '#skF_7')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_784, c_279, c_800])).
% 3.08/1.49  tff(c_742, plain, (![A_235, B_236, C_237]: (r2_hidden('#skF_5'(A_235, B_236, C_237), B_236) | ~r2_hidden(A_235, k9_relat_1(C_237, B_236)) | ~v1_relat_1(C_237))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.08/1.49  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.08/1.49  tff(c_746, plain, (![A_235, B_236, C_237]: (m1_subset_1('#skF_5'(A_235, B_236, C_237), B_236) | ~r2_hidden(A_235, k9_relat_1(C_237, B_236)) | ~v1_relat_1(C_237))), inference(resolution, [status(thm)], [c_742, c_2])).
% 3.08/1.49  tff(c_807, plain, (![A_235]: (m1_subset_1('#skF_5'(A_235, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_235, k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_803, c_746])).
% 3.08/1.49  tff(c_813, plain, (![A_262]: (m1_subset_1('#skF_5'(A_262, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_262, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_807])).
% 3.08/1.49  tff(c_836, plain, (m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_281, c_813])).
% 3.08/1.49  tff(c_849, plain, (![A_266, B_267, C_268]: (r2_hidden(k4_tarski('#skF_5'(A_266, B_267, C_268), A_266), C_268) | ~r2_hidden(A_266, k9_relat_1(C_268, B_267)) | ~v1_relat_1(C_268))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.08/1.49  tff(c_48, plain, (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.08/1.49  tff(c_286, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_8')) | r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_279, c_48])).
% 3.08/1.49  tff(c_287, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_286])).
% 3.08/1.49  tff(c_347, plain, (![A_163, B_164, C_165, D_166]: (k7_relset_1(A_163, B_164, C_165, D_166)=k9_relat_1(C_165, D_166) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.08/1.49  tff(c_354, plain, (![D_166]: (k7_relset_1('#skF_7', '#skF_6', '#skF_8', D_166)=k9_relat_1('#skF_8', D_166))), inference(resolution, [status(thm)], [c_36, c_347])).
% 3.08/1.49  tff(c_370, plain, (![A_174, B_175, C_176]: (k7_relset_1(A_174, B_175, C_176, A_174)=k2_relset_1(A_174, B_175, C_176) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.08/1.49  tff(c_375, plain, (k7_relset_1('#skF_7', '#skF_6', '#skF_8', '#skF_7')=k2_relset_1('#skF_7', '#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_36, c_370])).
% 3.08/1.49  tff(c_378, plain, (k9_relat_1('#skF_8', '#skF_7')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_354, c_279, c_375])).
% 3.08/1.49  tff(c_317, plain, (![A_153, B_154, C_155]: (r2_hidden('#skF_5'(A_153, B_154, C_155), B_154) | ~r2_hidden(A_153, k9_relat_1(C_155, B_154)) | ~v1_relat_1(C_155))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.08/1.49  tff(c_321, plain, (![A_153, B_154, C_155]: (m1_subset_1('#skF_5'(A_153, B_154, C_155), B_154) | ~r2_hidden(A_153, k9_relat_1(C_155, B_154)) | ~v1_relat_1(C_155))), inference(resolution, [status(thm)], [c_317, c_2])).
% 3.08/1.49  tff(c_381, plain, (![A_153]: (m1_subset_1('#skF_5'(A_153, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_153, k2_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_378, c_321])).
% 3.08/1.49  tff(c_387, plain, (![A_177]: (m1_subset_1('#skF_5'(A_177, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_177, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_381])).
% 3.08/1.49  tff(c_406, plain, (m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_281, c_387])).
% 3.08/1.49  tff(c_407, plain, (![A_178, B_179, C_180]: (r2_hidden(k4_tarski('#skF_5'(A_178, B_179, C_180), A_178), C_180) | ~r2_hidden(A_178, k9_relat_1(C_180, B_179)) | ~v1_relat_1(C_180))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.08/1.49  tff(c_44, plain, (![E_84]: (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | ~r2_hidden(k4_tarski(E_84, '#skF_11'), '#skF_8') | ~m1_subset_1(E_84, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.08/1.49  tff(c_302, plain, (![E_84]: (~r2_hidden(k4_tarski(E_84, '#skF_11'), '#skF_8') | ~m1_subset_1(E_84, '#skF_7'))), inference(splitLeft, [status(thm)], [c_44])).
% 3.08/1.49  tff(c_418, plain, (![B_179]: (~m1_subset_1('#skF_5'('#skF_11', B_179, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_179)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_407, c_302])).
% 3.08/1.49  tff(c_458, plain, (![B_184]: (~m1_subset_1('#skF_5'('#skF_11', B_184, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_184)))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_418])).
% 3.08/1.49  tff(c_461, plain, (~m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_378, c_458])).
% 3.08/1.49  tff(c_464, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_406, c_461])).
% 3.08/1.49  tff(c_465, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_44])).
% 3.08/1.49  tff(c_8, plain, (![C_21, A_6, D_24]: (r2_hidden(C_21, k2_relat_1(A_6)) | ~r2_hidden(k4_tarski(D_24, C_21), A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.08/1.49  tff(c_468, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_465, c_8])).
% 3.08/1.49  tff(c_475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_287, c_468])).
% 3.08/1.49  tff(c_477, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_286])).
% 3.08/1.49  tff(c_42, plain, (![E_84]: (~r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_6', '#skF_8')) | ~r2_hidden(k4_tarski(E_84, '#skF_11'), '#skF_8') | ~m1_subset_1(E_84, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.08/1.49  tff(c_710, plain, (![E_84]: (~r2_hidden(k4_tarski(E_84, '#skF_11'), '#skF_8') | ~m1_subset_1(E_84, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_477, c_279, c_42])).
% 3.08/1.49  tff(c_860, plain, (![B_267]: (~m1_subset_1('#skF_5'('#skF_11', B_267, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_267)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_849, c_710])).
% 3.08/1.49  tff(c_900, plain, (![B_272]: (~m1_subset_1('#skF_5'('#skF_11', B_272, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k9_relat_1('#skF_8', B_272)))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_860])).
% 3.08/1.49  tff(c_903, plain, (~m1_subset_1('#skF_5'('#skF_11', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_803, c_900])).
% 3.08/1.49  tff(c_906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_281, c_836, c_903])).
% 3.08/1.49  tff(c_908, plain, (~r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_52])).
% 3.08/1.49  tff(c_50, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8') | r2_hidden('#skF_11', k2_relset_1('#skF_7', '#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.08/1.49  tff(c_910, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_908, c_50])).
% 3.08/1.49  tff(c_917, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_910, c_8])).
% 3.08/1.49  tff(c_935, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_928, c_917, c_928, c_48])).
% 3.08/1.49  tff(c_929, plain, (~r2_hidden('#skF_11', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_928, c_908])).
% 3.08/1.49  tff(c_941, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_935, c_929])).
% 3.08/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.49  
% 3.08/1.49  Inference rules
% 3.08/1.49  ----------------------
% 3.08/1.49  #Ref     : 0
% 3.08/1.49  #Sup     : 183
% 3.08/1.49  #Fact    : 0
% 3.08/1.49  #Define  : 0
% 3.08/1.49  #Split   : 5
% 3.08/1.49  #Chain   : 0
% 3.08/1.49  #Close   : 0
% 3.08/1.49  
% 3.08/1.49  Ordering : KBO
% 3.08/1.49  
% 3.08/1.49  Simplification rules
% 3.08/1.49  ----------------------
% 3.08/1.49  #Subsume      : 4
% 3.08/1.49  #Demod        : 59
% 3.08/1.49  #Tautology    : 46
% 3.08/1.49  #SimpNegUnit  : 3
% 3.08/1.49  #BackRed      : 5
% 3.08/1.49  
% 3.08/1.49  #Partial instantiations: 0
% 3.08/1.49  #Strategies tried      : 1
% 3.08/1.49  
% 3.08/1.49  Timing (in seconds)
% 3.08/1.49  ----------------------
% 3.08/1.50  Preprocessing        : 0.33
% 3.08/1.50  Parsing              : 0.17
% 3.08/1.50  CNF conversion       : 0.03
% 3.08/1.50  Main loop            : 0.40
% 3.08/1.50  Inferencing          : 0.15
% 3.08/1.50  Reduction            : 0.12
% 3.08/1.50  Demodulation         : 0.08
% 3.08/1.50  BG Simplification    : 0.02
% 3.08/1.50  Subsumption          : 0.07
% 3.08/1.50  Abstraction          : 0.03
% 3.08/1.50  MUC search           : 0.00
% 3.08/1.50  Cooper               : 0.00
% 3.08/1.50  Total                : 0.77
% 3.08/1.50  Index Insertion      : 0.00
% 3.08/1.50  Index Deletion       : 0.00
% 3.08/1.50  Index Matching       : 0.00
% 3.08/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
