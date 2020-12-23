%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:33 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 446 expanded)
%              Number of leaves         :   38 ( 168 expanded)
%              Depth                    :   11
%              Number of atoms          :  254 (1246 expanded)
%              Number of equality atoms :   17 (  51 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_114,negated_conjecture,(
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

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( v1_relat_1(C)
         => ( C = k7_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(D,B)
                  & r2_hidden(k4_tarski(D,E),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_24,plain,(
    ! [A_25,B_26] : v1_relat_1(k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_48,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_73,plain,(
    ! [B_138,A_139] :
      ( v1_relat_1(B_138)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_139))
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_76,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_6')) ),
    inference(resolution,[status(thm)],[c_48,c_73])).

tff(c_79,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_76])).

tff(c_784,plain,(
    ! [A_324,B_325,C_326,D_327] :
      ( k7_relset_1(A_324,B_325,C_326,D_327) = k9_relat_1(C_326,D_327)
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(A_324,B_325))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_787,plain,(
    ! [D_327] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_327) = k9_relat_1('#skF_9',D_327) ),
    inference(resolution,[status(thm)],[c_48,c_784])).

tff(c_588,plain,(
    ! [A_272,B_273,C_274,D_275] :
      ( k7_relset_1(A_272,B_273,C_274,D_275) = k9_relat_1(C_274,D_275)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_591,plain,(
    ! [D_275] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_275) = k9_relat_1('#skF_9',D_275) ),
    inference(resolution,[status(thm)],[c_48,c_588])).

tff(c_377,plain,(
    ! [A_223,B_224,C_225,D_226] :
      ( k7_relset_1(A_223,B_224,C_225,D_226) = k9_relat_1(C_225,D_226)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_380,plain,(
    ! [D_226] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_226) = k9_relat_1('#skF_9',D_226) ),
    inference(resolution,[status(thm)],[c_48,c_377])).

tff(c_70,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | m1_subset_1('#skF_11','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_80,plain,(
    m1_subset_1('#skF_11','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_62,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | r2_hidden('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_102,plain,(
    r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_66,plain,
    ( r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7'))
    | r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_107,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_151,plain,(
    ! [A_163,B_164,C_165,D_166] :
      ( k7_relset_1(A_163,B_164,C_165,D_166) = k9_relat_1(C_165,D_166)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_154,plain,(
    ! [D_166] : k7_relset_1('#skF_8','#skF_6','#skF_9',D_166) = k9_relat_1('#skF_9',D_166) ),
    inference(resolution,[status(thm)],[c_48,c_151])).

tff(c_56,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_133,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8')
      | ~ r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_247,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_133,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_56])).

tff(c_248,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_112,plain,(
    ! [A_148,C_149,B_150] :
      ( r2_hidden(A_148,k1_relat_1(C_149))
      | ~ r2_hidden(k4_tarski(A_148,B_150),C_149)
      | ~ v1_relat_1(C_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_115,plain,
    ( r2_hidden('#skF_11',k1_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_107,c_112])).

tff(c_118,plain,(
    r2_hidden('#skF_11',k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_115])).

tff(c_272,plain,(
    ! [A_197,C_198,B_199,D_200] :
      ( r2_hidden(A_197,k9_relat_1(C_198,B_199))
      | ~ r2_hidden(D_200,B_199)
      | ~ r2_hidden(k4_tarski(D_200,A_197),C_198)
      | ~ r2_hidden(D_200,k1_relat_1(C_198))
      | ~ v1_relat_1(C_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_300,plain,(
    ! [A_201,C_202] :
      ( r2_hidden(A_201,k9_relat_1(C_202,'#skF_7'))
      | ~ r2_hidden(k4_tarski('#skF_11',A_201),C_202)
      | ~ r2_hidden('#skF_11',k1_relat_1(C_202))
      | ~ v1_relat_1(C_202) ) ),
    inference(resolution,[status(thm)],[c_102,c_272])).

tff(c_303,plain,
    ( r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ r2_hidden('#skF_11',k1_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_107,c_300])).

tff(c_306,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_118,c_303])).

tff(c_308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_248,c_306])).

tff(c_337,plain,(
    ! [F_207] :
      ( ~ r2_hidden(F_207,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_207,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_207,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_344,plain,
    ( ~ r2_hidden('#skF_11','#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(resolution,[status(thm)],[c_107,c_337])).

tff(c_351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_102,c_344])).

tff(c_352,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_384,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_352])).

tff(c_30,plain,(
    ! [A_27,B_28,C_29] :
      ( r2_hidden(k4_tarski('#skF_5'(A_27,B_28,C_29),A_27),C_29)
      | ~ r2_hidden(A_27,k9_relat_1(C_29,B_28))
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_81,plain,(
    ! [C_140,A_141,B_142] :
      ( v4_relat_1(C_140,A_141)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_85,plain,(
    v4_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_81])).

tff(c_91,plain,(
    ! [B_146,A_147] :
      ( k7_relat_1(B_146,A_147) = B_146
      | ~ v4_relat_1(B_146,A_147)
      | ~ v1_relat_1(B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_94,plain,
    ( k7_relat_1('#skF_9','#skF_8') = '#skF_9'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_85,c_91])).

tff(c_97,plain,(
    k7_relat_1('#skF_9','#skF_8') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_94])).

tff(c_472,plain,(
    ! [D_241,B_242,E_243,A_244] :
      ( r2_hidden(D_241,B_242)
      | ~ r2_hidden(k4_tarski(D_241,E_243),k7_relat_1(A_244,B_242))
      | ~ v1_relat_1(k7_relat_1(A_244,B_242))
      | ~ v1_relat_1(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_479,plain,(
    ! [D_241,E_243] :
      ( r2_hidden(D_241,'#skF_8')
      | ~ r2_hidden(k4_tarski(D_241,E_243),'#skF_9')
      | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_8'))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_472])).

tff(c_483,plain,(
    ! [D_245,E_246] :
      ( r2_hidden(D_245,'#skF_8')
      | ~ r2_hidden(k4_tarski(D_245,E_246),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_79,c_97,c_479])).

tff(c_487,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_5'(A_27,B_28,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_27,k9_relat_1('#skF_9',B_28))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_30,c_483])).

tff(c_491,plain,(
    ! [A_247,B_248] :
      ( r2_hidden('#skF_5'(A_247,B_248,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_247,k9_relat_1('#skF_9',B_248)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_487])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_496,plain,(
    ! [A_249,B_250] :
      ( m1_subset_1('#skF_5'(A_249,B_250,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_249,k9_relat_1('#skF_9',B_250)) ) ),
    inference(resolution,[status(thm)],[c_491,c_2])).

tff(c_509,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_384,c_496])).

tff(c_28,plain,(
    ! [A_27,B_28,C_29] :
      ( r2_hidden('#skF_5'(A_27,B_28,C_29),B_28)
      | ~ r2_hidden(A_27,k9_relat_1(C_29,B_28))
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_405,plain,(
    ! [A_232,B_233,C_234] :
      ( r2_hidden(k4_tarski('#skF_5'(A_232,B_233,C_234),A_232),C_234)
      | ~ r2_hidden(A_232,k9_relat_1(C_234,B_233))
      | ~ v1_relat_1(C_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_353,plain,(
    ~ r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_64,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_133,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8')
      | r2_hidden(k4_tarski('#skF_11','#skF_10'),'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_381,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_133,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_64])).

tff(c_409,plain,(
    ! [B_233] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_233,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_233,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_233))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_405,c_381])).

tff(c_522,plain,(
    ! [B_255] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_255,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_255,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_255)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_409])).

tff(c_526,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_28,c_522])).

tff(c_530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_384,c_509,c_526])).

tff(c_531,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_593,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_531])).

tff(c_676,plain,(
    ! [D_289,B_290,E_291,A_292] :
      ( r2_hidden(D_289,B_290)
      | ~ r2_hidden(k4_tarski(D_289,E_291),k7_relat_1(A_292,B_290))
      | ~ v1_relat_1(k7_relat_1(A_292,B_290))
      | ~ v1_relat_1(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_683,plain,(
    ! [D_289,E_291] :
      ( r2_hidden(D_289,'#skF_8')
      | ~ r2_hidden(k4_tarski(D_289,E_291),'#skF_9')
      | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_8'))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_676])).

tff(c_687,plain,(
    ! [D_293,E_294] :
      ( r2_hidden(D_293,'#skF_8')
      | ~ r2_hidden(k4_tarski(D_293,E_294),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_79,c_97,c_683])).

tff(c_691,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_5'(A_27,B_28,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_27,k9_relat_1('#skF_9',B_28))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_30,c_687])).

tff(c_704,plain,(
    ! [A_295,B_296] :
      ( r2_hidden('#skF_5'(A_295,B_296,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_295,k9_relat_1('#skF_9',B_296)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_691])).

tff(c_711,plain,(
    ! [A_297,B_298] :
      ( m1_subset_1('#skF_5'(A_297,B_298,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_297,k9_relat_1('#skF_9',B_298)) ) ),
    inference(resolution,[status(thm)],[c_704,c_2])).

tff(c_724,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_593,c_711])).

tff(c_615,plain,(
    ! [A_280,B_281,C_282] :
      ( r2_hidden(k4_tarski('#skF_5'(A_280,B_281,C_282),A_280),C_282)
      | ~ r2_hidden(A_280,k9_relat_1(C_282,B_281))
      | ~ v1_relat_1(C_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_532,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_60,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_133,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8')
      | r2_hidden('#skF_11','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_564,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_133,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_532,c_60])).

tff(c_622,plain,(
    ! [B_281] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_281,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_281,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_281))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_615,c_564])).

tff(c_726,plain,(
    ! [B_299] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_299,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_299,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_299)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_622])).

tff(c_730,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_28,c_726])).

tff(c_734,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_593,c_724,c_730])).

tff(c_735,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_8','#skF_6','#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_789,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_735])).

tff(c_748,plain,(
    ! [C_305,A_306,B_307] :
      ( v4_relat_1(C_305,A_306)
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(A_306,B_307))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_752,plain,(
    v4_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_748])).

tff(c_34,plain,(
    ! [B_34,A_33] :
      ( k7_relat_1(B_34,A_33) = B_34
      | ~ v4_relat_1(B_34,A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_755,plain,
    ( k7_relat_1('#skF_9','#skF_8') = '#skF_9'
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_752,c_34])).

tff(c_758,plain,(
    k7_relat_1('#skF_9','#skF_8') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_755])).

tff(c_875,plain,(
    ! [D_341,B_342,E_343,A_344] :
      ( r2_hidden(D_341,B_342)
      | ~ r2_hidden(k4_tarski(D_341,E_343),k7_relat_1(A_344,B_342))
      | ~ v1_relat_1(k7_relat_1(A_344,B_342))
      | ~ v1_relat_1(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_882,plain,(
    ! [D_341,E_343] :
      ( r2_hidden(D_341,'#skF_8')
      | ~ r2_hidden(k4_tarski(D_341,E_343),'#skF_9')
      | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_8'))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_758,c_875])).

tff(c_897,plain,(
    ! [D_349,E_350] :
      ( r2_hidden(D_349,'#skF_8')
      | ~ r2_hidden(k4_tarski(D_349,E_350),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_79,c_758,c_882])).

tff(c_901,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_5'(A_27,B_28,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_27,k9_relat_1('#skF_9',B_28))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_30,c_897])).

tff(c_905,plain,(
    ! [A_351,B_352] :
      ( r2_hidden('#skF_5'(A_351,B_352,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_351,k9_relat_1('#skF_9',B_352)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_901])).

tff(c_910,plain,(
    ! [A_353,B_354] :
      ( m1_subset_1('#skF_5'(A_353,B_354,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_353,k9_relat_1('#skF_9',B_354)) ) ),
    inference(resolution,[status(thm)],[c_905,c_2])).

tff(c_922,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_789,c_910])).

tff(c_799,plain,(
    ! [A_329,B_330,C_331] :
      ( r2_hidden(k4_tarski('#skF_5'(A_329,B_330,C_331),A_329),C_331)
      | ~ r2_hidden(A_329,k9_relat_1(C_331,B_330))
      | ~ v1_relat_1(C_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_736,plain,(
    ~ m1_subset_1('#skF_11','#skF_8') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_68,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_133,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8')
      | m1_subset_1('#skF_11','#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_777,plain,(
    ! [F_133] :
      ( ~ r2_hidden(F_133,'#skF_7')
      | ~ r2_hidden(k4_tarski(F_133,'#skF_10'),'#skF_9')
      | ~ m1_subset_1(F_133,'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_736,c_68])).

tff(c_803,plain,(
    ! [B_330] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_330,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_330,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_330))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_799,c_777])).

tff(c_927,plain,(
    ! [B_355] :
      ( ~ r2_hidden('#skF_5'('#skF_10',B_355,'#skF_9'),'#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_10',B_355,'#skF_9'),'#skF_8')
      | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9',B_355)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_803])).

tff(c_931,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_10','#skF_7','#skF_9'),'#skF_8')
    | ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_28,c_927])).

tff(c_935,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_789,c_922,c_931])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 20:52:15 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.56  
% 3.62/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.56  %$ v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 3.62/1.56  
% 3.62/1.56  %Foreground sorts:
% 3.62/1.56  
% 3.62/1.56  
% 3.62/1.56  %Background operators:
% 3.62/1.56  
% 3.62/1.56  
% 3.62/1.56  %Foreground operators:
% 3.62/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.62/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.62/1.56  tff('#skF_11', type, '#skF_11': $i).
% 3.62/1.56  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.62/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.62/1.56  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.62/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.62/1.56  tff('#skF_10', type, '#skF_10': $i).
% 3.62/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.62/1.56  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.62/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.62/1.56  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.62/1.56  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.62/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.62/1.56  tff('#skF_9', type, '#skF_9': $i).
% 3.62/1.56  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.62/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.62/1.56  tff('#skF_8', type, '#skF_8': $i).
% 3.62/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.62/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.62/1.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.62/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.62/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.62/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.62/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.62/1.56  
% 3.62/1.59  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.62/1.59  tff(f_114, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 3.62/1.59  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.62/1.59  tff(f_87, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.62/1.59  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 3.62/1.59  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 3.62/1.59  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.62/1.59  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.62/1.59  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_relat_1)).
% 3.62/1.59  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.62/1.59  tff(c_24, plain, (![A_25, B_26]: (v1_relat_1(k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.62/1.59  tff(c_48, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.62/1.59  tff(c_73, plain, (![B_138, A_139]: (v1_relat_1(B_138) | ~m1_subset_1(B_138, k1_zfmisc_1(A_139)) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.62/1.59  tff(c_76, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_6'))), inference(resolution, [status(thm)], [c_48, c_73])).
% 3.62/1.59  tff(c_79, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_76])).
% 3.62/1.59  tff(c_784, plain, (![A_324, B_325, C_326, D_327]: (k7_relset_1(A_324, B_325, C_326, D_327)=k9_relat_1(C_326, D_327) | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(A_324, B_325))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.62/1.59  tff(c_787, plain, (![D_327]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_327)=k9_relat_1('#skF_9', D_327))), inference(resolution, [status(thm)], [c_48, c_784])).
% 3.62/1.59  tff(c_588, plain, (![A_272, B_273, C_274, D_275]: (k7_relset_1(A_272, B_273, C_274, D_275)=k9_relat_1(C_274, D_275) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.62/1.59  tff(c_591, plain, (![D_275]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_275)=k9_relat_1('#skF_9', D_275))), inference(resolution, [status(thm)], [c_48, c_588])).
% 3.62/1.59  tff(c_377, plain, (![A_223, B_224, C_225, D_226]: (k7_relset_1(A_223, B_224, C_225, D_226)=k9_relat_1(C_225, D_226) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.62/1.59  tff(c_380, plain, (![D_226]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_226)=k9_relat_1('#skF_9', D_226))), inference(resolution, [status(thm)], [c_48, c_377])).
% 3.62/1.59  tff(c_70, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | m1_subset_1('#skF_11', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.62/1.59  tff(c_80, plain, (m1_subset_1('#skF_11', '#skF_8')), inference(splitLeft, [status(thm)], [c_70])).
% 3.62/1.59  tff(c_62, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | r2_hidden('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.62/1.59  tff(c_102, plain, (r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_62])).
% 3.62/1.59  tff(c_66, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')) | r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.62/1.59  tff(c_107, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_66])).
% 3.62/1.59  tff(c_151, plain, (![A_163, B_164, C_165, D_166]: (k7_relset_1(A_163, B_164, C_165, D_166)=k9_relat_1(C_165, D_166) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.62/1.59  tff(c_154, plain, (![D_166]: (k7_relset_1('#skF_8', '#skF_6', '#skF_9', D_166)=k9_relat_1('#skF_9', D_166))), inference(resolution, [status(thm)], [c_48, c_151])).
% 3.62/1.59  tff(c_56, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski(F_133, '#skF_10'), '#skF_9') | ~m1_subset_1(F_133, '#skF_8') | ~r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.62/1.59  tff(c_247, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski(F_133, '#skF_10'), '#skF_9') | ~m1_subset_1(F_133, '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_56])).
% 3.62/1.59  tff(c_248, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(splitLeft, [status(thm)], [c_247])).
% 3.62/1.59  tff(c_112, plain, (![A_148, C_149, B_150]: (r2_hidden(A_148, k1_relat_1(C_149)) | ~r2_hidden(k4_tarski(A_148, B_150), C_149) | ~v1_relat_1(C_149))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.62/1.59  tff(c_115, plain, (r2_hidden('#skF_11', k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_107, c_112])).
% 3.62/1.59  tff(c_118, plain, (r2_hidden('#skF_11', k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_115])).
% 3.62/1.59  tff(c_272, plain, (![A_197, C_198, B_199, D_200]: (r2_hidden(A_197, k9_relat_1(C_198, B_199)) | ~r2_hidden(D_200, B_199) | ~r2_hidden(k4_tarski(D_200, A_197), C_198) | ~r2_hidden(D_200, k1_relat_1(C_198)) | ~v1_relat_1(C_198))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.62/1.59  tff(c_300, plain, (![A_201, C_202]: (r2_hidden(A_201, k9_relat_1(C_202, '#skF_7')) | ~r2_hidden(k4_tarski('#skF_11', A_201), C_202) | ~r2_hidden('#skF_11', k1_relat_1(C_202)) | ~v1_relat_1(C_202))), inference(resolution, [status(thm)], [c_102, c_272])).
% 3.62/1.59  tff(c_303, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~r2_hidden('#skF_11', k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_107, c_300])).
% 3.62/1.59  tff(c_306, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_118, c_303])).
% 3.62/1.59  tff(c_308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_248, c_306])).
% 3.62/1.59  tff(c_337, plain, (![F_207]: (~r2_hidden(F_207, '#skF_7') | ~r2_hidden(k4_tarski(F_207, '#skF_10'), '#skF_9') | ~m1_subset_1(F_207, '#skF_8'))), inference(splitRight, [status(thm)], [c_247])).
% 3.62/1.59  tff(c_344, plain, (~r2_hidden('#skF_11', '#skF_7') | ~m1_subset_1('#skF_11', '#skF_8')), inference(resolution, [status(thm)], [c_107, c_337])).
% 3.62/1.59  tff(c_351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_102, c_344])).
% 3.62/1.59  tff(c_352, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_66])).
% 3.62/1.59  tff(c_384, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_380, c_352])).
% 3.62/1.59  tff(c_30, plain, (![A_27, B_28, C_29]: (r2_hidden(k4_tarski('#skF_5'(A_27, B_28, C_29), A_27), C_29) | ~r2_hidden(A_27, k9_relat_1(C_29, B_28)) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.62/1.59  tff(c_81, plain, (![C_140, A_141, B_142]: (v4_relat_1(C_140, A_141) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.62/1.59  tff(c_85, plain, (v4_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_48, c_81])).
% 3.62/1.59  tff(c_91, plain, (![B_146, A_147]: (k7_relat_1(B_146, A_147)=B_146 | ~v4_relat_1(B_146, A_147) | ~v1_relat_1(B_146))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.62/1.59  tff(c_94, plain, (k7_relat_1('#skF_9', '#skF_8')='#skF_9' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_85, c_91])).
% 3.62/1.59  tff(c_97, plain, (k7_relat_1('#skF_9', '#skF_8')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_94])).
% 3.62/1.59  tff(c_472, plain, (![D_241, B_242, E_243, A_244]: (r2_hidden(D_241, B_242) | ~r2_hidden(k4_tarski(D_241, E_243), k7_relat_1(A_244, B_242)) | ~v1_relat_1(k7_relat_1(A_244, B_242)) | ~v1_relat_1(A_244))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.62/1.59  tff(c_479, plain, (![D_241, E_243]: (r2_hidden(D_241, '#skF_8') | ~r2_hidden(k4_tarski(D_241, E_243), '#skF_9') | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_97, c_472])).
% 3.62/1.59  tff(c_483, plain, (![D_245, E_246]: (r2_hidden(D_245, '#skF_8') | ~r2_hidden(k4_tarski(D_245, E_246), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_79, c_97, c_479])).
% 3.62/1.59  tff(c_487, plain, (![A_27, B_28]: (r2_hidden('#skF_5'(A_27, B_28, '#skF_9'), '#skF_8') | ~r2_hidden(A_27, k9_relat_1('#skF_9', B_28)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_30, c_483])).
% 3.62/1.59  tff(c_491, plain, (![A_247, B_248]: (r2_hidden('#skF_5'(A_247, B_248, '#skF_9'), '#skF_8') | ~r2_hidden(A_247, k9_relat_1('#skF_9', B_248)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_487])).
% 3.62/1.59  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.62/1.59  tff(c_496, plain, (![A_249, B_250]: (m1_subset_1('#skF_5'(A_249, B_250, '#skF_9'), '#skF_8') | ~r2_hidden(A_249, k9_relat_1('#skF_9', B_250)))), inference(resolution, [status(thm)], [c_491, c_2])).
% 3.62/1.59  tff(c_509, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_384, c_496])).
% 3.62/1.59  tff(c_28, plain, (![A_27, B_28, C_29]: (r2_hidden('#skF_5'(A_27, B_28, C_29), B_28) | ~r2_hidden(A_27, k9_relat_1(C_29, B_28)) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.62/1.59  tff(c_405, plain, (![A_232, B_233, C_234]: (r2_hidden(k4_tarski('#skF_5'(A_232, B_233, C_234), A_232), C_234) | ~r2_hidden(A_232, k9_relat_1(C_234, B_233)) | ~v1_relat_1(C_234))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.62/1.59  tff(c_353, plain, (~r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_66])).
% 3.62/1.59  tff(c_64, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski(F_133, '#skF_10'), '#skF_9') | ~m1_subset_1(F_133, '#skF_8') | r2_hidden(k4_tarski('#skF_11', '#skF_10'), '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.62/1.59  tff(c_381, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski(F_133, '#skF_10'), '#skF_9') | ~m1_subset_1(F_133, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_353, c_64])).
% 3.62/1.59  tff(c_409, plain, (![B_233]: (~r2_hidden('#skF_5'('#skF_10', B_233, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_233, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_233)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_405, c_381])).
% 3.62/1.59  tff(c_522, plain, (![B_255]: (~r2_hidden('#skF_5'('#skF_10', B_255, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_255, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_255)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_409])).
% 3.62/1.59  tff(c_526, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_28, c_522])).
% 3.62/1.59  tff(c_530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_384, c_509, c_526])).
% 3.62/1.59  tff(c_531, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_62])).
% 3.62/1.59  tff(c_593, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_591, c_531])).
% 3.62/1.59  tff(c_676, plain, (![D_289, B_290, E_291, A_292]: (r2_hidden(D_289, B_290) | ~r2_hidden(k4_tarski(D_289, E_291), k7_relat_1(A_292, B_290)) | ~v1_relat_1(k7_relat_1(A_292, B_290)) | ~v1_relat_1(A_292))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.62/1.59  tff(c_683, plain, (![D_289, E_291]: (r2_hidden(D_289, '#skF_8') | ~r2_hidden(k4_tarski(D_289, E_291), '#skF_9') | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_97, c_676])).
% 3.62/1.59  tff(c_687, plain, (![D_293, E_294]: (r2_hidden(D_293, '#skF_8') | ~r2_hidden(k4_tarski(D_293, E_294), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_79, c_97, c_683])).
% 3.62/1.59  tff(c_691, plain, (![A_27, B_28]: (r2_hidden('#skF_5'(A_27, B_28, '#skF_9'), '#skF_8') | ~r2_hidden(A_27, k9_relat_1('#skF_9', B_28)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_30, c_687])).
% 3.62/1.59  tff(c_704, plain, (![A_295, B_296]: (r2_hidden('#skF_5'(A_295, B_296, '#skF_9'), '#skF_8') | ~r2_hidden(A_295, k9_relat_1('#skF_9', B_296)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_691])).
% 3.62/1.59  tff(c_711, plain, (![A_297, B_298]: (m1_subset_1('#skF_5'(A_297, B_298, '#skF_9'), '#skF_8') | ~r2_hidden(A_297, k9_relat_1('#skF_9', B_298)))), inference(resolution, [status(thm)], [c_704, c_2])).
% 3.62/1.59  tff(c_724, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_593, c_711])).
% 3.62/1.59  tff(c_615, plain, (![A_280, B_281, C_282]: (r2_hidden(k4_tarski('#skF_5'(A_280, B_281, C_282), A_280), C_282) | ~r2_hidden(A_280, k9_relat_1(C_282, B_281)) | ~v1_relat_1(C_282))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.62/1.59  tff(c_532, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitRight, [status(thm)], [c_62])).
% 3.62/1.59  tff(c_60, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski(F_133, '#skF_10'), '#skF_9') | ~m1_subset_1(F_133, '#skF_8') | r2_hidden('#skF_11', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.62/1.59  tff(c_564, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski(F_133, '#skF_10'), '#skF_9') | ~m1_subset_1(F_133, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_532, c_60])).
% 3.62/1.59  tff(c_622, plain, (![B_281]: (~r2_hidden('#skF_5'('#skF_10', B_281, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_281, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_281)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_615, c_564])).
% 3.62/1.59  tff(c_726, plain, (![B_299]: (~r2_hidden('#skF_5'('#skF_10', B_299, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_299, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_299)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_622])).
% 3.62/1.59  tff(c_730, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_28, c_726])).
% 3.62/1.59  tff(c_734, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_593, c_724, c_730])).
% 3.62/1.59  tff(c_735, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_8', '#skF_6', '#skF_9', '#skF_7'))), inference(splitRight, [status(thm)], [c_70])).
% 3.62/1.59  tff(c_789, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_787, c_735])).
% 3.62/1.59  tff(c_748, plain, (![C_305, A_306, B_307]: (v4_relat_1(C_305, A_306) | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(A_306, B_307))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.62/1.59  tff(c_752, plain, (v4_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_48, c_748])).
% 3.62/1.59  tff(c_34, plain, (![B_34, A_33]: (k7_relat_1(B_34, A_33)=B_34 | ~v4_relat_1(B_34, A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.62/1.59  tff(c_755, plain, (k7_relat_1('#skF_9', '#skF_8')='#skF_9' | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_752, c_34])).
% 3.62/1.59  tff(c_758, plain, (k7_relat_1('#skF_9', '#skF_8')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_79, c_755])).
% 3.62/1.59  tff(c_875, plain, (![D_341, B_342, E_343, A_344]: (r2_hidden(D_341, B_342) | ~r2_hidden(k4_tarski(D_341, E_343), k7_relat_1(A_344, B_342)) | ~v1_relat_1(k7_relat_1(A_344, B_342)) | ~v1_relat_1(A_344))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.62/1.59  tff(c_882, plain, (![D_341, E_343]: (r2_hidden(D_341, '#skF_8') | ~r2_hidden(k4_tarski(D_341, E_343), '#skF_9') | ~v1_relat_1(k7_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_758, c_875])).
% 3.62/1.59  tff(c_897, plain, (![D_349, E_350]: (r2_hidden(D_349, '#skF_8') | ~r2_hidden(k4_tarski(D_349, E_350), '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_79, c_758, c_882])).
% 3.62/1.59  tff(c_901, plain, (![A_27, B_28]: (r2_hidden('#skF_5'(A_27, B_28, '#skF_9'), '#skF_8') | ~r2_hidden(A_27, k9_relat_1('#skF_9', B_28)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_30, c_897])).
% 3.62/1.59  tff(c_905, plain, (![A_351, B_352]: (r2_hidden('#skF_5'(A_351, B_352, '#skF_9'), '#skF_8') | ~r2_hidden(A_351, k9_relat_1('#skF_9', B_352)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_901])).
% 3.62/1.59  tff(c_910, plain, (![A_353, B_354]: (m1_subset_1('#skF_5'(A_353, B_354, '#skF_9'), '#skF_8') | ~r2_hidden(A_353, k9_relat_1('#skF_9', B_354)))), inference(resolution, [status(thm)], [c_905, c_2])).
% 3.62/1.59  tff(c_922, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_789, c_910])).
% 3.62/1.59  tff(c_799, plain, (![A_329, B_330, C_331]: (r2_hidden(k4_tarski('#skF_5'(A_329, B_330, C_331), A_329), C_331) | ~r2_hidden(A_329, k9_relat_1(C_331, B_330)) | ~v1_relat_1(C_331))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.62/1.59  tff(c_736, plain, (~m1_subset_1('#skF_11', '#skF_8')), inference(splitRight, [status(thm)], [c_70])).
% 3.62/1.59  tff(c_68, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski(F_133, '#skF_10'), '#skF_9') | ~m1_subset_1(F_133, '#skF_8') | m1_subset_1('#skF_11', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.62/1.59  tff(c_777, plain, (![F_133]: (~r2_hidden(F_133, '#skF_7') | ~r2_hidden(k4_tarski(F_133, '#skF_10'), '#skF_9') | ~m1_subset_1(F_133, '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_736, c_68])).
% 3.62/1.59  tff(c_803, plain, (![B_330]: (~r2_hidden('#skF_5'('#skF_10', B_330, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_330, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_330)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_799, c_777])).
% 3.62/1.59  tff(c_927, plain, (![B_355]: (~r2_hidden('#skF_5'('#skF_10', B_355, '#skF_9'), '#skF_7') | ~m1_subset_1('#skF_5'('#skF_10', B_355, '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', B_355)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_803])).
% 3.62/1.59  tff(c_931, plain, (~m1_subset_1('#skF_5'('#skF_10', '#skF_7', '#skF_9'), '#skF_8') | ~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_7')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_28, c_927])).
% 3.62/1.59  tff(c_935, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_789, c_922, c_931])).
% 3.62/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.59  
% 3.62/1.59  Inference rules
% 3.62/1.59  ----------------------
% 3.62/1.59  #Ref     : 0
% 3.62/1.59  #Sup     : 161
% 3.62/1.59  #Fact    : 0
% 3.62/1.59  #Define  : 0
% 3.62/1.59  #Split   : 6
% 3.62/1.59  #Chain   : 0
% 3.62/1.59  #Close   : 0
% 3.62/1.59  
% 3.62/1.59  Ordering : KBO
% 3.62/1.59  
% 3.62/1.59  Simplification rules
% 3.62/1.59  ----------------------
% 3.62/1.59  #Subsume      : 12
% 3.62/1.59  #Demod        : 90
% 3.62/1.59  #Tautology    : 31
% 3.62/1.59  #SimpNegUnit  : 4
% 3.62/1.59  #BackRed      : 6
% 3.62/1.59  
% 3.62/1.59  #Partial instantiations: 0
% 3.62/1.59  #Strategies tried      : 1
% 3.62/1.59  
% 3.62/1.59  Timing (in seconds)
% 3.62/1.59  ----------------------
% 3.62/1.59  Preprocessing        : 0.36
% 3.62/1.59  Parsing              : 0.18
% 3.62/1.59  CNF conversion       : 0.04
% 3.62/1.59  Main loop            : 0.46
% 3.62/1.59  Inferencing          : 0.18
% 3.62/1.59  Reduction            : 0.13
% 3.62/1.59  Demodulation         : 0.09
% 3.62/1.59  BG Simplification    : 0.03
% 3.62/1.59  Subsumption          : 0.08
% 3.62/1.59  Abstraction          : 0.02
% 3.62/1.59  MUC search           : 0.00
% 3.62/1.59  Cooper               : 0.00
% 3.62/1.59  Total                : 0.88
% 3.62/1.59  Index Insertion      : 0.00
% 3.62/1.59  Index Deletion       : 0.00
% 3.62/1.59  Index Matching       : 0.00
% 3.62/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
